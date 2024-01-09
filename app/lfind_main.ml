open Lfindalgo

exception Invalid_Examples of string

let clean (context : LFContext.t) : unit =
  match !Consts.clean_up with
  | false -> ()
  | true -> let dir = context.lfind_dir in
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/conj*") in 
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/lfind_conj*") in 
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/.lfind_conj*") in
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/lfind_generalized_*") in 
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/.lfind_generalized_**") in
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/lfind_eval*") in 
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/.lfind_eval*") in
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/lfind_proverbot_eval_*") in 
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/.lfind_proverbot_eval_*") in
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/lfind_quickchick*") in 
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/.lfind_quickchick*") in
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/search-report*") in 
  let _ = Utils.run_cmd ("rm -rf " ^ dir ^ "/lfind_axiom_*") in  ()

let print_results (context : LFContext.t) (lemmas : Conjecture.t list) : string =
  let rec get_first_n n acc = function
  | [] -> acc
  | h :: t -> if n > 0 then (get_first_n (n-1) (acc @ [h]) t) else acc in
  if List.length lemmas = 0 then "LFind generated no helper lemmas. \n"
  else 
    let num = if List.length lemmas > 5 then 5 else List.length lemmas in
    let top = List.map (Conjecture.get_pretty_print context) (get_first_n num [] lemmas) in
    "Top "^ string_of_int num ^" Lemmas from LFind:\n" ^ (String.concat "\n" top) ^ "\n"

let lfind_tac (debug: bool) (clean_flag: bool) : unit Proofview.tactic =
  Consts.start_time := int_of_float(Unix.time ());
  Consts.clean_up := clean_flag;
  Consts.debug := debug; 
  let quickchick_passed = ref false in

  Proofview.Goal.enter
  begin fun gl ->
    let is_running = Utils.get_env_var "is_lfind" in 
    if String.equal is_running "true" then Tacticals.New.tclZEROMSG (Pp.str ("LFind is already running! Aborting"))
    else
      begin
        Utils.env_setup ();
        let context = LFContext.get gl in
        LogProgress.context context;

        if (List.length (LFContext.non_type_variables context ) = 0) 
        then (
          print_endline "No variables in goal state, stopping LFind execution.";
          LogProgress.no_variables_abort_message context; exit(0);
        ) else();
        
        let commands_file = Consts.fmt "%s/lfind_command_log.txt" context.lfind_dir in
        Consts.decidable := Sys.file_exists (Consts.fmt "%s/decide.v" context.lfind_dir);
        (* Makes sure the instances of decidability, show and arbitrary are compiled *)
        let _ = if (!Consts.decidable) then 
          (Utils.run_cmd (Consts.fmt "cd %s/ && coqc -R . %s %s" context.lfind_dir context.namespace "decide.v")) else [] in

        let example_file = Consts.fmt "%s/examples_%s.txt" context.lfind_dir context.filename in
        if (not (Sys.file_exists example_file) & !Consts.decidable) then 
        (
          print_endline "Example file not found and decidable, so generating examples for synthesis";
          let op = ExampleGeneration.run context in 
          (* 1st check that Quickchick was able to run without error *)
          let ran_successfully = List.fold_left (fun acc l -> acc || (Utils.contains l "lemmafinder_success") ) false op
          (* Then we want to check if Quickchick actually succeeded or if counterexamples were found *)
          (* Quickchick failure message that is printed: *** Failed after _ tests and _ shrinks. *)
          in let quickchick_success = List.fold_left (fun acc l -> acc || (Utils.contains l "+++ Passed 50 tests") ) false op
          in quickchick_passed := quickchick_success;
          if not ran_successfully then raise (Invalid_Examples "Quickchick failed to run successfully") else 
          (* if not quickchick_success then raise (Invalid_Examples "Current proof state incorrect (without hypotheses or in general)") else  *)
          Feedback.msg_info (Pp.str "lemmafinder_example_generation_success")
        ); let _ = Utils.run_cmd "export is_lfind=true" in 

        (* Gather the examples for the proof context *)
        let examples = if (Sys.file_exists example_file) then ExampleManagement.gather_examples example_file else [] in

        (* Determine the generalizations *)
        let generalized_variables, generalizations = Generalization.get_generalizations context in 
        LogProgress.generalization context generalized_variables generalizations; clean context;
        Utils.write_to_file commands_file !Consts.commands;

        (* Push the examples through the generalized terms as well -- state is mutated here, adding generalized examples to tables*)
        let _ = ExampleManagement.get_examples_for_generalizations context generalized_variables examples in (* string error occurs here *)

        (* Determine which generalizations are valid on their own *)
        let valid, invalid = if (!Consts.decidable) then Validity.check_generalizations context generalizations else [],generalizations in
        LogProgress.vaidity_check context valid invalid; clean context;
        Utils.write_to_file commands_file !Consts.commands;

        (* Add implications to lemmas that were invalid *)
        let updated_invalid = if (!Consts.decidable) then Validity.add_implications context invalid else invalid in  
        LogProgress.implications context updated_invalid; clean context;
        Utils.write_to_file commands_file !Consts.commands;

        (* Again, determine if the implications are invalid or not *)
        let valid_implications, invalid_still = if (!Consts.decidable) then Validity.check_generalizations context updated_invalid else [], updated_invalid in
        LogProgress.vaidity_check context valid_implications invalid_still; clean context;

        (* Create the different synthesis problems *)
        (* NOTE: change the "invalid_still" to include valid generalizations, if below threshold *)
        let sketches = Sketch.generate context invalid_still in
        LogProgress.sketches context sketches; clean context;
        Utils.write_to_file commands_file !Consts.commands;

        (* Create the distinct synthesis problems *)
        let synthesis_problems, problem_by_sketch = Synthesis.create_problems context sketches generalized_variables examples in
        LogProgress.synthesis context problem_by_sketch; clean context;
        Utils.write_to_file commands_file !Consts.commands;

        (* Run each synthesis problem *)
        let synthesizer = BlackBox.get_synthesizer context in
        let ran_synthesis_problems = BlackBox.run_synthesis context synthesizer synthesis_problems in
        LogProgress.ran_synthesis context ran_synthesis_problems; clean context;
        Utils.write_to_file commands_file !Consts.commands;

        (* Generate a list of all of the possible conjectures *)
        let candidate_lemmas_from_generalization = Conjecture.from_generalizations context (valid @ valid_implications) in
        let offset = (List.length candidate_lemmas_from_generalization) + 1 in
        let candidate_lemmas_from_synthesis = Conjecture.from_synthesis offset context ran_synthesis_problems sketches problem_by_sketch in
        let candidate_lemmas = candidate_lemmas_from_generalization @ candidate_lemmas_from_synthesis in
        LogProgress.candidate_lemmas context candidate_lemmas; clean context;
        Utils.write_to_file commands_file !Consts.commands;

        (* Filter out any redundant or invalid *)
        let filtered_candidate_lemmas, (duplicates, quickchick_filtered) = Filter.filtering context candidate_lemmas in 
        LogProgress.filtering context filtered_candidate_lemmas (List.length candidate_lemmas) duplicates quickchick_filtered;
        clean context;

        (* Rank *)
        let start_ranking = int_of_float(Unix.time ()) in
        let (category_one,category_two,category_three) = Ranking.rank context filtered_candidate_lemmas in 
        let are_provable = List.filter (fun (x : Conjecture.t) -> x.provable) category_three in
        let not_provable = List.filter (fun (x : Conjecture.t) -> x.provable = false) category_three in
        (* Error with ranking so not looking at the right now *)
        (* let (category_one,category_two,are_provable,not_provable) = ([],[],[],filtered_candidate_lemmas) in *)
        clean context;

        (* If we not run QuickChick, so !Consts.decidable is false, 
           we don't want to include it if not provable (to not risk adding invalid suggetsions) *)
        let category_two = if (!Consts.decidable) then category_two else [] in
        let not_provable = if (!Consts.decidable) then not_provable else [] in

        (* Summarize results for user *)
        let completed_at = int_of_float(Unix.time ()) in
        let summary_file = Consts.fmt "%s/lfind_summary_log.txt" context.lfind_dir in
        let algorithm_log = Consts.fmt "%s/lfind_progress_log.txt" context.lfind_dir in
        Utils.write_to_file algorithm_log !Consts.progress; clean context;
        Utils.write_to_file commands_file !Consts.commands;
        let results =
          String.concat "\n"
          [
            "LFind Results"; 
            (Consts.fmt "LFind Directory: %s" context.lfind_dir);
            (if (!Consts.decidable) then "" else "\nDecidability proof NOT provided, so results are limited");
            (Consts.fmt "\nNumber of Lemmas: %d" (List.length candidate_lemmas));
            (Consts.fmt "Number of Lemmas (after duplicates removed): %d" duplicates);
            (Consts.fmt "Number of Lemmas (after QuickChick used to filter): %d" quickchick_filtered);
            ("* Number of Candidate Lemmas: " ^ (string_of_int (List.length filtered_candidate_lemmas)));
            ("\nTime until ranking: " ^ (string_of_int (start_ranking - !Consts.start_time)));
            ("Time to complete: " ^ (string_of_int (completed_at - !Consts.start_time)) ^ "\n");
            ("Stuck state true independent of hypotheses: " ^ (string_of_bool !quickchick_passed));
            "\nCategory 1:";Consts.fmt "Count = %d" (List.length category_one); 
            List.fold_left (fun acc x -> acc ^ "\n" ^ (Conjecture.get_pretty_print context x)) "" category_one;
            "\nCategory 2:";Consts.fmt "Count = %d" (List.length category_two); 
            List.fold_left (fun acc x -> acc ^ "\n" ^ (Conjecture.get_pretty_print context x)) "" category_two;
            "\nCategory 3 (provable):";Consts.fmt "Count = %d" (List.length are_provable); 
            List.fold_left (fun acc x -> acc ^ "\n" ^ (Conjecture.get_pretty_print context x)) "" are_provable;
            (* "\n\nAll lemmas here because ranking is turned off right now..."; *)
            "\nCategory 3 (not provable):";Consts.fmt "Count = %d" (List.length not_provable); 
            List.fold_left (fun acc x -> acc ^ "\n" ^ (Conjecture.get_pretty_print context x)) "" not_provable;
          ] 
        in Utils.write_to_file summary_file results;
        let top_lemmas = print_results context (category_one @ category_two @ are_provable @ not_provable) in
        let decide_provided = if (!Consts.decidable) then "" else "Decidability proof not provided, so results limited.\n" in
        let msg = "LFIND Successful.\n" ^ decide_provided ^ top_lemmas ^  "\nResults of LFIND at: " ^ summary_file ^ 
        "\nAlgorithm Progress of LFIND at: " ^ algorithm_log ^ "\nCommands ran listed at: " ^ commands_file in
        Tacticals.New.tclZEROMSG (Pp.str msg)
      end
  end
