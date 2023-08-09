exception Mismatch_Filtered of string

let remove_duplicate_conj (context : LFContext.t) (conj : Conjecture.t list)  : Conjecture.t list =
  let conj_eq (a : Conjecture.t) (b : Conjecture.t) = 
    String.equal (LFContext.e_str context a.lemma) (LFContext.e_str context b.lemma) in
  Utils.remove_duplicates conj_eq conj

let create_quickchick_eval_for_conj (context : LFContext.t) (conj : Conjecture.t) : string =
  let eval_file = context.lfind_dir ^ (Consts.fmt "/lfind_eval_%s.v" conj.label) in
  let file_intro = ExampleGeneration.coq_quickchick_prereqs context 50 true in
  let content = String.concat "\n" 
  [file_intro; (Conjecture.get_pretty_print context conj); "Admitted."; (Consts.fmt "QuickChick %s." conj.label)] in
  Utils.write_to_file eval_file content;
  eval_file

let check_conjecture_with_quickchick (context : LFContext.t) (conj : Conjecture.t)  : bool * string list =
  let file = create_quickchick_eval_for_conj context conj in
  let cmd = Consts.fmt "cd %s/ && coqc -R . %s %s" context.lfind_dir context.namespace file in
  let output = Utils.run_cmd cmd in 
  let valid = List.fold_left (fun acc l -> acc || (Utils.contains l "Passed") ) false output in
  let counterexample = List.fold_left (fun acc l -> acc || (Utils.contains l "Failed") ) false output in
  if valid 
  then true, []
  else 
    if counterexample then false, (Validity.gather_counterexamples output)
    else 
      (
        print_endline ("Quickchick failed to run when compiling: "^file^" \nOutput:\n" ^(String.concat "\n" output));
        raise (Failure "Quickchick error triggered in Filter.ml")
      )

let run lemmas imports prelude theorem_name theorem = 
  let python = "python3 "
  in let script = Consts.fmt "%ssrc/filter.py" !Consts.lfind_path
  in let cmd = 
    Consts.fmt "%s %s --prelude=%s --theorem_name=%s --theorem=%s --lemmas %s --imports %s"
      python
      script
      prelude
      theorem_name
      theorem
      lemmas
      imports
  in print_endline cmd;
  Utils.run_cmd cmd

(* Using previous filtering script from python *)
let filter_lemmas (context : LFContext.t) (conjectures : Conjecture.t list) : Conjecture.t list =
  let imports = 
    Consts.fmt "\"%s\" %s \"From %s Require Import %s.\""
      Consts.lfind_declare_module
      (List.fold_left 
      (fun acc d -> if (String.length d > 0) then acc ^ Consts.fmt " \"%s\"" d else acc) 
      "" (String.split_on_char '\n' context.declarations))
      context.namespace
      context.filename in
  let lemmas = List.fold_left 
    (fun acc (c : Conjecture.t) -> acc ^ " \"" ^ (Conjecture.get_pretty_print context c) ^ "\"") "" conjectures in
  let prelude = Consts.fmt "\"%s\"" context.lfind_dir in
  let name = Consts.fmt "\"%s\"" context.proof_name in
  let theorem = Consts.fmt "\"%s\"" context.theorem in
  let output = run lemmas imports prelude name theorem in
  (* lemma name * lemma body *)
  let simplified_lemmas = List.fold_left (
      fun (acc) l ->
      if Utils.contains l ":trivial_count" then acc
      else
      (
        if Utils.contains l ":is_version_count" then acc
        else
        (
          if Utils.contains l "FilteredLemma$" 
          then
            let content = String.split_on_char '$' l
            in (List.nth content 1,List.nth content 2) :: acc
          else acc
        )
      )
    ) [] output in
  let filtered_names = List.map (fun (x,y) -> x) simplified_lemmas in
  let simplified_conjectures = 
    List.fold_left 
    (
      fun acc (r : Conjecture.t)->
        match List.mem r.label filtered_names with
        | true -> (r :: acc)
        | false -> acc
    ) [] conjectures
    in
  if (List.length simplified_lemmas) != (List.length simplified_conjectures)
  then raise @@ Mismatch_Filtered ("Filtered lemmas do not match the result")
  else simplified_conjectures

(* let create_trivial_lemma_eval_for_conj (context : LFContext.t) (conj : Conjecture.t) : string =
  let eval_file = context.lfind_dir ^ (Consts.fmt "/lfind_trivial_eval_%s.v" conj.label) in
  let file_intro = ExampleGeneration.coq_quickchick_prereqs context in
  let content = String.concat "\n" 
  [file_intro; (Conjecture.get_pretty_print context conj); "Proof."; "intros."; "trivial."; "Qed."] in
  Utils.write_to_file eval_file content;
  eval_file

let check_if_conjecture_is_trivial (context : LFContext.t) (conj : Conjecture.t)  : bool  =
  let run_trivial_cmd command = 
    try
      let exit_code = Sys.command command in exit_code = 0 (* This is the case that it is trivial*)
    with _ -> false in (* This is the case it is not trivial *)
  let file = create_trivial_lemma_eval_for_conj context conj in
  let cmd = Consts.fmt "cd %s/ && coqc -R . %s %s" context.lfind_dir context.namespace file in
  let trivial = run_trivial_cmd cmd in
  trivial = false (*Returns true if a non-trivial lemma*) *)

let filtering (context : LFContext.t) (lemmas : Conjecture.t list) : Conjecture.t list * (int * int ) =
  let to_str = LFContext.e_str context in let lemma_length (x : Conjecture.t)  = String.length (to_str x.lemma) in
  (* Sort by length *)
  let sorted = List.sort (fun a b-> (lemma_length b) - (lemma_length a)) lemmas in
  (* Remove any lemmas that are the goal state *)
  let remove_goal = List.filter (fun (x : Conjecture.t) -> String.equal (to_str x.lemma) (to_str context.goal) = false) sorted in
  (* Filtered by removing syntactically similar duplicates *)
  let filtered_by_syntactic_equivalence = remove_duplicate_conj context remove_goal in
  (* Filter invalid lemmas via QuickChick *)
  let filtered_by_quickchick = List.filter (fun x -> fst (check_conjecture_with_quickchick context x)) filtered_by_syntactic_equivalence in
  (* Filter out lemmas using script from original algorithm *)
  let filtered_by_script = filter_lemmas context (List.sort (fun a b-> (lemma_length b) - (lemma_length a)) filtered_by_quickchick) in 
  filtered_by_script, (List.length filtered_by_syntactic_equivalence, List.length filtered_by_quickchick)