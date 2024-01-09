let write_to_log (context : LFContext.t) : unit =
  let algorithm_log = Consts.fmt "%s/lfind_progress_log.txt" context.lfind_dir in
  Utils.write_to_file algorithm_log !Consts.progress

let time_elapsed () : string = Consts.fmt "Time elapsed: %d seconds" ((int_of_float(Unix.time ())) - !Consts.start_time)

let context (context : LFContext.t) : unit = 
  Consts.progress := !Consts.progress ^ (LFContext.pp_context context); write_to_log context 

let no_variables_abort_message (context : LFContext.t) : unit = 
  Consts.progress := !Consts.progress ^ ("\n\nGoal state includes no variables. No need to run lfind."); write_to_log context 

let generalization context generalized_variables generalizations : unit =
  let e_str = LFContext.e_str context in
  Consts.progress := !Consts.progress ^ ("\n\n<---GENERALIZATION--->\n"^time_elapsed ()^"\nGeneralized Variables:");
  Hashtbl.iter (fun x (typ,_,term) -> Consts.progress := !Consts.progress ^ "\n" ^ (x ^ " : " ^ e_str typ ^ " = " ^ e_str term)) generalized_variables;
  Consts.progress := !Consts.progress ^ ("\n\nGeneralizations:");
  List.iter (fun g -> Consts.progress := !Consts.progress ^ "\n" ^ (Generalization.pp context g)) generalizations;
  write_to_log context 

let sketches context sketches : unit = 
  let e_str = LFContext.e_str context in
  Consts.progress := !Consts.progress ^ ("\n\n\n<---CREATE SKETCHES--->\n"^time_elapsed ()^"\nSketches:");
  List.iter (fun (s : Sketch.t) -> Consts.progress := !Consts.progress ^ "\nSketch " ^ s.label ^ " : " ^ (e_str s.goal_with_hole)) sketches;
  write_to_log context 

let vaidity_check context valid invalid : unit =
  Consts.progress := !Consts.progress ^ ("\n\n\n<---VALIDITY CHECKS--->\n"^time_elapsed ()^"\nValid:");
  List.iter (fun g -> Consts.progress := !Consts.progress ^ "\n" ^ (Generalization.pp context g)) valid;
  Consts.progress := !Consts.progress ^ ("\n\nInvalid:");
  List.iter (fun g -> Consts.progress := !Consts.progress ^ "\n" ^ (Generalization.pp context g)) invalid;
  write_to_log context 

let implications context updated_invalid : unit = 
  Consts.progress := !Consts.progress ^ ("\n\n<---ADD IMPLICATIONS--->\n"^time_elapsed ()^"\nGeneralizations:");
  List.iter (fun g -> Consts.progress := !Consts.progress ^ "\n" ^ (Generalization.pp context g)) updated_invalid;
  write_to_log context 

let synthesis context problem_by_sketch : unit = 
  Consts.progress := !Consts.progress ^ ("\n\n\n<---CREATE SYNTHESIS PROBLEMS--->\n"^time_elapsed ()^"\nProblems per Sketch:");
  Hashtbl.iter (fun s p -> Consts.progress := !Consts.progress ^ "\nSketch " ^ s ^ " --> Problem  " ^ p) problem_by_sketch;
  write_to_log context 

let ran_synthesis context ran_synthesis_problems : unit =
  Consts.progress := !Consts.progress ^ ("\n\n\n<--- SYNTHESIS PROBLEM RESULTS--->\n"^time_elapsed ());
  Hashtbl.iter 
  (fun x lst -> 
    Consts.progress := !Consts.progress ^ ("\n\nProblem: " ^ x); 
    List.iter (fun y -> Consts.progress := !Consts.progress ^ ("\n " ^ y)) lst;) 
  ran_synthesis_problems;
  write_to_log context 

let candidate_lemmas context candidates : unit = 
  Consts.progress := !Consts.progress ^ ("\n\n<---INITIAL CANDIDATE LEMMAS--->\n"^time_elapsed ()^"\nLemmas:");
  List.iter (fun l -> Consts.progress := !Consts.progress ^ "\n" ^ (Conjecture.get_pretty_print context l)) candidates;
  write_to_log context 

let filtering context candidates initial dups quickchick : unit = 
  Consts.progress := !Consts.progress ^ ("\n\n<---FILTERED CANDIDATE LEMMAS--->\n"^time_elapsed ());
  Consts.progress := !Consts.progress ^ ("\nDuplicates removed: " ^ string_of_int (initial - dups));
  Consts.progress := !Consts.progress ^ ("\nFiltered by Quickchick: "^ string_of_int (dups - quickchick));
  Consts.progress := !Consts.progress ^ ("\nFiltered by script: "^ string_of_int (quickchick - (List.length candidates)));
  Consts.progress := !Consts.progress ^ ("\nRemaining: "^ string_of_int (List.length candidates));
  Consts.progress := !Consts.progress ^ ("\n\nLemmas: ");
  List.iter (fun l -> Consts.progress := !Consts.progress ^ "\n" ^ (Conjecture.get_pretty_print context l)) candidates;
  write_to_log context 