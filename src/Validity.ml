let evaluate_example (hyp : EConstr.t) (context : LFContext.t) (generalization : Generalization.t) : string =
  try
    let hyp_replace = 
      Hashtbl.fold
      (fun var value expr -> ExampleManagement.replace_var_with_value context var value expr)
      (List.hd generalization.counterexamples) 
      hyp in
    let hyp_str_replace = LFContext.e_str context hyp_replace in
    (Consts.fmt "Definition generalized_hypothesis : %s." hyp_str_replace)
  with _ -> raise (Failure "Error evaluating hypotheses with counterexample triggered in Validity.ml")

(* assumes a counter example is returned --> copied from original lfind*)
let gather_counterexamples (output : string list) : string list = 
  let strings, _ = 
  List.fold_left 
  (fun (acc, is_acc) l -> 
    if  Utils.contains l ".native" 
    then acc, true 
    else
    (
      if Utils.contains l "Failed" 
      then acc, false
      else ( if is_acc then (List.append acc [l]), is_acc else acc, is_acc)
    )
  ) 
  ([],false) output 
  in strings

let cleanup (directory : string) (file : string) : unit =
  let filename = String.split_on_char '.' file |> List.hd in
  let _ = Utils.run_cmd ("rm -rf " ^ directory ^ "/" ^ filename ^"*") in ()

let check_generalization (context : LFContext.t) (generalization : Generalization.t) : bool * string list =
  let file = Generalization.quickchick context generalization in
  let cmd = Consts.fmt "cd %s/ && coqc -R . %s %s" context.lfind_dir context.namespace file in
  let output = Utils.run_cmd cmd in 
  let valid = List.fold_left (fun acc l -> acc || (Utils.contains l "Passed") ) false output in
  let counterexample = List.fold_left (fun acc l -> acc || (Utils.contains l "Failed") ) false output in
  if valid 
  then (cleanup context.lfind_dir file; true, [])
  else 
    if counterexample then (cleanup context.lfind_dir file; false, (gather_counterexamples output))
    else 
      (
        print_endline ("Quickchick failed to run when compiling: "^file^" \nOutput:\n" ^(String.concat "\n" output));
        raise (Failure "Quickchick error triggered in Validity.ml")
      )

let check_generalizations (context : LFContext.t) (generalizations : Generalization.t list) : Generalization.t list * Generalization.t list =
  (* Use Quickchick to 1) check of valid 2) if invalid, gather counterexamples *)
  let rec iterate valid invalid = function
  | [] -> valid, invalid
  | g :: rest -> 
    let is_valid, counterexamples = check_generalization context g in
    if is_valid 
      then (iterate ({g with valid = true} :: valid) invalid rest) (* We also typically run proverbot here to determine if provable or cat 1 *)
      else 
        (
          (* let variables = LFUtils.non_type_variables context in *)
          let variables = Generalization.non_type_variables context g in
          let var_strings = List.map Names.Id.to_string variables in
          if (List.length variables == List.length counterexamples)
          then 
            (
              let tbl = Hashtbl.create 1 in
              (* This relies on the order being parsed consistently (of the example values with respect to vars) *)
              let rec aux vars vals = 
                match (vars,vals) with
                | [], [] -> () 
                | v :: rest_var, e :: rest_vals -> 
                  Hashtbl.add tbl v e; aux rest_var rest_vals
                | _,_ -> raise (Failure "1. Error in gathering counterexamples (triggered in Validity.ml)")
              in aux var_strings counterexamples;
              iterate valid ({g with counterexamples = tbl :: g.counterexamples; valid = false} :: invalid) rest
            )
          else 
            (
              List.iter print_endline var_strings;
              List.iter print_endline counterexamples;
              raise (Failure "2. Error in gathering counterexamples (triggered in Validity.ml)")
            )
        )
  in iterate [] [] generalizations

let check_hypotheses (context : LFContext.t) (generalization : Generalization.t) (hypotheses : EConstr.t list) 
: (EConstr.t list) * (EConstr.t list) =
  let check_hypothesis (hypo : EConstr.t) : bool =
    if Hashtbl.mem context.types (LFContext.e_str context hypo)
    then false
    else
      if (LFUtils.contains_string context hypo "forall") then false
      else
      (
        let sub_expr = evaluate_example hypo context generalization in
        if String.equal "" sub_expr 
        then false
        else 
          (
            let file = LFUtils.create_quickchick_file context "generalized_hypothesis" sub_expr in
            let output = Evaluate.run_eval context.lfind_dir file context.namespace in
            List.fold_left (fun acc l -> acc || (Utils.contains l "Failed") ) false output
          )
      ) in 
  LFUtils.filter_split check_hypothesis hypotheses (* was just a List.filter*)

(* let add_implications (context : LFContext.t) (generalizations : Generalization.t list) : Generalization.t list =
  let per_generalization (generalization : Generalization.t) =
    let required_hypotheses = check_hypotheses context generalization in
    let conjunction_of_hyps = LFCoq.conjoin_props context.sigma required_hypotheses in
    match conjunction_of_hyps with
    | None -> [generalization]
    | Some antecedent -> let empty_binding = Context.anonR in
      let new_goal = Constr.mkProd (empty_binding, antecedent, (EConstr.to_constr context.sigma generalization.goal)) in
      [
        {generalization with 
          goal = (EConstr.of_constr new_goal); 
          label = generalization.label ^ "_imp"}; 
        generalization
      ]
  in List.flatten (List.map per_generalization generalizations) *)

let add_implications (context : LFContext.t) (generalizations : Generalization.t list) : Generalization.t list =
  let per_generalization (generalization : Generalization.t) =
    let updated = ref false in
    let hyps = (List.map (fun hyp -> match hyp with Context.Named.Declaration.LocalAssum(_,y) -> y) generalization.hypotheses) in
    let updated_label = generalization.label ^ "_imp" in
    let rec iterate (g : Generalization.t) (updated_hyps : EConstr.t list) = 
      let required_hypotheses, remaining_hyps = check_hypotheses context g updated_hyps in
      let implication_of_hyps = LFCoq.join_props_with_impl context.sigma required_hypotheses in
      match implication_of_hyps with
      | None -> g
      | Some antecedent -> updated := true;
        let impl = LFCoq.create_implication antecedent (EConstr.to_constr context.sigma g.goal) in
        let updated_gen = {g with goal = (EConstr.of_constr impl); label = updated_label} in
        let valid, invalid = check_generalizations context [updated_gen] in
        match invalid with
        | [] -> updated_gen
        | h :: t -> iterate h remaining_hyps in
      let result = iterate generalization hyps in
      if !updated then [generalization;result] else [result]
  in List.flatten (List.map per_generalization generalizations) 