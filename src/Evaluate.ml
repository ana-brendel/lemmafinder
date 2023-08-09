let generate_eval_file (context : LFContext.t) (eval_str : string) : string =
  let lfind_file = context.lfind_dir ^ "/lfind_eval.v"
  in let content = Consts.fmt "%s%s\nFrom %s Require Import %s.\n%s\n%s\n%s\n%s\n%s\n%s"
    Consts.lfind_declare_module
    context.declarations
    context.namespace 
    context.filename
    ""
    Consts.coq_printing_depth
    "Unset Printing Notations." 
    "Set Printing Implicit."
    (LFUtils.set_nat_as_unknown_type context)
    eval_str in Utils.write_to_file lfind_file content; lfind_file

let run_eval (dir : string) (fname : string) (namespace : string) : string list =
  (* let cmd = "coqc -R " ^ dir ^ " " ^ namespace  ^ " " ^ fname *)
  let cmd = "cd " ^ dir ^ " && coqc -R . " ^ namespace  ^ " " ^ fname
  in try Utils.run_cmd cmd with _ -> [] 

let get_evaluate_str (expr : string) (vars : string) (vars_list : string list) (example : (string, string) Hashtbl.t) : string =
  let def = "Definition lfind_eval " ^ vars ^ " :=\n" ^ expr ^ ".\n" in
  let example_input = 
    List.map
    (fun v -> try (Consts.fmt "(%s)" (Hashtbl.find example v)) with _ -> "")
    vars_list in
  let compute_string = "\nCompute lfind_eval " ^ (String.concat " " example_input) ^ ".\n" in
  def ^ compute_string

let parse_output (output : string list) : string option= 
  let flattened = String.concat " " (List.map String.trim output) in
  let split_on_equal = String.split_on_char '=' flattened in
  if (List.length split_on_equal != 2)
  then raise (Failure ("1. Error in parsing output for example propgation (triggered in Evaluate.ml) -- On line: " ^ flattened))
  else 
    (
      let content = List.hd (List.rev split_on_equal) in
      let split_from_type = String.split_on_char ':' content in
      if (List.length split_from_type != 2)
      then raise (Failure ("2. Error in parsing output for example propgation (triggered in Evaluate.ml) -- On line: " ^ flattened))
      else Some (String.trim (List.hd split_from_type))
    )

let econstr_term (context : LFContext.t) (example : (string, string) Hashtbl.t) (expr : EConstr.t) : string option = 
  let expr_string = LFContext.e_str context expr in
  let variables_in_expr = LFCoq.vars_from_constr context.env context.sigma [] (EConstr.to_constr context.sigma expr) in
  let variables_in_expr_str = List.map Names.Id.to_string variables_in_expr in
  let non_types = List.filter (fun v -> (Hashtbl.mem context.types v) = false) variables_in_expr_str in
  let args_str = String.concat " " (List.map
    (fun v -> 
      let (typ,_,_)  = try Hashtbl.find context.variables v 
      with _ -> raise (Failure (Consts.fmt "1. Cannot find variable [%s] info (triggered in Evaluate.ml)" v))
      in "(" ^ v ^ " : " ^ (LFContext.e_str context typ) ^ ")")
    non_types) in
  let evaluation_string = get_evaluate_str expr_string args_str variables_in_expr_str example in
  let eval_file = generate_eval_file context evaluation_string in
  let output = run_eval context.lfind_dir eval_file context.namespace in
  parse_output output

let econstr_term_with_vars (context : LFContext.t) (variables : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t) 
(example : (string, string) Hashtbl.t) (expr : EConstr.t) : string option = 
  let expr_string = LFContext.e_str context expr in
  let variables_in_expr = LFCoq.vars_from_constr context.env context.sigma [] (EConstr.to_constr context.sigma expr) in
  let variables_in_expr_str = List.map Names.Id.to_string variables_in_expr in
  let non_types = List.filter (fun v -> (Hashtbl.mem context.types v) = false) variables_in_expr_str in
  let args_str = String.concat " " (List.map
    (fun v -> 
      let (typ,_,_)  = try Hashtbl.find variables v 
      with _ -> try Hashtbl.find context.variables v 
      with _ -> raise (Failure (Consts.fmt "2. Cannot find variable [%s] info (triggered in Evaluate.ml)" v))
      in "(" ^ v ^ " : " ^ (LFContext.e_str context typ) ^ ")")
    non_types) in
  let evaluation_string = get_evaluate_str expr_string args_str variables_in_expr_str example in
  let eval_file = generate_eval_file context evaluation_string in
  let output = run_eval context.lfind_dir eval_file context.namespace in
  parse_output output

let evaluate_string (context : LFContext.t) (str : string) : bool =
  let eval_string = "Lemma eval_example : " ^ str ^ "." in
  let eval_file = LFUtils.create_quickchick_file context "eval_example" eval_string 1 in
  let output = run_eval context.lfind_dir eval_file context.namespace in
  List.fold_left (fun acc l -> acc || (Utils.contains l "+++ Passed 1 tests") ) false output