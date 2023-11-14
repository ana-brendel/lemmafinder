let parse_example (example : string) : (string, string) Hashtbl.t = 
  let split_by_variable = String.split_on_char '`' example in
  let example_table = Hashtbl.create (List.length split_by_variable) in
  List.iter 
  (fun ex -> 
    let values = String.split_on_char ':' ex in
    try 
    let var_name, value = (List.hd values), (List.hd (List.tl values))
    in Hashtbl.add example_table var_name value with _ -> ()
  ) split_by_variable; example_table

let gather_examples (example_file : string) : ((string, string) Hashtbl.t) list =
  let file_contents = Utils.read_file example_file in 
  List.map parse_example (Utils.remove_duplicates (String.equal) file_contents) (* Note: consider printing examples differently to avoid bugs *)

let replace_var_with_value (context : LFContext.t) (var : string) (value : string) (expr : EConstr.t) : EConstr.t =
  let env = context.env in let sigma = context.sigma in
  let rec iterate current =
    let current_string = LFContext.e_str context (EConstr.of_constr current) in (* uses econstr to value without ()*)
    if (String.equal var current_string) then (Constr.mkVar (Names.Id.of_string_soft ("(" ^ value ^ ")"))) 
    else match Constr.kind current with
    | App (func, args) -> (* Check if the application is the term, if not iterate *)
      (
        let updated_args_list = List.map iterate (Array.to_list args) in 
        let updated_array = Array.of_list updated_args_list in
        Constr.mkApp (func, updated_array)
      )
    | Prod (id,hypo,result) ->
      (
        let updated_hypo = iterate hypo in
        let updated_result = iterate result in
        Constr.mkProd (id, updated_hypo, updated_result)
      )
    | Lambda (ids,inp,body) -> 
      (
        let updated_inp = iterate inp in
        let updated_body = iterate body in
        Constr.mkLambda (ids, updated_inp, updated_body)
      )
    | LetIn (ids,inp,assignment,expr) ->
      (
        let updated_assignment = iterate assignment in
        let updated_expr = iterate expr in
        let updated_inp = iterate inp in
        Constr.mkLetIn (ids, updated_inp, updated_assignment, updated_expr)
      )
    | Case (info,a,b,arr) -> 
      (
        let updated_arr = Array.of_list (List.map iterate (Array.to_list arr)) in
        let updated_a = iterate a in
        let updated_b = iterate b in
        Constr.mkCase (info, updated_a, updated_b, updated_arr)
      )
    | _ -> current
  in EConstr.of_constr (iterate (EConstr.to_constr context.sigma expr))

let evaluate_example (context : LFContext.t) (generalized : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t) 
 (example : (string, string) Hashtbl.t) : unit = 
  Hashtbl.iter
  (
    fun var (_,_,term) -> let e_opt = Evaluate.econstr_term context example term in 
    match e_opt with
    | Some e -> Hashtbl.add example var e
    | None -> raise (Failure (Consts.fmt "Potential Error, example not generated for [%s] (triggered in ExampleManagement.ml)" var))
  ) generalized; ()

let get_examples_for_generalizations (context : LFContext.t) 
(generalized_variables : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t) 
(coq_examples : (string, string) Hashtbl.t list) : (string, string) Hashtbl.t list =
  List.iter (evaluate_example context generalized_variables) coq_examples; coq_examples