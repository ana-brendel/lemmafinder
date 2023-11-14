(* This file holds functions that help deal with the Coq API in our context *)
(* All low level operations (not dependent on any other files) *)

let string_of_econstr (env : Environ.env) (sigma : Evd.evar_map) (expr : Evd.econstr) : string =
  (Pp.string_of_ppcmds (Printer.pr_goal_concl_style_env env sigma expr))
  
let string_of_constr (env : Environ.env) (sigma : Evd.evar_map) (expr : Constr.t) : string =
  (Pp.string_of_ppcmds (Printer.safe_pr_constr_env env sigma expr))

(* Not super clear on how this function is working, copied from Utils.ml *)
let get_type_of_econstr env sigma econstr = 
  try Some (Retyping.get_type_of ~lax:false ~polyprop:false env sigma econstr)
  with _ -> None

let process_hyps (hyp_context : EConstr.named_context) : (string,(Names.variable * EConstr.t)) Hashtbl.t =
  let iter hyp =
    match hyp with
    | Context.Named.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), y)
    | Context.Named.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), y)
  in let processed = List.map iter hyp_context in
  let result = Hashtbl.create (List.length processed) in
  List.iter (fun (var,econstr) -> Hashtbl.add result (Names.Id.to_string var) (var,econstr)) processed; result

let rec terms_in_econstr (env : Environ.env) (sigma : Evd.evar_map) (type_terms : (EConstr.t * EConstr.t) list) 
(econstr : Evd.econstr) : (EConstr.t * EConstr.t) list = 
  let eq_here (x : (EConstr.t * EConstr.t)) (y : (EConstr.t * EConstr.t)) : bool =
    let (term_x,_) = x in let (term_y,_) = y in 
    String.equal (string_of_econstr env sigma term_x) (string_of_econstr env sigma term_y)
  in
  match Constr.kind (EConstr.to_constr sigma econstr) with
  | App (func, args) -> (* App is a sub-term that we would want to include, then iterate arguments *)
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms | Some x -> (econstr, x) :: type_terms in 
      (* let args_list =  List.map EConstr.of_constr (func :: Array.to_list args) in  --> collect functions differently *)
      let args_list =  List.map EConstr.of_constr (Array.to_list args) in 
      Utils.remove_duplicates eq_here (List.fold_left (terms_in_econstr env sigma) tmp args_list)
    )
  | Prod (_,hypo,result) -> (* Prod is the implication type, not including variable bindings below *)
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms | Some x -> (econstr, x) :: type_terms in 
      let args_list =  List.map EConstr.of_constr [hypo;result] in 
      Utils.remove_duplicates eq_here (List.fold_left (terms_in_econstr env sigma) tmp args_list)
    )
  | Lambda (ids,inp,body) -> 
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms | Some x -> (econstr, x) :: type_terms in 
      let args_list =  List.map EConstr.of_constr [inp;body] in 
      Utils.remove_duplicates eq_here (List.fold_left (terms_in_econstr env sigma) tmp args_list)
    )
  | LetIn (ids,inp,assignment,expr) ->
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms | Some x -> (econstr, x) :: type_terms in 
      let args_list =  List.map EConstr.of_constr [inp;assignment;expr] in 
      Utils.remove_duplicates eq_here (List.fold_left (terms_in_econstr env sigma) tmp args_list)
    )
  | Case (info,a,b,arr) -> 
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms | Some x -> (econstr, x) :: type_terms in 
      let args_list =  List.map EConstr.of_constr ([a;b] @ (Array.to_list arr)) in 
      Utils.remove_duplicates eq_here (List.fold_left (terms_in_econstr env sigma) tmp args_list)
    )
  | _ -> (* This just adds any types from the econster, might want to finetune later on (could require more iteration) 
      --> For example, maybe iterate over Lambda or LetIn kinds to get all types (haven't encountered yet)*)
    try 
      let econstr_type = get_type_of_econstr env sigma econstr in
      match econstr_type with | None -> Utils.remove_duplicates eq_here type_terms 
      | Some x ->  Utils.remove_duplicates eq_here ((econstr, x) :: type_terms)
    with _ -> type_terms

let rec types_in_econstr (env : Environ.env) (sigma : Evd.evar_map) (type_terms : EConstr.t list) 
(econstr : Evd.econstr) : EConstr.t list = 
  let eq_here (x : EConstr.t) (y : EConstr.t) : bool = 
    String.equal (string_of_econstr env sigma x) (string_of_econstr env sigma y)
  in
  match Constr.kind (EConstr.to_constr sigma econstr) with
  | App (func, args) -> (* App is a sub-term that we would want to include, then iterate arguments *)
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms |Some typ -> typ :: type_terms in
      let args_list =  List.map EConstr.of_constr (Array.to_list args) in 
      Utils.remove_duplicates eq_here (List.fold_left (types_in_econstr env sigma) tmp args_list)
    )
  | Prod (_,hypo,result) -> (* Prod is the implication type, not including variable bindings below *)
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms |Some typ -> typ :: type_terms in
      let args_list =  List.map EConstr.of_constr [hypo;result] in 
      Utils.remove_duplicates eq_here (List.fold_left (types_in_econstr env sigma) tmp args_list)
    )
  | Lambda (_,inp,body) -> 
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms |Some typ -> typ :: type_terms in
      let args_list =  List.map EConstr.of_constr [inp;body] in 
      Utils.remove_duplicates eq_here (List.fold_left (types_in_econstr env sigma) tmp args_list)
    )
  | LetIn (_,inp,assignment,expr) ->
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms |Some typ -> typ :: type_terms in
      let args_list =  List.map EConstr.of_constr [inp;assignment;expr] in 
      Utils.remove_duplicates eq_here (List.fold_left (types_in_econstr env sigma) tmp args_list)
    )
  | Case (_,a,b,arr) -> 
    (
      let econstr_type = get_type_of_econstr env sigma econstr in 
      let tmp = match econstr_type with | None -> type_terms |Some typ -> typ :: type_terms in
      let args_list =  List.map EConstr.of_constr ([a;b] @ (Array.to_list arr)) in 
      Utils.remove_duplicates eq_here (List.fold_left (types_in_econstr env sigma) tmp args_list)
    )
  | _ -> (* This just adds any types from the econster, might want to finetune later on (could require more iteration) 
      --> For example, maybe iterate over Lambda or LetIn kinds to get all types (haven't encountered yet)*)
    try 
      let econstr_type = get_type_of_econstr env sigma econstr in
      match econstr_type with | None -> Utils.remove_duplicates eq_here type_terms
      | Some typ -> Utils.remove_duplicates eq_here (typ :: type_terms)
    with _ -> type_terms

let rec func_in_econstr (env : Environ.env) (sigma : Evd.evar_map) (func_type_terms : (EConstr.t * EConstr.t * EConstr.t list) list) 
(econstr : EConstr.t) : (EConstr.t * EConstr.t * EConstr.t list) list= 
  let is_a_type x = match (get_type_of_econstr env sigma x) with | None -> false
   | Some typ ->  String.equal (string_of_econstr env sigma typ) "Type" in
  match Constr.kind (EConstr.to_constr sigma econstr) with
  | App (func, args) ->
    ( 
      let efunc = EConstr.of_constr func in
      let func_constr_type = get_type_of_econstr env sigma efunc in 
      let args_list =  List.map EConstr.of_constr (Array.to_list args) in
      let type_params = List.filter is_a_type args_list in
      let tmp = match func_constr_type with | None -> func_type_terms 
      | Some ftyp -> (efunc, ftyp, type_params) :: func_type_terms in 
      List.fold_left (func_in_econstr env sigma) tmp args_list
    )
  | Prod (_,hypo,result) -> 
    List.fold_left (func_in_econstr env sigma) func_type_terms (List.map EConstr.of_constr [hypo;result])
  | Lambda (_,inp,body) -> 
    List.fold_left (func_in_econstr env sigma) func_type_terms (List.map EConstr.of_constr [inp;body])
  | LetIn (_,inp,assignment,expr) ->
    List.fold_left (func_in_econstr env sigma) func_type_terms (List.map EConstr.of_constr [inp;assignment;expr])
  | Case (info,a,b,arr) -> 
    List.fold_left (func_in_econstr env sigma) func_type_terms (List.map EConstr.of_constr ([a;b] @ (Array.to_list arr)))
  (* We might want to explore the functions from terms other than application (if there are other 
      iteratively defined (such as LetIn or Lambda)) *)
  | _ -> func_type_terms

let rec vars_from_constr (env : Environ.env) (sigma : Evd.evar_map) 
(context_vars : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t)
(vars : Names.variable list) (constr : Constr.t) : Names.variable list =
  let recursive_call = vars_from_constr env sigma context_vars in
  let is_variable x = Hashtbl.find_opt context_vars (string_of_constr env sigma x) in
  let result = match Constr.kind constr with
  | Var id -> id :: vars
  | App (func, args) -> (let values = List.fold_left recursive_call vars (Array.to_list args) in
    match (is_variable func) with | None -> values | Some (_,id,_) -> id :: values)
  | Prod (_,hypo,result) -> List.fold_left recursive_call vars (hypo :: [result])
  | Lambda (ids,inp,body) -> List.fold_left recursive_call vars (inp :: [body])
  | LetIn (ids,inp,assignment,expr) -> List.fold_left recursive_call vars (inp :: [assignment;expr])
  | _ -> (*print_endline ("Variables parsing undefined passed here: " ^ string_of_constr env sigma constr);*) vars
  in Utils.remove_duplicates (fun x y -> String.equal (Names.Id.to_string x) (Names.Id.to_string y)) result

let conjoin_props (sigma : Evd.evar_map) (props : EConstr.t list) : Constr.t option =
  let and_mutind = 
    Names.MutInd.make2 
    (Names.MPfile (Names.DirPath.make (List.map Names.Id.of_string ["Logic";"Init";"Coq"])))
    (Names.Label.make "and") in
  let and_constr = Constr.mkInd (and_mutind,0) in
  let rec aux = function
  | [] -> None
  | last :: [] -> Some (EConstr.to_constr sigma last)
  | curr :: remaining -> 
    match aux remaining with
    | None -> Some (EConstr.to_constr sigma curr)
    | Some clause -> Some (Constr.mkApp (and_constr,Array.of_list [(EConstr.to_constr sigma curr); clause]))
  in aux props

let make_equal (typ : Constr.t) (left : Constr.t) (right : Constr.t) : Constr.t =
  let eq_mutind = 
    Names.MutInd.make2 
    (Names.MPfile (Names.DirPath.make (List.map Names.Id.of_string ["Logic";"Init";"Coq"])))
    (Names.Label.make "eq") in
  let eq_constr = Constr.mkInd (eq_mutind,0) in
  Constr.mkApp (eq_constr,Array.of_list [typ;left;right])

let make_equal_to_str (typ : Constr.t) (left : Constr.t) (right : string) : Constr.t =
  let right_constr = Constr.mkVar (Names.Id.of_string_soft right) in make_equal typ left right_constr

let non_types_helper (types : (string, Evd.econstr * bool) Hashtbl.t) (vars : string list)
(tbl : (string, (EConstr.t * Names.variable * EConstr.t)) Hashtbl.t) : Names.variable list = 
  let strs =  List.filter (fun v -> (Hashtbl.mem types v) = false) vars in
  let get_var x =
    try let (_,v,_) = Hashtbl.find tbl x in v
    with _ -> raise (Failure "Error in variables table for context (triggered in LFUtils.ml)") in
    List.map get_var strs

let create_implication (antecedent : Constr.t) (result : Constr.t)=
  let empty_binding = Context.anonR in Constr.mkProd (empty_binding, antecedent, result)

let join_props_with_impl (sigma : Evd.evar_map) (props : EConstr.t list) : Constr.t option =
  let rec aux = function
  | [] -> None
  | last :: [] -> Some (EConstr.to_constr sigma last)
  | curr :: remaining -> 
    match aux remaining with
    | None -> Some (EConstr.to_constr sigma curr)
    | Some clause -> Some (create_implication (EConstr.to_constr sigma curr) clause)
  in aux props