let get_type_name (context : LFContext.t) (typ : EConstr.t) : string =
  let typ_str = LFContext.e_str context typ in
  try
    let (econstr,poly) = Hashtbl.find context.types typ_str in
    match poly with
    | false -> typ_str
    | _ -> 
      match Constr.kind (EConstr.to_constr context.sigma typ) with
      | App(f, args) -> LFContext.c_str context f
      | _ -> raise (Failure "Found polymorphic typ that is not polymorphic (causing error in LFUtils.ml)")
  with _ -> raise (Failure "Getting type name for a type that was not recorded (causing error in LFUtils.ml)")

let derive_type_properties_quickchick (context : LFContext.t) (typ : EConstr.t) : string= 
  let typ_constr = EConstr.to_constr Evd.empty typ in
  if Constr.isSort(typ_constr) || Constr.isVar(typ_constr) then ""
  else 
    if not (Constr.isApp(typ_constr)) && not (Constr.isInd(typ_constr)) && not (Constr.isConst(typ_constr))
      then (print_endline (LFContext.e_str context typ); "")
    else
      let typ_name = get_type_name context typ in
      let mod_typ_name = List.hd (String.split_on_char ' ' typ_name) in
      let file_name = Consts.fmt "%s/show_%s.v" context.lfind_dir mod_typ_name in
      if Sys.file_exists file_name then String.concat "\n" (Utils.read_file file_name |> List.rev)
      else (* This doesn't accurately define the needed information for polymorphic types *)
        Consts.fmt 
        ("Derive Show for %s.\n
        Derive Arbitrary for %s.\n
        Instance Dec_Eq_%s : Dec_Eq %s.\n
        Proof. dec_eq. Qed.\n") mod_typ_name mod_typ_name mod_typ_name (LFContext.e_str context typ)

let set_nat_as_unknown_type (context : LFContext.t) : string =
  let unknown_type_var = List.filter (Hashtbl.mem context.types) (List.map Names.Id.to_string (LFContext.get_variable_list context)) in
  let notations = List.map (Consts.fmt "Notation %s := nat.\n") unknown_type_var in
  String.concat "\n" notations        

let coq_file_intro (context : LFContext.t) : string =
  let import_file = Consts.fmt "%s\nFrom %s Require Import %s." (Consts.lfind_declare_module) (context.namespace) (context.filename) in
  let module_imports = context.declarations in
  let lfind__prereqs = String.concat "\n" [Consts.lfind_declare_module; module_imports; Consts.quickchick_import;  import_file]
  in lfind__prereqs ^ "\n"

let quickchick_imports (context : LFContext.t) : string =
  let quickchick_import = Consts.quickchick_import in
  let qc_include = Consts.fmt ("QCInclude \"%s/\".\nQCInclude \".\".") context.lfind_dir in
  (* NOTE : should look out for bugs here, when the type properties need to be automatically generated *)
  let typ_dev_list = List.map (derive_type_properties_quickchick context) (Hashtbl.fold (fun _ (y,_) accum -> y :: accum) context.types []) in
  let type_derivations = String.concat "\n\n" (Utils.remove_duplicates String.equal typ_dev_list) in
  let setting_unknown_types = set_nat_as_unknown_type context in
  let lfind_generator_prereqs =  String.concat "\n"
    [quickchick_import; qc_include; Consts.def_qc_num_examples; setting_unknown_types; type_derivations]
  in lfind_generator_prereqs ^ "\n"

let replace_subterm_econstr (context : LFContext.t) (goal : EConstr.t) (subterm : EConstr.t) (fill : EConstr.t) : EConstr.t =
  let env = context.env in let sigma = context.sigma in
  let subterm_str = LFContext.e_str context subterm in
  let fill_constr = EConstr.to_constr sigma fill in
  let rec iterate (current : Constr.t) = 
    let current_string = LFContext.e_str context (EConstr.of_constr current) in
    if (String.equal subterm_str current_string) then (fill_constr)
    else
    match Constr.kind current with
    | App (func, args) -> 
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
        let updated_args_list = List.map iterate (Array.to_list arr) in 
        let updated_arr = Array.of_list updated_args_list in
        let updated_a = iterate a in
        let updated_b = iterate b in
        Constr.mkCase(info,updated_a,updated_b,updated_arr)
      )
    | _ -> current
  in EConstr.of_constr (iterate (EConstr.to_constr sigma goal))

let create_quickchick_file (context : LFContext.t) (name : string) (define_lemma : string) : string =
  let lfind_file = context.lfind_dir ^ "/lfind_" ^ name ^ ".v" in
  let coq_intro = coq_file_intro context in
  let quickchick_intro = quickchick_imports context in
  let run_quickchick = "QuickChick " ^ name ^ "." in
  let content = String.concat "\n" [coq_intro; quickchick_intro; define_lemma; "Admitted."; run_quickchick ] in
  Utils.write_to_file lfind_file content;
  lfind_file

let filter_split (check : 'a -> bool) (lst : 'a list) : ('a list * 'a list) =
  let rec iter tlist flist = function
  | [] -> (tlist, flist)
  | h :: remaining ->
    match check h with
    | true -> iter (h :: tlist) flist remaining
    | false -> iter tlist (h :: flist) remaining
  in iter [] [] lst

let contains_string (context : LFContext.t) (expr : EConstr.t) (str : string) : bool =
  let expr_str = LFContext.e_str context expr in
  let rec iterate e s =
    if (s = String.length str) then true
    else (
      if (e = String.length expr_str) then false
      else (
        let e_char = String.get expr_str e in
        let s_char = String.get str s in
        match (Char.equal e_char s_char) with
        | true -> iterate (e+1) (s+1)
        | false -> iterate (e+1) s
        )
      ) in iterate 0 0
    