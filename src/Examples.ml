let create_extraction_file (dir : string) (filename : string) : unit =
  let lfind_content = "
  module SS = Set.Make(String)
  let values = ref SS.empty
    
  let write_to_file value=
    let oc = open_out_gen [Open_append; Open_creat] 0o777 \"" ^ filename ^ "\" in
    if not(SS.mem value !values) then 
      (
        values := SS.add value !values;
        Printf.fprintf oc \"%s\\n\"  value;
      );
    close_out oc; ()
  
  let print n nstr=
    write_to_file (String.of_seq (List.to_seq nstr));
    (n)
    "
  in let extract_file_name = Consts.fmt ("%s/%s") dir "extract.ml"
  in Utils.write_to_file extract_file_name lfind_content

let get_lemma_statement_for_generation (context : LFContext.t) : string = 
  let implicit_types = ref "" in
  let var_str = 
    List.fold_left 
    (fun acc var -> 
      try
        let (typ,_,_) = Hashtbl.find context.variables var in
        if Hashtbl.mem context.types var 
        then (implicit_types := !implicit_types ^ (Consts.fmt "{%s}" var); acc)
        else (acc ^ " (" ^ var ^ " : " ^ (LFContext.e_str context typ) ^ ")")
      with _  -> print_endline "Type not found, potential error"; acc)
    ""
    (List.map Names.Id.to_string (LFContext.get_variable_list context)) in
  Consts.fmt "Lemma lfind_state %s %s : %s.\nAdmitted." !implicit_types var_str (LFContext.e_str context context.goal)

let break_off_last (vars : (string * string) list) :  (string * string list) =
  match List.rev vars with
  | [] -> "",[]
  | (tail,_) :: remaining -> let rest = List.rev remaining in tail, (List.map (fun (x,_) -> x) rest)

let construct_data_collection (context : LFContext.t) (variables : (string * string) list) : string = 
  let non_types = List.filter (fun (v,_) -> not (Hashtbl.mem context.types v)) variables in
  let variable_string = 
    List.fold_left ( fun acc (var,typ) -> (Consts.fmt "%s (%s : %s)" acc var typ) ) "" non_types in
  let examples = List.map 
    (fun (var_str,_) -> Consts.fmt "\"%s:\" ++ \"(\" ++ show %s ++ \")\"" var_str var_str)
    non_types |> String.concat "++ \"|\" ++" in
  if (List.length non_types = 0) 
    then raise (Failure "Case without variables in goal state not handled (triggered in ExampleGeneration.ml)") else ();
  let last_variable, others = break_off_last non_types in
  let func_signature = Consts.fmt ("Definition collect_data%s :=\n") variable_string
  in Consts.fmt ("%s let lfind_var := %s\n in let lfind_v := print %s lfind_var\n in lfind_state %s lfind_v.\n")
  func_signature examples last_variable (String.concat " " others)

let quickchick_prereqs_helper (context : LFContext.t) (lfind_state_definition : string): string =
  let file_intro = LFUtils.coq_file_intro context in
  let quickchick_import = LFUtils.quickchick_imports context 75 in
  let lfind_generator_prereqs =  String.concat "\n"
    [file_intro; (lfind_state_definition ^ "\n"); quickchick_import]
  in lfind_generator_prereqs ^ "\n" 

  let coq_quickchick_prereqs (context : LFContext.t) : string = (* Might be used outside of file *)
  let lfind_state_definition = get_lemma_statement_for_generation context in 
  quickchick_prereqs_helper context lfind_state_definition

let get_vars_with_type (context : LFContext.t) (generalized : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t) :
(string * string) list = 
  let from_table tbl = Hashtbl.fold (fun var_str (typ,var,expr) acc -> acc @ [(var_str,LFContext.e_str context typ)]) tbl [] in
  (from_table context.variables) @ (from_table generalized)

let get_print_signature (context : LFContext.t) (variables : (string * string) list) =
  let vars = List.rev variables in
  let non_types = List.filter (fun (var,_) -> (Hashtbl.mem context.types var) = false) vars in 
  let type_string = match non_types  with 
  | [] -> "nat"
  | (_,typ) :: _ -> typ
  in Consts.fmt ("Parameter print : (%s) -> string -> (%s).\n") type_string type_string

let get_generation_lemma (context : LFContext.t) (variables : (string * string) list) : string = 
  let implicit_types = ref "" in
  let var_str = List.fold_left 
  (
    fun acc (var,typ) -> 
      if Hashtbl.mem context.types var then (implicit_types := !implicit_types ^ (Consts.fmt "{%s}" var); acc)
      else (Consts.fmt "%s (%s : %s)" acc var typ)
  ) "" variables in
  let conjunction_body = List.fold_left
  (
    fun acc (var,typ) -> 
      if Hashtbl.mem context.types var then acc
      else acc @ [(Consts.fmt "(@eq (%s) %s %s)" typ var var)]
  ) [] variables |> String.concat " /\\ "
 in Consts.fmt "Lemma lfind_state %s %s : %s.\nAdmitted." !implicit_types var_str conjunction_body

let generate (context : LFContext.t) (example_filename : string) 
(generalized : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t) : string list =
  create_extraction_file context.lfind_dir example_filename;
  let generator = Consts.fmt ("%s/%s") context.lfind_dir "lfind_example_generator.v" in 
  let all_variables = get_vars_with_type context generalized in
  let generation_lemma = get_generation_lemma context all_variables in
  let lfind_generator_prereqs = quickchick_prereqs_helper context generation_lemma in
  let extract_print_const = "Extract Constant print => \"Extract.print\".\n" in (* Consts.extract_print *)
  let signature = get_print_signature context all_variables in
  let example_print_content = Consts.fmt("%s\n%s%s")  Consts.string_scope signature extract_print_const in
  let collect_content = construct_data_collection context all_variables in
  let content = lfind_generator_prereqs ^ example_print_content ^ collect_content ^ "QuickChick collect_data.\n" ^ Consts.vernac_success in
  Utils.write_to_file generator content;
  let cmd = Consts.fmt "cd %s/ && coqc -R . %s %s" context.lfind_dir context.namespace generator
  in Utils.run_cmd cmd

let parse_single_example (example : string) : (string, string) Hashtbl.t = 
  let split_by_variable = String.split_on_char '|' example in
  let example_table = Hashtbl.create (List.length split_by_variable) in
  List.iter 
  (fun ex -> 
    let values = String.split_on_char ':' ex in
    try 
    let var_name, value = (List.hd values), (List.hd (List.tl values))
    in Hashtbl.add example_table var_name value with _ -> ()
  ) split_by_variable; example_table

let parse (example_file : string) : ((string, string) Hashtbl.t) list =
  let file_contents = Utils.read_file example_file in 
  List.map parse_single_example (Utils.remove_duplicates (String.equal) file_contents) (* Note: consider printing examples differently to avoid bugs *)