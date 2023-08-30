let create_extraction_file (dir : string) (filename : string) : unit =
  let lfind_content = "
  module SS = Set.Make(String)
  let values = ref SS.empty
    
  let write_to_file value=
    let oc = open_out_gen [Open_append; Open_creat] 0o777 \""^dir ^"/examples_" ^ filename ^ ".txt\" in
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

let get_print_signature (context : LFContext.t) =
  let vars = List.rev (LFContext.get_variable_list context) in
  let non_types = List.filter (fun x -> (Hashtbl.mem context.types (Names.Id.to_string x)) = false) vars in 
  let type_string = match non_types  with 
  | [] -> "nat"
  | var :: _ -> try
    (
      match Hashtbl.find context.variables (Names.Id.to_string var) with
      | (typ,_,_) -> LFContext.e_str context typ
    ) with _ -> "nat"
  in Consts.fmt ("Parameter print : %s -> string -> %s.\n") type_string type_string

let break_off_last (vars : Names.variable list) :  (string * string list) =
  match List.rev vars with
  | [] -> "",[]
  | id :: remaining -> 
    let tail_str = Names.Id.to_string id in
    let rest = List.rev remaining in
    let rest_str = List.map (fun x -> Names.Id.to_string x) rest in
    tail_str, rest_str

let construct_data_collection (context : LFContext.t) : string = 
  let variable_string = 
    List.fold_left 
    (
      fun acc var -> 
        try
          let (typ,_,_) = Hashtbl.find context.variables var in
          if (Hashtbl.mem context.types var) (* checks to see if the variable is a type*)
          then acc
          else (acc ^ " (" ^ var ^ " : " ^ (LFContext.e_str context typ) ^ ")")
      with _ -> print_endline "Type not found, potential error"; acc
    )
    ""
    (List.map Names.Id.to_string (LFContext.get_variable_list context)) in
  let examples = 
    List.map 
    (fun var_str -> 
      (let show_str = Consts.fmt "show %s" var_str in
        Consts.fmt "\"%s:\" ++ \"(\" ++ %s ++ \")\"" var_str show_str)) 
    (List.filter (fun x -> not (Hashtbl.mem context.types x)) (List.map Names.Id.to_string (LFContext.get_variable_list context))) 
    |> String.concat "++ \"|\" ++" in
  let non_types = LFContext.non_type_variables context in
  if (List.length non_types = 0) 
    then raise (Failure "Case without variables in goal state not handled (triggered in ExampleGeneration.ml)") else ();
  let last_variable, others = break_off_last non_types in
  let func_signature = Consts.fmt ("Definition collect_data%s :=\n") variable_string
  in Consts.fmt ("%s let lfind_var := %s\n in let lfind_v := print %s lfind_var\n in lfind_state %s lfind_v.\n")
  func_signature examples last_variable (String.concat " " others)

let coq_quickchick_prereqs (context : LFContext.t) : string =
  let lfind_state_definition = get_lemma_statement_for_generation context in 
  let file_intro = LFUtils.coq_file_intro context in
  let quickchick_import = LFUtils.quickchick_imports context 50 in
  let lfind_generator_prereqs =  String.concat "\n"
    [file_intro; (lfind_state_definition ^ "\n"); quickchick_import]
  in lfind_generator_prereqs ^ "\n" 

let run (context : LFContext.t) : string list =
  create_extraction_file context.lfind_dir context.filename; 
  let example_file = Consts.fmt ("%s/%s") context.lfind_dir "lfind_quickchick_generator.v" in 
  let lfind_generator_prereqs = coq_quickchick_prereqs context in
  let extract_print_const = "Extract Constant print => \"Extract.print\".\n" in (* Consts.extract_print *)
  let example_print_content = Consts.fmt("%s\n%s%s")  Consts.string_scope (get_print_signature context) extract_print_const in
  let collect_content = construct_data_collection context in
  let content = lfind_generator_prereqs ^ example_print_content ^ collect_content ^ "QuickChick collect_data.\n" ^ Consts.vernac_success in
  Utils.write_to_file example_file content;
  let cmd = Consts.fmt "cd %s/ && coqc -R . %s %s" context.lfind_dir context.namespace example_file
  in Utils.run_cmd cmd
