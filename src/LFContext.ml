type t = 
{ 
  env: Environ.env;
  sigma: Evd.evar_map;
  hypotheses : EConstr.named_context;
  goal : EConstr.t;
  variables : (string, (EConstr.t * Names.variable * EConstr.t)) Hashtbl.t; (* string , (type,var,term) *)
  terms : (string, (EConstr.t * EConstr.t)) Hashtbl.t; (* string , (term,type) *)
  types : (string, EConstr.t * bool) Hashtbl.t; (* string , (type,?polymorphic) *)
  functions : (string, EConstr.t * EConstr.t list * EConstr.t) Hashtbl.t; (* string , (econstr,?polymorphic arguments,type) *)
  filename: string;
  original_dir: string;
  lfind_dir: string;
  full_context: string; (* do we use? *)
  namespace: string;
  declarations: string;
  proof_name: string;
  theorem: string;
}

let e_str (c : t) : EConstr.t -> string = LFCoq.string_of_econstr c.env c.sigma 

let c_str (c : t) : Constr.t -> string = LFCoq.string_of_constr c.env c.sigma 

let get_variable_list (c : t) : Names.variable list = Hashtbl.fold (fun _ (_,var,_) acc -> acc @ [var]) c.variables []

let non_type_variables (context : t) : Names.variable list =
  let vars = List.map Names.Id.to_string (get_variable_list context) in
  LFCoq.non_types_helper context.types vars context.variables

let pp_context (c : t) : string =
  let hyps = LFCoq.process_hyps c.hypotheses in
  let contents = 
    [
      "File Information";
      (Consts.fmt "- File name: %s" c.filename);
      (Consts.fmt "- Original Directory: %s" c.original_dir);
      (Consts.fmt "- LFind Directory: %s" c.lfind_dir);
      (Consts.fmt "- Namespace: %s" c.namespace);
      (Consts.fmt "- Proof name: %s" c.proof_name);
      (Consts.fmt "- Theorem: %s" c.theorem);
      (Consts.fmt "- Declarations: %s" c.declarations);
      "";
      "Proof Context";
      (Consts.fmt "* Goal State: %s" (e_str c c.goal));
      (Consts.fmt "\n* Hypothesis:\n%s" 
      (String.concat "\n" (Hashtbl.fold (fun h (_,hyp) acc -> (h ^ " : " ^ (e_str c hyp)) :: acc) hyps [])));
      (Consts.fmt "\n* Types:\n%s" (String.concat "\n" (Utils.get_keys c.types)));
      (Consts.fmt "\n* Polymorphic Types:\n%s" 
      (String.concat "\n" (Hashtbl.fold (fun typ (_,poly) acc -> if poly then typ :: acc else acc) c.types [])));
      (Consts.fmt "\n* Variables:\n%s" 
      (String.concat "\n" (Hashtbl.fold (fun var (typ,_,_) acc -> (var ^ " : " ^ (e_str c typ)) :: acc) c.variables [])));
      (Consts.fmt "\n* Terms:\n%s" 
      (String.concat "\n" (Hashtbl.fold (fun term (_,typ) acc -> (term ^ " : " ^ (e_str c typ)) :: acc) c.terms [])));
      (Consts.fmt "\n* Functions:\n%s" 
      (String.concat "\n" 
      (Hashtbl.fold 
      (fun f (_,args,typ) acc -> 
        (f ^ " " ^ (String.concat " " (List.map (fun x -> "("^ (e_str c x) ^")") args)) ^ " : " ^ (e_str c typ)) :: acc) c.functions [])));
    ] in
    String.concat "\n" contents

let get_terms (env : Environ.env) (sigma : Evd.evar_map) (econstrs : EConstr.t list) : (string, (EConstr.t * EConstr.t)) Hashtbl.t =
  let terms_and_type = List.fold_left (LFCoq.terms_in_econstr env sigma) [] econstrs in
  let terms = Hashtbl.create (List.length terms_and_type) in
  List.iter (fun (term,typ) -> Hashtbl.add terms (LFCoq.string_of_econstr env sigma term) (term,typ)) terms_and_type;
  terms

let get_variables (env : Environ.env) (sigma : Evd.evar_map) (terms : (string, (EConstr.t * EConstr.t)) Hashtbl.t) 
(econstrs : EConstr.t list)  : (string, (EConstr.t * Names.variable * EConstr.t)) Hashtbl.t = 
  let varIds = List.flatten (List.map (fun e -> LFCoq.vars_from_constr env sigma (Hashtbl.create 0) [] (EConstr.to_constr sigma e)) econstrs) in
  let eq_vars (a : Names.variable) (b : Names.variable) : bool =
    String.equal (Names.Id.to_string a) (Names.Id.to_string b) in
  let vars_simplified = Utils.remove_duplicates eq_vars varIds in
  let result = Hashtbl.create (List.length vars_simplified) in
  List.iter 
  (
    fun var -> let var_str = Names.Id.to_string var in
      try 
        let (term,typ) = Hashtbl.find terms var_str in
        Hashtbl.add result var_str (typ,var,term)
      with _ -> print_endline ("No type found for: " ^ var_str)
  ) vars_simplified; result

(* might want to consider a case where function is polymorphic but is used with two different types *)
let get_functions (env : Environ.env) (sigma : Evd.evar_map) (econstrs : EConstr.t list)  
: (string, EConstr.t * EConstr.t list * EConstr.t) Hashtbl.t = 
  let funcs = List.flatten (List.map (fun e -> LFCoq.func_in_econstr env sigma [] e) econstrs) in
  let econstr_str = LFCoq.string_of_econstr env sigma in
  let eq_func (a : (EConstr.t * _ * _ list)) (b : (EConstr.t * _ * _ list)) : bool = 
    let (func_a,_,_) = a in let (func_b,_,_) = b in String.equal (econstr_str func_a) (econstr_str func_b) in
  let funcs_simplified = Utils.remove_duplicates eq_func funcs in
  let result = Hashtbl.create (List.length funcs_simplified) in
  List.iter (fun (f,typ,args) -> Hashtbl.add result (econstr_str f) (f,args,typ)) funcs_simplified; 
  result

let get_types (env) (sigma) (econstrs) (functions) : (string, EConstr.t * bool) Hashtbl.t =
  let typs = List.flatten (List.map (fun e -> LFCoq.types_in_econstr env sigma [] e) econstrs) in
  let terms = List.fold_left (LFCoq.terms_in_econstr env sigma) [] econstrs in
  let econstr_str = LFCoq.string_of_econstr env sigma in
  let from_terms = List.filter (fun (_,typ) -> ((String.equal "Set" (econstr_str typ)) or (String.equal "Type" (econstr_str typ)))) 
  terms |> List.map (fun (term,_) -> term) in
  let eq_typs (a : EConstr.t) (b : EConstr.t) : bool = String.equal (econstr_str a) (econstr_str b) in
  let typs_simplified = Utils.remove_duplicates eq_typs (typs @ from_terms) in
  let result = Hashtbl.create (List.length typs_simplified) in
  List.iter 
  (
    fun typ -> 
      let typ_str = LFCoq.string_of_econstr env sigma typ in
      let first = List.hd (String.split_on_char ' ' typ_str) in
      let poly = Hashtbl.mem functions first in
      Hashtbl.add result typ_str (typ,poly)
  ) typs_simplified; result

let get_proof (gl : Proofview.Goal.t) =
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let hypotheses = Proofview.Goal.hyps gl in (* hyps are in opposite order of coqide *)
  let goal = Proofview.Goal.concl gl in
  let econstrs = goal :: (Hashtbl.fold (fun _ (_,e) acc -> e :: acc) (LFCoq.process_hyps hypotheses) []) in
  let terms = get_terms env sigma econstrs in (* as a list in case we want to gather terms from hypotheses *)
  let variables = get_variables env sigma terms econstrs in
  let functions = get_functions env sigma econstrs in
  let types = get_types env sigma econstrs functions in
  (env, sigma, goal, hypotheses, variables, terms, types, functions)

(* Copied over from the original proof context file *)
let get_directories paths =
  List.fold_left 
  (fun (namespace, dir) path ->
    let path_str = (Utils.get_str_of_pp (Loadpath.pp (path)))
    in let is_contains = Utils.contains path_str "Coq."
    in if is_contains || not (String.equal dir "") 
    then (namespace, dir)
    else
    (
      let pathlst = (String.split_on_char ' ' path_str)
      in let namespace = List.hd pathlst
      in let dir = List.hd (List.rev pathlst)
      in (namespace, dir)
    )
  ) ("", "") paths
 
(* Copied over from the original proof context file *)
let get_declarations dir fname =
  let lines = Utils.read_file (dir ^ "/" ^ fname ^ ".v")
  in List.fold_right 
  (fun line acc -> 
    let is_comment = Utils.contains line "*"
    in let is_quickchick = Utils.contains line "QuickChick"
    in if (not is_comment) && (not is_quickchick) && (Utils.contains line "Import")
        then acc ^ "\n" ^ line
        else acc
  ) lines "" 

let get_file (env : Environ.env) (sigma: Evd.evar_map) =
  let paths = Loadpath.get_load_paths ()
  in let namespace_prime, original_dir = get_directories paths
  in let namespace = List.hd (String.split_on_char '\n' namespace_prime)
  in let parent_dir, this_dir = Utils.get_parent_curr_dir original_dir in
  (* This is the line that creates the lfind directory by copying from original *)
  let lfind_dir = parent_dir ^ "_lfind_" ^ this_dir in Utils.cp_dir original_dir (lfind_dir); 
  let full_context = Pp.string_of_ppcmds (Prettyp.print_full_context env sigma) in
  let library = List.hd (String.split_on_char '\n' full_context) in
  let filename = List.hd (List.rev (String.split_on_char '.' library)) in
  let declarations = get_declarations lfind_dir filename in
  let pstate = 
    match Vernacstate.Proof_global.get_pstate () with 
    | Some ps -> ps 
    | _ -> (raise (Invalid_argument "proof state")) in
  let pdata = Proof.data (Proof_global.get_proof pstate) in
  let proof_name = Names.Id.to_string pdata.name in
  let theorem = 
  try
    match List.hd (Proofview.initial_goals pdata.entry) with
    | (_,initial_goal) -> "Theorem " ^ proof_name ^ ": " ^ (LFCoq.string_of_econstr env sigma initial_goal) ^ "."
  with _ -> (raise (Invalid_argument "empty entry")) in
  (filename, original_dir, lfind_dir, full_context, namespace, declarations, proof_name, theorem)

let get (gl : Proofview.Goal.t) : t =
  let env, sigma, goal, hypotheses, variables, terms, types, functions = get_proof gl in 
  let filename, original_dir, lfind_dir, full_context, namespace, declarations, proof_name, theorem = get_file env sigma in
  { 
    env; sigma; goal; hypotheses; variables; terms; types; functions;
    filename; original_dir; lfind_dir; full_context; namespace; declarations; proof_name; theorem
  } 

let get_goal_subterms (c : t) : EConstr.t list =
  let goal_terms = get_terms c.env c.sigma [c.goal] in
  let econstrs = Hashtbl.fold (fun _ (term,_) acc -> term :: acc) goal_terms [] in
  List.sort (fun a b -> (String.length (e_str c b)) - (String.length (e_str c a))) econstrs