type t = 
{
  label : string;
  goal : EConstr.t;
  hypotheses : EConstr.named_context;
  variables : (string, (EConstr.t * Names.variable * EConstr.t)) Hashtbl.t; (* string , (type,var,term) *)
  valid : bool;
  counterexamples : (string, string) Hashtbl.t list; (* Counter-examples, if invalid *)
}

let non_type_variables (context : LFContext.t) (g : t) : Names.variable list =
  let vars = List.rev (Utils.get_keys g.variables) in
  LFCoq.non_types_helper context.types vars g.variables

let rec generate_powerset = function
| [] -> [[]]
| h :: t -> 
  let later_sets = generate_powerset t in
  let tmp = List.map (fun x -> h :: x) later_sets in
  tmp @ later_sets

let pp (context : LFContext.t) (generalization : t) : string = 
  let lemma_intro = "Lemma " ^ generalization.label ^ ": forall " in
  let implicit_types = ref "" in
  let variables_strings = Hashtbl.fold
  (
    fun var_str (typ,var,term) acc ->
      let var_type = LFContext.e_str context typ in
      match var_type with
      | "" -> raise (Failure "Variable type not found (triggered in Generalization.ml)")
      | "Type" -> implicit_types := Consts.fmt "%s{%s} " !implicit_types var_str; acc
      | "Set" -> implicit_types := Consts.fmt "%s{%s} " !implicit_types var_str; acc
      | _ -> ("(" ^ var_str ^ " : " ^ var_type ^ ")") :: acc
  ) generalization.variables [] in 
  let variables_str = String.concat " " variables_strings in
  let body = LFContext.e_str context generalization.goal in
  lemma_intro ^ !implicit_types ^ variables_str ^ ", " ^ body ^ "."

let quickchick (context : LFContext.t) (g : t) : string =
  let lemma_prettyprint = pp context g in
  LFUtils.create_quickchick_file context g.label lemma_prettyprint

let equal (context : LFContext.t) (g1 : t) (g2 : t) : bool =
  let goals_equal = String.equal (LFContext.e_str context (g1.goal)) (LFContext.e_str context (g2.goal)) in
  let check_hyps_equal = 
    (fun h1 h2 -> 
      let (v1, e1) = match h1 with Context.Named.Declaration.LocalAssum(x,y) -> (Context.(x.binder_name), y) in
      let (v2, e2) = match h2 with Context.Named.Declaration.LocalAssum(x,y) -> (Context.(x.binder_name), y) in
      String.equal (LFContext.e_str context e1) (LFContext.e_str context e2)
      && Names.Id.equal v1 v2) in
  let hyps_equal = List.length g1.hypotheses == List.length g2.hypotheses &&
    List.fold_left (&&) true (List.map2 check_hyps_equal g1.hypotheses g2.hypotheses) in
  goals_equal

let generalize_with_variable (context : LFContext.t) (goal : EConstr.t) (term : EConstr.t) (var : Names.variable) : EConstr.t =
  let variable_econstr = EConstr.of_constr (Constr.mkVar var) in
  LFUtils.replace_subterm_econstr context goal term variable_econstr

let generalize_hypotheses (context : LFContext.t) (hypotheses : EConstr.named_context) (term : EConstr.t) (typ : EConstr.t) 
(var : Names.variable) : EConstr.named_context =
  let new_hyp_for_var = Context.Named.Declaration.of_tuple ((Context.annotR var),None,typ) in
  let rec iterate_hyps = function
  | [] -> []
  | h :: t -> 
    let bind,econstr = match h with Context.Named.Declaration.LocalAssum(x,y) -> (x, y) in
    let updated_econstr = generalize_with_variable context econstr term var in
    (Context.Named.Declaration.of_tuple (bind,None,updated_econstr)) :: iterate_hyps t
  in new_hyp_for_var :: iterate_hyps hypotheses

let generalize_single_term (context : LFContext.t) (goal : EConstr.t) (hyps : EConstr.named_context)
(typ : EConstr.t) (econstr : EConstr.t) (var : Names.variable) : EConstr.t * EConstr.named_context =
  let updated_goal = generalize_with_variable context goal econstr var in
  let generalize = Utils.contains (LFContext.e_str context updated_goal) (Names.Id.to_string var) in
  let update_hypotheses = 
    match generalize with
    | false -> hyps
    | true -> (generalize_hypotheses context hyps econstr typ var) 
  in (updated_goal,update_hypotheses)

let generalize_set_of_terms (context : LFContext.t) (generalized : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t) 
(index : int) (vars : string list) : t = 
  let terms_generalizing = 
    List.map 
    (
      fun var -> let (_,_,term) = try Hashtbl.find generalized var
        with _ -> raise (Failure (Consts.fmt "1. Generalized variable [%s] not recorded/found (triggered in Generalization.ml)" var))
        in (var,term)
    ) vars in
  let var_x_term_to_generalize = List.map (fun (v,t) -> (v,(LFContext.e_str context t))) (List.sort 
    (fun (_,a) (_,b) -> (String.length (LFContext.e_str context b)) - (String.length (LFContext.e_str context a))) 
    terms_generalizing) in
  let label = ("conj" ^ (string_of_int (index +1))) in
  let generalized_goal = context.goal in
  let generalized_hyps = context.hypotheses in
  let rec generalize (g : EConstr.t) (hyps : EConstr.named_context) = function
  | [] -> (g,hyps)
  | (var_str, term) :: remaining ->
    (* Check if the term is in the goal state at all *)
    if (Utils.contains (LFContext.e_str context g) term)
    then 
      (
        let (typ,var,econstr) = try Hashtbl.find generalized var_str
        with _ -> raise (Failure (Consts.fmt "2. Generalized variable [%s] not recorded/found (triggered in Generalization.ml)" var_str)) in 
        let (update_goal, update_hyps) = generalize_single_term context g hyps typ econstr var in
        generalize update_goal update_hyps remaining
      )
    else (generalize g hyps remaining)
  in let goal, hypotheses = generalize generalized_goal generalized_hyps var_x_term_to_generalize in
  let varIds =  LFCoq.vars_from_constr context.env context.sigma context.variables [] (EConstr.to_constr context.sigma goal) in
  let variables = Hashtbl.create (List.length varIds) in
  List.iter 
  (
    fun var -> 
      let var_str = Utils.remove_parentheses (Names.Id.to_string var) in 
      let value = try Hashtbl.find context.variables var_str 
      with _ -> try Hashtbl.find generalized var_str 
      with _ -> raise (Failure (Consts.fmt "3. Generalized variable [%s] not recorded/found (triggered in Generalization.ml)" var_str)) in
      Hashtbl.add variables var_str value
  ) varIds;
  { label; goal; hypotheses; variables; valid = false; counterexamples = [];}

let get_generalized_vars (context : LFContext.t) (terms : string list) 
: (string, (EConstr.t * Names.variable * EConstr.t)) Hashtbl.t  =
  let result = Hashtbl.create (List.length terms) in
  let rec aux index = function
  | [] -> ()
  | expr :: remaining -> 
    try 
      let (term,typ) = Hashtbl.find context.terms expr in
      (* We don't want the generalized variable to be a proposition *)
      if (String.equal (LFContext.e_str context typ) "Prop") then aux index remaining
      else
      (
        let new_var = Names.Id.of_string ("lf" ^ (string_of_int index)) in 
        Hashtbl.add result ("lf" ^ (string_of_int index)) (typ,new_var,term); (* string , (type,var,term) *)
        aux (index + 1) remaining 
      ) 
    with _ -> raise (Failure ("Expression (" ^ expr ^ ") not in table (triggered in Generalization.ml)."))
  in aux 1 terms; result

let get_terms_to_generalize (context : LFContext.t) : string list =
  let goal_terms_str = List.map (LFContext.e_str context) (LFContext.get_goal_subterms context) in 
  let removed_types = List.filter (fun x -> Hashtbl.mem context.types x = false) goal_terms_str in
  let removed_variables = List.filter (fun x -> Hashtbl.mem context.variables x = false) removed_types in
  let removed_goal = List.filter (fun x -> String.equal x (LFContext.e_str context context.goal) = false) removed_variables in
  removed_goal (* terms left to potentially generalize *)

let get_generalizations (context : LFContext.t) : (string, Evd.econstr * Names.variable * Evd.econstr) Hashtbl.t * t list = 
  let terms_to_generalize_str = get_terms_to_generalize context in
  let generalized_vars = get_generalized_vars context terms_to_generalize_str in
  let sets_of_vars = generate_powerset (Utils.get_keys generalized_vars) in (* these are the generalized variables to index *)
  let results = List.mapi (generalize_set_of_terms context generalized_vars) sets_of_vars in
  let simplified_results = Utils.remove_duplicates (equal context) results in 
  generalized_vars, simplified_results