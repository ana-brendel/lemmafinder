type t = 
{
  label : string;
  lemma : EConstr.t; (* This is the proposed helper lemma *)
  variables : (string, (EConstr.t * Names.variable * EConstr.t)) Hashtbl.t; (* string , (type,var,term) *)
  provable : bool;
}

let equal (context : LFContext.t) (a : t) (b : t) : bool =
  String.equal (LFContext.e_str context a.lemma) (LFContext.e_str context b.lemma)

let rec get_body (context : LFContext.t) (lemma : EConstr.t) : string =
  match Constr.kind (EConstr.to_constr context.sigma lemma) with
  | Prod (_,hypo,result) -> (
    let h_str = get_body context (EConstr.of_constr hypo) in
    let r_str = get_body context (EConstr.of_constr result) in
    "not (" ^ h_str ^ ") \\/ (" ^ r_str ^ ")"
    )
  | _ -> LFContext.e_str context lemma

let get_pretty_print_for_filter_script (context : LFContext.t) (conj : t) : string =
  let lemma_intro = if (Hashtbl.length conj.variables = 0)  then conj.label ^ ": " else conj.label ^ ": forall " in
  let implicit_types = ref "" in
  let variables_strings = 
  Hashtbl.fold
  (
    fun var_str (typ,_,_) accum ->
      if (Constr.is_Type (EConstr.to_constr context.sigma typ) || Constr.is_Set (EConstr.to_constr context.sigma typ))
      then (implicit_types := !implicit_types ^ "{" ^ var_str ^ "} "; accum) 
      else accum @ [("(" ^ var_str ^ " : " ^ (LFContext.e_str context typ) ^ ")")]
  ) conj.variables [] in 
  let variables_str = String.concat " " (List.filter (fun x -> String.equal "" x = false) variables_strings) in
  let all_variables_string = !implicit_types ^ variables_str in
  let formated_variables = if (String.equal "" all_variables_string) then "" else (all_variables_string ^ ", ") in
  let body = get_body context conj.lemma in
  let str = lemma_intro ^ formated_variables ^ body in
  String.concat " " (String.split_on_char '\n' str)

let get_pretty_print (context : LFContext.t) (result : t) : string = 
  "Lemma " ^ (get_pretty_print_for_filter_script context result) ^ "."

let from_generalizations (context : LFContext.t) (generalizations : Generalization.t list) : t list =
  List.mapi
  (fun i (g : Generalization.t) -> { label = Consts.fmt "candidate_%d" (i + 1); lemma = g.goal; variables = g.variables; provable = false; }) 
  generalizations

let from_synthesis (offset : int) (context : LFContext.t) (results : (string, string list) Hashtbl.t)
(sketches : Sketch.t list) (problems_by_sketch : (string, string) Hashtbl.t) : t list  = 
  let index = ref (offset - 1) in
  let get_conjectures (sketch : Sketch.t) : t list = 
    let problem = try Hashtbl.find problems_by_sketch sketch.label 
    with _ -> raise (Failure ("Sketch " ^ (LFContext.e_str context sketch.goal_with_hole) ^ " without problem (triggered in Conjecture.ml).")) in
    let results = try Hashtbl.find results problem
    with _ -> raise (Failure ("Problem " ^ problem ^ " without results list (triggered in Conjecture.ml).")) in
    List.map
    ( 
      fun r -> index := !index + 1;
        let lemma = ExampleManagement.replace_var_with_value context "(##hole##)" r sketch.goal_with_hole in
        { label = Consts.fmt "candidate_%d" !index; lemma; variables = sketch.variables; provable = false; }
    ) results in
  List.flatten (List.map get_conjectures sketches)

