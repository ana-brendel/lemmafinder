
(* This file contains the abstractions for the synthesizer and the prover that we are using, separate from logic of system *)

type synthesizer =
{
  command : string;
  logical_dir : string;
  phyiscal_dir : string;
  coq_module : string;
  extra_expr : string list;
}

(* This is the Synthesis.t type for individual queries to synthesizer: 
  { label : string; params : (string * string) list; output_type : EConstr.t; examples : (string * string) list; } *)

let get_functions_from_global (context : LFContext.t) (expr : string list) : string list =
  let filter_consts (x : Names.Constant.t) ((p,_) : Opaqueproof.opaque Declarations.constant_body * _) =
    match p.const_body with
    | Def a -> let a_constr = Mod_subst.force_constr a in (Utils.contains (Names.Constant.to_string x) context.namespace) 
    && ((Constr.isFix a_constr) || (Constr.isCoFix a_constr) (*|| (Constr.isConst a_constr)*)) (* Need to handle non-Fixpoint defintions*)
    | _ -> false in
  let global_view = Environ.Globals.view context.env.env_globals in
  let filtered_const = Names.Cmap_env.filter filter_consts global_view.constants in
  Names.Cmap_env.fold 
  (fun x _ acc -> let str = Consts.fmt "@%s " (Names.Constant.to_string x) in
    if List.mem str expr then acc else str :: acc) 
  filtered_const []

let get_extra_expressions (context : LFContext.t) : string list =
  let expr = Hashtbl.fold
  (
    fun _ (func,typ_params,_) accum ->
      ((Utils.get_func_str_with_mod context.env context.sigma func) ^ " " ^ 
        String.concat " " (List.map (fun x -> "(" ^ LFContext.e_str context x ^ ")") typ_params)) :: accum
  ) context.functions [] in 
  expr @ (get_functions_from_global context expr)

let get_synthesizer (context : LFContext.t) : synthesizer =
  let command = Consts.coq_synthesizer_path in (* "coq_synth" *)
  let logical_dir = context.namespace in 
  let phyiscal_dir = context.original_dir in
  let coq_module = context.filename in
  let extra_expr = get_extra_expressions context in
  { command; logical_dir; phyiscal_dir; coq_module; extra_expr }

let get_full_output_type (context : LFContext.t) (typ : EConstr.t) : string =
  match (Utils.get_func_str_with_mod context.env context.sigma typ) with 
  | "" -> LFContext.e_str context typ
  | typ_string -> typ_string

let synthesis_command (context : LFContext.t) (s : synthesizer) (problem : Synthesis.t) : string * string =
  let synth_command = Consts.coq_synthesizer_path in
  let output_file = context.lfind_dir ^ "/" ^ context.filename ^ problem.label ^ "synthesis.txt" in
  let logical_dir = "--logical-dir=" ^ s.logical_dir in
  let phyiscal_dir = "--physical-dir=\"" ^ s.phyiscal_dir ^ "\"" in
  let coq_module = "--module=" ^ s.coq_module in
  let output_type = "--type=\'" ^ (get_full_output_type context problem.output_type) ^ "\'" in
  let params = "--params=\'" ^ (String.concat "," (List.map (fun (var,typ) -> var ^ ":" ^ typ) problem.params)) ^ "\'" in
  let extra_exprs = "--extra-exprs=\'" ^ (String.concat "," s.extra_expr) ^ "\'" in
  let examples = "--examples=\'" ^ (String.concat ";" (List.map (fun (inp,out) -> inp ^ "=" ^ out) problem.examples)) ^ "\'" in
  let num_terms = "--num-terms=" ^ string_of_int (Consts.synth_batch_size) in
  let output_direction = "> " ^ output_file in
  let timeout = Consts.fmt "timeout  %s" Consts.synthesizer_timeout in
  let cmd_contents = [timeout;synth_command;logical_dir;phyiscal_dir;coq_module;output_type;params;extra_exprs;examples;num_terms;output_direction] in
  output_file, String.concat " " cmd_contents

let run_synthesizer (context : LFContext.t) (synthesizer : synthesizer) (problem : Synthesis.t) : string list =
  let file, cmd = synthesis_command context synthesizer problem in
  try let _ = Utils.run_cmd cmd in let output = Utils.read_file file in 
  if !Consts.clean_up then let _ = Utils.run_cmd ("rm -rf " ^ file) in () else ();
  (List.map Utils.remove_parentheses output)
  with _ -> if !Consts.clean_up then let _ = Utils.run_cmd ("rm -rf " ^ file) in () else (); []

let run_synthesis (context : LFContext.t) (synthesizer : synthesizer) (problems : Synthesis.t list) : (string, string list) Hashtbl.t =
  let results = Hashtbl.create (List.length problems) in
  List.iter (fun (p : Synthesis.t) -> Hashtbl.add results p.label (run_synthesizer context synthesizer p)) problems; results

let pp_goal_for_prover (context : LFContext.t) : string = 
  let is_type s = not (Sorts.is_set s || Sorts.is_prop s || Sorts.is_sprop s || Sorts.is_small s) in
  let keep_hyps = true in
  let lemma = Consts.lfind_lemma in
  let conc = LFContext.e_str context context.goal in
  let var_types_opt = List.map 
    (fun hyp -> match hyp with
    | Context.Named.Declaration.LocalAssum(x, y) -> 
      let (sigma', s) = Typing.sort_of context.env context.sigma y in
      if (keep_hyps || Sorts.is_set s || is_type s) then Some (x.binder_name, y) else None
    | Context.Named.Declaration.LocalDef(x, _, y) -> (* NOT SURE IF THIS IS CORRECT BEHAVIOR *)
      let (sigma', s) = Typing.sort_of context.env context.sigma y in
      if (keep_hyps || Sorts.is_set s || is_type s) then Some (x.binder_name, y) else None
    ) context.hypotheses in
  let var_types = List.filter (fun x -> match x with | None -> false | _ -> true) var_types_opt in
  let vars_str = 
    List.map 
    (
      fun opt -> 
        match opt with 
        | None -> ""
        | Some (v, t) -> "(" ^ Names.Id.to_string (v) ^ " : " ^ (LFContext.e_str context t) ^ ")"
    ) (List.rev var_types) |> String.concat " "  in
  if List.length var_types = 0 then Consts.fmt "Lemma current_goal:%s." conc
  else Consts.fmt "Lemma current_goal %s: %s." vars_str conc 