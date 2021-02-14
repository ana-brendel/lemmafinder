open Sexp
open Utils

let gen_var next_val = 
  "lf" ^ (string_of_int (next_val()))

let generalize_expr s expr next_val =
  let var_name = ref ""
  in let rec aux (acc: string list) = function 
  | (Atom tag)::tl -> (aux ((protect tag)::acc) tl)
  | (Expr e)::tl ->
    let str_to_concat= (aux [] e)
    in let to_app = if (equal e expr) then
        (  
          if String.equal !var_name ""
          then 
            var_name := (gen_var next_val);
          !var_name
        )
      else 
        "(" ^
        (String.concat " " str_to_concat)
        ^ ")"
      in
      aux (to_app::acc) tl
  | [] -> (List.rev acc)
  in
  let str_expr = (aux [] s)
  in String.concat " " str_expr, !var_name
  
let generalize_exprL exprL type_table goal =
  let sigma = Hashtbl.create 100
  in let counter = ref 0 
  in List.fold_left 
             (fun (acc, sigma) e ->
                let gen, var_name = (generalize_expr acc e (Utils.next_val counter))
                in if String.equal var_name ""
                    then 
                      acc, sigma
                    else 
                      ((Hashtbl.add sigma var_name (e, (Hashtbl.find type_table (string_of_sexpr e))));of_string gen, sigma)
             ) 
             (goal, sigma) exprL

let gen_conjecture_name inc = 
  "conj" ^ (string_of_int (inc()))
 
let get_var_type t = 
  let return_type = (Utils.get_return_type (of_string t))
  in if String.equal return_type ""
      then return_type
      else ":" ^ return_type

let is_variable var atom_type_table = 
  let type_from_tbl = try (Hashtbl.find atom_type_table var) with Not_found -> ""
  in match type_from_tbl with
  | "" -> false
  | v -> 
            begin 
              let sexpr_type  = of_string ("(" ^ v ^ ")")
              in
              match sexpr_type with
              | [Expr [(Atom n)]] -> if String.equal n "Set" or String.equal n "Prop" then false else true
              | _ -> false
            end
  
let add_variable acc v_type = 
  let var_exists = List.exists (fun e -> String.equal e v_type) acc
  in if var_exists then acc else (v_type :: acc)

let rec get_variables_in_sexp acc expr atom_type_table = 
  match expr with
  | (Atom v) :: tl -> if (is_variable v atom_type_table)
                        then 
                        let new_acc = (add_variable acc ("(" ^ v ^":"^ (Hashtbl.find atom_type_table v) ^ ")")) 
                        in get_variables_in_sexp new_acc
                         tl atom_type_table
                        else get_variables_in_sexp (acc) tl atom_type_table

  | (Expr e) :: tl -> let head_acc = get_variables_in_sexp acc  e atom_type_table
                      in get_variables_in_sexp head_acc tl atom_type_table
  | [] -> acc

let get_conjecture gen sigma var_str counter: string =
  let conjecture_str = ": forall " ^ var_str
  in let quantified_var_str = Hashtbl.fold (fun k (e, t) acc -> acc ^ "("^ k ^ (get_var_type t) ^")")  sigma conjecture_str
  in quantified_var_str ^ " , " ^ gen


let print_generalizations generalizations atom_type_table = 
  let counter = ref 0
  in let generalized_conjecture_strings = List.map (fun (g, sigma) -> 
                  let var_str = (String.concat "" (get_variables_in_sexp [] g atom_type_table))
                  in (get_conjecture (string_of_sexpr g) sigma var_str counter)
               )
            generalizations
  in let generalized_conjecture_strings_nodup = Utils.remove_dup generalized_conjecture_strings
  in List.iter (fun s -> let conjecture_name = (gen_conjecture_name (Utils.next_val counter)) in Printf.printf "%s\n" (conjecture_name ^ s)) generalized_conjecture_strings_nodup
         
let construct_all_generalizations generalization_set type_table goal =
  List.map 
        (
          fun g -> let sorted_g = LatticeUtils.sort_by_size g
          in generalize_exprL sorted_g type_table goal
        ) generalization_set

