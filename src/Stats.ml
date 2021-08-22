open LatticeUtils
open Consts

type synthesis_stat = {
    synthesis_term : string;
    enumerated_exprs : string list;
    valid_lemmas : (string * conjecture) list;
    provable_lemmas : (string * conjecture) list;
}

type generalization_stat = {
    conjecture : conjecture;
    is_valid : bool;
    is_provable : bool;
    synthesis_stats : synthesis_stat list;
}

let global_stat : generalization_stat list ref = ref []

let get_synthesized_valid_lemmas stats=
    List.fold_left (fun acc g_stat -> 
                            acc + 
                            (List.fold_left (fun acc s_stat -> 
                                                acc + (List.length s_stat.valid_lemmas)
                                            ) 0 g_stat.synthesis_stats
                            )
                   ) 0 stats

let probable_lemmas_to_string provable_lemmas =
    List.fold_left (fun acc (_, lemma) -> 
                        acc
                        ^
                        fmt "\t\t\t Lemma : %s\n" lemma.conjecture_str
                ) "" provable_lemmas

let get_synthesized_provable_lemmas stats=
    List.fold_left (fun (acc,len) g_stat -> 
                    let new_acc, l = 
                    (List.fold_left 
                        (fun (acc_synth,len) s_stat -> 
                            let l = len + (List.length s_stat.provable_lemmas)
                            in let c_str = probable_lemmas_to_string s_stat.provable_lemmas
                            in if (List.length s_stat.provable_lemmas) > 0
                                then (acc_synth ^ "\n" ^ c_str, l)
                                else acc_synth, l
                        ) (acc, 0) g_stat.synthesis_stats
                    )
                    in new_acc, len + l
                ) ("",0) stats

let generalized_lemma_useful stats : string *int =
    List.fold_left (fun (acc,l) g -> 
                            if g.is_provable then
                            (print_endline ("here: " ^ g.conjecture.conjecture_str);
                            ((acc ^ "\n" ^ g.conjecture.conjecture_str), l+1))
                            else (acc,l)
                   ) ("", 0) stats

let summarize stats curr_state_lemma =
    let no_valid_gen_lemmas = List.length (List.filter (fun g -> g.is_valid) stats)
    in let gen_provable_lemmas, len_gen_provable_lemmas = generalized_lemma_useful stats
    in let total_synthesized_valid_lemmas = get_synthesized_valid_lemmas stats
    in let str_provable_lemmas, total_synthesized_provable_lemmas = get_synthesized_provable_lemmas stats
    in let summary =  (fmt "\n### SUMMARY ###\n"
    ^
    fmt "Stuck Proof State: %s\n"  (curr_state_lemma)
    ^
    fmt "# Generalizations : %d\n" (List.length stats)
    ^
    fmt "#Generalizations not disprovable : %d\n" no_valid_gen_lemmas
    ^
    fmt "#Generalizations useful in proving original goal: %d\nLemmas\n%s" len_gen_provable_lemmas gen_provable_lemmas
    ^
    fmt "#Synthesized Lemmas not disprovable : %d\n" total_synthesized_valid_lemmas
    ^
    fmt "#Synthesized Lemmas useful in proving original goal: %d\nLemmas\n%s" total_synthesized_provable_lemmas str_provable_lemmas)

    in Log.write_to_log summary !Log.stats_summary_file; ()

let valid_lemmas_to_string valid_lemmas =
    List.fold_left (fun acc (synthesized_expr, lemma) -> 
                            acc
                            ^
                            fmt "\t\t\t Myth Term : %s\n" synthesized_expr
                            ^
                            fmt "\t\t\t Lemma : %s\n" lemma.conjecture_str
                   ) "" valid_lemmas

let synthstat_to_string synth_stat =
    fmt "\t\t\n### Synthesis Stats ###\n"
    ^
    fmt "\t\t Synthesis Term : %s\n" synth_stat.synthesis_term
    ^
    fmt "\t\t # Myth Enumerated Terms : %d\n" (List.length synth_stat.enumerated_exprs)
    ^
    fmt "\t\t # Valid Synthesized Lemmas : %d\n" (List.length synth_stat.valid_lemmas)
    ^
    fmt "\t\t Valid Lemmas\n %s\n" (valid_lemmas_to_string synth_stat.valid_lemmas)
    ^
    fmt "\t\t # Lemmas useful to prove original goal : %d\n" (List.length synth_stat.provable_lemmas)
    ^
    fmt "\t\t Lemmas that can prove the original goal \n %s\n" (valid_lemmas_to_string synth_stat.provable_lemmas)
    ^
    fmt "------------------------------------------------------------------------\n"


let synthstats_to_string synthesis_stats =
    List.fold_left (fun acc synth_stat -> acc ^ (synthstat_to_string synth_stat)) "" synthesis_stats

let genstat_to_string gen_stat =
    fmt "\n### Generalization Stat ###\n"
    ^
    fmt "Generalized Conjecture : %s\n" gen_stat.conjecture.conjecture_str
    ^
    fmt "is_valid : %b\n" (gen_stat.is_valid)
    ^ 
    fmt "is_provable (can help prove original goal): %b\n" (gen_stat.is_provable)
    ^
    fmt "Synthesis Stats : \n %s \n" (synthstats_to_string gen_stat.synthesis_stats)
