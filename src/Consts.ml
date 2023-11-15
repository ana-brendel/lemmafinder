let lfind_declare_module = "Load LFindLoad."
let synthesizer_timeout = "12"
let coq_printing_depth = "Set Printing Depth 1000."

let fmt = Printf.sprintf

let lfind_lemma = "lfind_state"
let quickchick_import = "From QuickChick Require Import QuickChick."
let string_scope = "Open Scope string_scope.\n"
let extract_print = "Extract Constant print => \"Extract.print\".\n"
let vernac_success = "Success."
let def_qc_num_examples = "Extract Constant defNumTests => \"50\"."

let prover = "PROVERBOT"
let prover_path = ref ""
let coq_synthesizer_path = "coq_synth"
let lfind_path = ref ""
let synth_batch_size = 5

let start_time = ref 0
let clean_up = ref true
let debug = ref true
let progress = ref ""
let commands = ref ""

let decidable = ref true