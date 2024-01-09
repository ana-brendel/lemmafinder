Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.
From QuickChick Require Import QuickChick.
QCInclude ".".
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".
Require Coq.extraction.Extraction.
Extraction Language OCaml.

Require Import Coq.Lists.List.

(* Target Lemma *)
(* Lemma rev_append: forall {T} (x y : list T), rev (x ++ y) = rev y ++ rev x. *)

Theorem rev_rev : forall {T} (x : list T), rev (rev x) = x.
Proof.
intros.
induction x.
- reflexivity.
- simpl.
 lfind. 
 Admitted.

(* rewrite rev_append. rewrite IHx. reflexivity.
Qed. *)