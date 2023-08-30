Require Import Coq.Lists.List.
Load LFindLoad.
From lfind Require Import LFind.
Unset Printing Notations.
Set Printing Implicit.


Lemma rev_append: forall {T} (x y : list T), rev (x ++ y) = rev y ++ rev x.
Proof.
intros.
induction x.
- simpl. rewrite app_nil_r. reflexivity.
- simpl. rewrite IHx. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_rev : forall {T} (x : list T), rev (rev x) = x.
Proof.
intros.
induction x.
- reflexivity.
- simpl. lfind_debug. 
Admitted.

(* rewrite rev_append. rewrite IHx. reflexivity.
Qed. *)
