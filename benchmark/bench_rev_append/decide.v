Load LFindLoad.
From test Require Import rev_append.
From QuickChick Require Import QuickChick.
Require Export Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Require Import String. Open Scope string.

(* ************************** [ NAT ] *************************** *)
Derive Show for nat.
Derive Arbitrary for nat.
Instance Dec_Eq_nat : Dec_Eq nat.
Proof. dec_eq. Qed.

(* ************************** [ BOOL ] *************************** *)
Derive Show for bool.
Derive Arbitrary for bool.
Instance Dec_Eq_bool : Dec_Eq bool.
Proof. dec_eq. Qed.

(* ************************** [ LIST ] *************************** *)
Instance show_list {T} `{_ : Show T} : Show (list T) := 
{| show := 
    let fix aux l :=
      match l with
      | nil => "nil"
      | cons x xs => "cons " ++ show x ++ " (" ++ aux xs ++ ")"
      end
    in aux
|}.
Derive Arbitrary for list.
Instance Dec_Eq_list {T} `{_ : Dec_Eq T}  : Dec_Eq (list T).
Proof. dec_eq. Qed.
