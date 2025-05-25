(* RelCond spec *)

Require Import Arith.
Require Import Coq.Arith.EqNat.
Require Import Forest.
Require Import rnk.
Require Import List.
Require Import Arith.
Require Import String.
Require Import Language.
Import ListNotations.

Arguments Pair {X} {Y}.

Notation "( A ; B )" := (Pair A B).

(* Aux function *)

Fixpoint joinRules_aux
  (tVal : nat)
  (l : list (list (pair nat (list (LF -> Target (pair LF (list nat)))))))
  :=
  match l with
  | nil => nil
  | frule::tl =>
      let rule := applyTo frule tVal nil Nat.eqb in
      rule++(joinRules_aux tVal tl)
  end.
 
Fixpoint joinRules
  (l : list (list (pair nat (list (LF -> Target (pair LF (list nat)))))))
  (auto : bool) (lV : list nat) :=
  match lV with
  | nil => nil
  | tVal::tl =>
      let rulesJoined := joinRules_aux tVal l in
      if negb (isEmpty rulesJoined) then
        (((tVal, rulesJoined), auto))::(joinRules l auto tl)
      else
        joinRules l auto tl
  end.



(* Truth-values *)

Definition vF := 0.
Definition vf := 1.
Definition vf1 := 2.
Definition vf2 := 3.
Definition vt2 := 4.
Definition vt1 := 5.
Definition vt := 6.
Definition vT := 7.

Definition V := [vF; vf; vf1; vf2; vt2; vt1; vt; vT].

Definition D := [vt; vt1; vt2; vT].
Definition F := [vf; vf1; vf2; vF].

(* Arrows *)

Definition arrowsK :=
  [
    (vT; [[vT]; [vt1]; [vt]; [vt2]]);
    (vt,
      [
        [vF; vT]; [vf1; vT]; [vf; vT]; [vf2; vT];
        [vF; vt1]; [vf1; vt1]; [vf; vt1]; [vf2; vt1];
        [vF; vt]; [vf1; vt]; [vf; vt]; [vf2; vt];
        [vF; vt2]; [vf1; vt2]; [vf; vt2]; [vf2; vt2]
    ]);
    (vt2, [[vF]; [vf1]; [vf]; [vf2]]);
    (vf,
      [
        [vF; vT]; [vf1; vT]; [vf; vT]; [vf2; vT];
        [vF; vt1]; [vf1; vt1]; [vf; vt1]; [vf2; vt1];
        [vF; vt]; [vf1; vt]; [vf; vt]; [vf2; vt];
        [vF; vt2]; [vf1; vt2]; [vf; vt2]; [vf2; vt2]
    ]);
    (vf2, [[vT]; [vt1]; [vt]; [vt2]]);
    (vF, [[vF]; [vf1]; [vf]; [vf2]])
  ].

Definition arrowsKB :=
  [
    (vT; [[vT]; [vt]]);
    (vt,
      [
        [vf; vT]; [vf2; vT];
        [vf; vt]; [vf2; vt]
    ]);
    (vt2, [[vf]; [vf2]]);
    (vf,
      [
        [vF; vt]; [vf; vt];
        [vF; vt2]; [vf; vt2]
    ]);
    (vf2, [[vt]; [vt2]]);
    (vF, [[vF]; [vf]])
  ].

Definition arrowsK4 :=
  [
    (vT; [[vT]; [vt1]]);
    (vt,
      [
        [vF; vT]; [vf1; vT]; [vf; vT]; [vf2; vT];
        [vF; vt1]; [vf1; vt1]; [vf; vt1]; [vf2; vt1];
        [vF; vt]; [vf1; vt]; [vf; vt]; [vf2; vt];
        [vF; vt2]; [vf1; vt2]; [vf; vt2]; [vf2; vt2]
    ]);
    (vt2, [[vF]; [vf1]]);
    (vf,
      [
        [vF; vT]; [vf1; vT]; [vf; vT]; [vf2; vT];
        [vF; vt1]; [vf1; vt1]; [vf; vt1]; [vf2; vt1];
        [vF; vt]; [vf1; vt]; [vf; vt]; [vf2; vt];
        [vF; vt2]; [vf1; vt2]; [vf; vt2]; [vf2; vt2]
    ]);
    (vf2, [[vT]; [vt1]]);
    (vF, [[vF]; [vf1]])
  ].

Definition arrowsK5 :=
  [
    (vT; [[vT]; [vt]]);
    (vt,
      [
        [vf; vt]
    ]);
    (vt2, [[vF]; [vf]]);
    (vf,
      [
        [vf; vt]
    ]);
    (vf2, [[vT]; [vt]]);
    (vF, [[vF]; [vf]])
  ].

Definition arrowsK45 :=
  [
    (vT; [[vT]]);
    (vt,
      [
        [vf; vt]
    ]);
    (vt2, [[vF]]);
    (vf,
      [
        [vf; vt]
    ]);
    (vf2, [[vT]]);
    (vF, [[vF]])
  ].

Definition arrowsKB45 :=
  [
    (vT; [[vT]]);
    (vt,
      [
        [vf; vt]
    ]);
    (vf,
      [
        [vf; vt]
    ]);
    (vF, [[vF]])
  ].

Definition arrowsKD :=
  [
    (vT; [[vT]; [vt]; [vt2]]);
    (vt,
      [
        [vF; vT]; [vf; vT]; [vf2; vT];
        [vF; vt]; [vf; vt]; [vf2; vt];
        [vF; vt2]; [vf; vt2]; [vf2; vt2]
    ]);
    (vt2, [[vF]; [vf]; [vf2]]);
    (vf,
      [
        [vF; vT]; [vf; vT]; [vf2; vT];
        [vF; vt]; [vf; vt]; [vf2; vt];
        [vF; vt2]; [vf; vt2]; [vf2; vt2]
    ]);
    (vf2, [[vT]; [vt]; [vt2]]);
    (vF, [[vF]; [vf]; [vf2]])
  ].

Definition arrowsKDB := arrowsKB.

Definition arrowsKD4 :=
  [
    (vT; [[vT]]);
    (vt,
      [
        [vF; vT]; [vf; vT]; [vf2; vT];
        [vF; vt]; [vf; vt]; [vf2; vt];
        [vF; vt2]; [vf; vt2]; [vf2; vt2]
    ]);
    (vt2, [[vF]]);
    (vf,
      [
        [vF; vT]; [vf; vT]; [vf2; vT];
        [vF; vt]; [vf; vt]; [vf2; vt];
        [vF; vt2]; [vf; vt2]; [vf2; vt2]
    ]);
    (vf2, [[vT]]);
    (vF, [[vF]])
  ].

Definition arrowsKD5 := arrowsK5.
  
Definition arrowsKD45 := arrowsK45.

Definition arrowsKT :=
  [
    (vt, [[vF]; [vf]]);
    (vf, [[vT]; [vt]])
  ].

Definition arrowsKT4 := arrowsKT.

Definition arrowsKTB :=
  [
    (vt, [[vf]]);
    (vf, [[vt]])
  ].

Definition arrowsKT45 := arrowsKTB.

Definition N := [vT; vt1; vf2; vf1].
Definition I := [vF; vf1; vt2; vt1].
Definition PA := [vT; vt; vf2; vf].
Definition PNA := [vF; vf; vt; vt2].

(* Tranformations *)
Definition toD (A : LF) := Some (A, D).
Definition toND (A : LF) := Some (A, F).
Definition posNA (A : LF) := Some (A, PNA).
Definition posA (A : LF) := Some (A, PA).
Definition necN (A : LF) := Some (A, N).
Definition necI (A : LF) := Some (A, I).

(* 'axD' é uma autorule; aplicada sobre o próprio v *)
Definition axD :=
  [
    (vT, [posA]);
    (vt1, [posA; posNA]);
    (vt2, [posNA]);
    (vf1, [posA; posNA]);
    (vf2, [posA]);
    (vF, [posNA])
  ].

(* 'axT' é uma autorule; aplicada sobre o próprio v *)
Definition axT :=
  [
    (vT, [toD]);
    (vt1, [toD; toND]);
    (vt2, [toND]);
    (vf1, [toND; toD]);
    (vf2, [toD]);
    (vF, [toND])
  ].

Definition boxRule :=
  [
    (vT, [toD]);
    (vt1, [toD; toND]);
    (vt2, [toND]);
    (vf1, [toD; toND]);
    (vf2, [toD]);
    (vF, [toND])
  ].

Definition ax4 :=
  [
    (vT, [necN]);
    (vt1, [necN; necI]);
    (vt2, [necI]);
    (vf1, [necN; necI]);
    (vf2, [necN]);
    (vF, [necI])
  ].

Definition axB :=
  [
    (vT, [posA]);
    (vt1, [posA]);
    (vt, [posA]);
    (vt2, [posA]);
    (vf1, [posNA]);
    (vf, [posNA]);
    (vf2, [posNA]);
    (vF, [posNA])
  ].

Definition ax5 :=
  [
    (vT, [posA]);
    (vt, [posA; posNA]);
    (vt2, [posNA]);
    (vf, [posA; posNA]);   
    (vf2, [posA]);
    (vF, [posNA])
  ].
      
Definition truleK :=
  (joinRules [boxRule] false V).

Definition truleKB :=
  (joinRules [boxRule; axB] false V).

Definition truleK4 :=
  (joinRules [boxRule; ax4] false V).

Definition truleK5 :=
  (joinRules [boxRule; ax5] false V).

Definition truleK45 :=
  (joinRules [boxRule; ax4; ax5] false V)
    ++(joinRules [axD] true V).

Definition truleKB45 :=
  (joinRules [boxRule; axB; ax4; ax5] false V).

Definition truleKD :=
  (joinRules [boxRule] false V)
    ++(joinRules [axD] true V).

Definition truleKDB :=
  (joinRules [boxRule; axB] false V)
    ++(joinRules [axD] true V).

Definition truleKD4 :=
  (joinRules [boxRule; ax4] false V)
    ++(joinRules [axD] true V).

Definition truleKD5 :=
  (joinRules [boxRule; ax5] false V)
    ++(joinRules [axD] true V).

Definition truleKD45 :=
  (joinRules [boxRule; ax4; ax5] false V)
    ++(joinRules [axD] true V).

Definition truleKT :=
  (joinRules [boxRule] false V)
    ++(joinRules [axT] true V).

Definition truleKTB :=
  (joinRules [boxRule; axB] false V)
    ++(joinRules [axT] true V).

Definition truleKT4 :=
  (joinRules [boxRule; ax4] false V)
    ++(joinRules [axT] true V).

Definition truleKT45 :=
  (joinRules [boxRule; ax4; ax5] false V)
    ++(joinRules [axT] true V).

Require Coq.extraction.Extraction.

Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Check truleK.

Recursive Extraction
  arrowsKT arrowsKTB arrowsKT4 arrowsKT45
  arrowsKD arrowsKDB arrowsKD4 arrowsKD5 arrowsKD45
  arrowsK arrowsKB arrowsK4 arrowsK5 arrowsK45 arrowsKB45
  truleK
  truleKB
  truleK4
  truleK5
  truleK45
  truleKB45
  truleKD
  truleKDB
  truleKD4
  truleKD5
  truleKD45
  truleKT
  truleKTB
  truleKT4
  truleKT45
.
