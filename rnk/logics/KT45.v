(**

    KT45 (S5)

 ***)

Require Import Forest.
Require Import List.
Require Import String.
Require Import Arith.
Require Import rnk.
Require Import Model.
Require Import Language.
Require Import RelCond.
Import ListNotations.

(* Truth-table definitions *)

Definition V := [vF; vf; vt; vT].
Definition D := [vt; vT].
Definition F := [vf; vF].

Definition neg_def :=
  [
    (vF, [vT]);
    (vf, [vt]);
    (vt, [vf]);
    (vT, [vF])
  ].
 
Definition box_def :=
  [
    (vF, [vF]);
    (vf, [vF]);
    (vt, [vF]);
    (vT, [vT])
  ].
Definition dia_def :=
  [
    (vF, [vF]);
    (vf, [vT]);
    (vt, [vT]);
    (vT, [vT])
  ].

Definition impl_def :=
  [
    ((vF; vF); [vT]);
    ((vF; vf); [vT]);
    ((vF; vt); [vT]);
    ((vF; vT); [vT]);
    ((vf; vF); [vt]);
    ((vf; vf); [vT; vt]);
    ((vf; vt); [vT; vt]);
    ((vf; vT); [vT]);
    ((vt; vF); [vf]);
    ((vt; vf); [vf]);
    ((vt; vt); [vT; vt]);
    ((vt; vT); [vT]);
    ((vT; vF); [vF]);
    ((vT; vf); [vf]);
    ((vT; vt); [vt]);
    ((vT; vT); [vT])
  ].

Definition conj_def :=
  [
    ((vF; vF); [vF]);
    ((vF; vf); [vF]);
    ((vF; vt); [vF]);
    ((vF; vT); [vF]);
    ((vf; vF); [vF]);
    ((vf; vf); [vF; vf]);
    ((vf; vt); [vF]);
    ((vf; vT); [vf]);
    ((vt; vF); [vF]);
    ((vt; vf); [vF]);
    ((vt; vt); [vt]);
    ((vt; vT); [vt]);
    ((vT; vF); [vF]);
    ((vT; vf); [vf]);
    ((vT; vt); [vt]);
    ((vT; vT); [vT])
  ].

Definition disj_def :=
  [
    ((vF; vF); [vF]);
    ((vF; vf); [vf]);
    ((vF; vt); [vt]);
    ((vF; vT); [vT]);
    ((vf; vF); [vf]);
    ((vf; vf); [vf]);
    ((vf; vt); [vT; vt]);
    ((vf; vT); [vT]);
    ((vt; vF); [vt]);
    ((vt; vf); [vT; vt]);
    ((vt; vt); [vT; vt]);
    ((vt; vT); [vT]);
    ((vT; vF); [vT]);
    ((vT; vf); [vT]);
    ((vT; vt); [vT]);
    ((vT; vT); [vT])
  ].

(** Nmatrix **)

Definition Nmatrix
  (B A : LF)
  (partialV : btree LF)
  (V : list nat)
  (allVs : list (btree LF))
  : btree LF
  :=
  match A with
  | Atom B => Leaf _ true
  | ~ B =>
      unary_op A B partialV 0 neg_def eqb_lf
  | [] B =>
      unary_op A B partialV 0 box_def eqb_lf
  | <> B =>
      unary_op A B partialV 0 dia_def eqb_lf
  | B --> C =>
      bin_op A B C partialV 0 0 impl_def eqb_lf
  | B \/ C =>
      bin_op A B C partialV 0 0 disj_def eqb_lf
  | B /\ C =>
      bin_op A B C partialV 0 0 conj_def eqb_lf
  end.

(***)

Definition makeMatrix (A : LF) :=
  makeIt
    A
    V
    Nmatrix
    eqb_lf
    leb_lf
    length_lf
    split_lf.

Definition makeRestrictionSteps
  (A : LF) :=
  restrictionSteps
    A
    (makeMatrix A)
    eqb_lf
    leb_lf
    geb_lf
    split_lf
    arrows
    8
    truleKT45
.

Definition makeComputeTable
  (A : LF) :=
  let steps := makeRestrictionSteps A in
  computeTable steps.


(*************************************)

(* 

   Testes
 
*)

(*************************************)

Definition P := Atom "p0".
Definition Q := Atom "p1".
Definition U := Atom "p3".

Definition AK := (([] (P --> Q)) --> (([] P) --> [] Q)).
Definition AB := P --> [] (<> P).
Definition AT := [] P --> P.
Definition A4 := []P --> [][]P.
Definition AD := []P --> <> P.
Definition A5 := <> P --> []<> P.

Definition k1 := ([](P  --> Q)) --> ((<> P) --> <> Q).
Definition k2 := (<> (P \/ Q)) --> ((<> P) \/ <> Q).
Definition k3 := ((<> P) --> [] Q) --> [] (P --> Q).
Definition k4 := (~ <> (P /\ ~ P)).

Compute makeComputeTable ([] k1).

Compute makeComputeTable AB.

Require Import Model.

Definition makeArrangeKM
  (A : LF)
  (smallest lazymode : bool)
  :=
  arrangeKM
    A
    (makeMatrix A)
    eqb_lf
    leb_lf
    geb_lf
    split_lf
    arrows
    8
    smallest lazymode truleKT45
.

Definition makeThisRn
  (w : nat)
  (A : LF)
  (smallest lazymode : bool)
  :=
  rnkripke
    A
    (makeMatrix A)
    eqb_lf
    leb_lf
    geb_lf
    length_lf
    split_lf
    arrows
    8
    D
    [Reflexive; Symmetry]
    smallest lazymode truleKT45
.

Definition makeAllRn
  (A : LF)
  (smallest lazymode : bool)
  :=
  rnkripke
    A
    (makeMatrix A)
    eqb_lf
    leb_lf
    geb_lf
    length_lf
    split_lf
    arrows
    8
    D
    [Reflexive; Symmetry]
    smallest lazymode truleKT45
.

(* Val : X -> list (node X) -> nat -> bool *)
Fixpoint Val
  (A : LF)
  (model : list (node LF))
  (w : nat) :=
  let accW := getAllAccessedWorld model w in
  match A with
  | ! _ => checkValInW A w model eqb_lf
  | ~ p => negb (Val p model w)
  | [] p =>
      forallb (
          map
            (fun k =>
               (Val p model k))
            accW
        )
  | <> p =>
      existb (
          map
            (fun k =>
               (Val p model k))
            accW
        )
  | p --> q =>
      orb (Val q model w) (negb (Val p model w))
  | p \/ q =>
      orb (Val q model w) (Val p model w)
  | p /\ q =>
      andb (Val q model w) (Val p model w)
  end.

Definition makeCheckAllModels
  (A : LF)
  (smallest lazymode : bool)
  :=
  checkAllModels
    A
    (makeMatrix A)
    eqb_lf leb_lf geb_lf
    split_lf
    arrows
    Val
    8
    (makeAllRn A smallest lazymode)
    D
    truleKT45
.

Require Coq.extraction.Extraction.

Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction
  makeCheckAllModels makeComputeTable makeThisRn.
