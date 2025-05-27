(**

     K45

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

Arguments Pair {X} {Y}.

Notation "( A ; B )" := (Pair A B).


(* Truth-table definitions *)

Definition V := [vF; vf; vf1; vf2; vt2; vt1; vt; vT].
Definition D := [vt; vt1; vt2; vT].
Definition F := [vf; vf1; vf2; vF].

Definition deadend := vT+1.

Definition neg_def :=
  [
    (vF, [vT]);
    (vf, [vt]);
    (vf1, [vt1]);
    (vf2, [vt2]);
    (vt2, [vf2]);
    (vt1, [vf1]);
    (vt, [vf]);
    (vT, [vF])
  ].

Definition box_def :=
  [
    (vF, [vF]);
    (vf, [vF]);
    (vf1, [vt1]);
    (vf2, [vT]);
    (vt2, [vF]);
    (vt1, [vt1]);
    (vt, [vF]);
    (vT, [vT])
  ].

Definition dia_def :=
  [
    (vF, [vF]);
    (vf, [vT]);
    (vf1, [vf1]);
    (vf2, [vT]);
    (vt2, [vF]);
    (vt1, [vf1]);
    (vt, [vT]);
    (vT, [vT])
  ].

Definition impl_def :=
  [
    ((vF; vF); [vT]);
    ((vF; vf); [vT]);
    ((vF; vf2); [vT]);
    ((vF; vt2); [vT]);
    ((vF; vt); [vT]);
    ((vF; vT); [vT]);
    ((vf; vF); [vt]);
    ((vf; vf); [vT; vt]);
    ((vf; vf2); [vT]);
    ((vf; vt2); [vt]);
    ((vf; vt); [vT; vt]);
    ((vf; vT); [vT]);
    ((vf2; vF); [vt2]);
    ((vf2; vf); [vt]);
    ((vf2; vf2); [vT]);
    ((vf2; vt2); [vt2]);
    ((vf2; vt); [vt]);
    ((vf2; vT); [vT]);
    ((vt2; vF); [vf2]);
    ((vt2; vf); [vf2]);
    ((vt2; vf2); [vf2]);
    ((vt2; vt2); [vT]);
    ((vt2; vt); [vT]);
    ((vt2; vT); [vT]);
    ((vt; vF); [vf]);
    ((vt; vf); [vf; vf2]);
    ((vt; vf2); [vf2]);
    ((vt; vt2); [vt]);
    ((vt; vt); [vT; vt]);
    ((vt; vT); [vT]);
    ((vT; vF); [vF]);
    ((vT; vf); [vf]);
    ((vT; vf2); [vf2]);
    ((vT; vt2); [vt2]);
    ((vT; vt); [vt]);
    ((vT; vT); [vT]);
    
    (* t1, v1 cases *)

    ((vf1; vf1); [vt1]);
    ((vf1; vt1); [vt1]);
    ((vt1; vf1); [vf1]);
    ((vt1; vt1); [vt1]);

    (* invalid cases in level0 *)

    ((vF; vf1); [deadend]);
    ((vF; vt1); [deadend]);
    ((vf1; vF); [deadend]);
    ((vt1; vF); [deadend]);
    ((vf; vf1); [deadend]);
    ((vf; vt1); [deadend]);
    ((vf1; vf); [deadend]);
    ((vt1; vf); [deadend]);
    ((vf2; vf1); [deadend]);
    ((vf2; vt1); [deadend]);
    ((vf1; vf2); [deadend]);
    ((vt1; vf2); [deadend]);
    ((vt2; vf1); [deadend]);
    ((vt2; vt1); [deadend]);
    ((vf1; vt2); [deadend]);
    ((vt1; vt2); [deadend]);
    ((vt; vf1); [deadend]);
    ((vt; vt1); [deadend]);
    ((vf1; vt); [deadend]);
    ((vt1; vt); [deadend]);
    ((vT; vf1); [deadend]);
    ((vT; vt1); [deadend]);
    ((vf1; vT); [deadend]);
    ((vt1; vT); [deadend])
  ].


Definition conj_def :=
  [
    ((vF; vF); [vF]);
    ((vF; vf); [vF]);
    ((vF; vf2); [vF]);
    ((vF; vt2); [vF]);
    ((vF; vt); [vF]);
    ((vF; vT); [vF]);
    ((vf; vF); [vF]);
    ((vf; vf); [vF; vf]);
    ((vf; vf2); [vf]);
    ((vf; vt2); [vF]);
    ((vf; vt); [vF]);
    ((vf; vT); [vf]);
    ((vf2; vF); [vF]);
    ((vf2; vf); [vf]);
    ((vf2; vf2); [vf2]);
    ((vf2; vt2); [vF]);
    ((vf2; vt); [vf]);
    ((vf2; vT); [vf2]);
    ((vt2; vF); [vF]);
    ((vt2; vf); [vF]);
    ((vt2; vf2); [vF]);
    ((vt2; vt2); [vt2]);
    ((vt2; vt); [vt2]);
    ((vt2; vT); [vt2]);
    ((vt; vF); [vF]);
    ((vt; vf); [vF]);
    ((vt; vf2); [vf]);
    ((vt; vt2); [vt2]);
    ((vt; vt); [vt; vt2]);
    ((vt; vT); [vt]);
    ((vT; vF); [vF]);
    ((vT; vf); [vf]);
    ((vT; vf2); [vf2]);
    ((vT; vt2); [vt2]);
    ((vT; vt); [vt]);
    ((vT; vT); [vT]);

    (* t1, v1 cases *)

    ((vf1; vf1); [vf1]);
    ((vf1; vt1); [vf1]);
    ((vt1; vf1); [vf1]);
    ((vt1; vt1); [vt1]);

    (* invalid cases in level0 *)

    ((vF; vf1); [deadend]);
    ((vF; vt1); [deadend]);
    ((vf1; vF); [deadend]);
    ((vt1; vF); [deadend]);
    ((vf; vf1); [deadend]);
    ((vf; vt1); [deadend]);
    ((vf1; vf); [deadend]);
    ((vt1; vf); [deadend]);
    ((vf2; vf1); [deadend]);
    ((vf2; vt1); [deadend]);
    ((vf1; vf2); [deadend]);
    ((vt1; vf2); [deadend]);
    ((vt2; vf1); [deadend]);
    ((vt2; vt1); [deadend]);
    ((vf1; vt2); [deadend]);
    ((vt1; vt2); [deadend]);
    ((vt; vf1); [deadend]);
    ((vt; vt1); [deadend]);
    ((vf1; vt); [deadend]);
    ((vt1; vt); [deadend]);
    ((vT; vf1); [deadend]);
    ((vT; vt1); [deadend]);
    ((vf1; vT); [deadend]);
    ((vt1; vT); [deadend])
    
  ].

Definition disj_def :=
  [
    ((vF; vF); [vF]);
    ((vF; vf); [vf]);
    ((vF; vf2); [vf2]);
    ((vF; vt2); [vt2]);
    ((vF; vt); [vt]);
    ((vF; vT); [vT]);
    ((vf; vF); [vf]);
    ((vf; vf); [vf; vf2]);
    ((vf; vf2); [vf2]);
    ((vf; vt2); [vt]);
    ((vf; vt); [vT; vt]);
    ((vf; vT); [vT]);
    ((vf2; vF); [vf2]);
    ((vf2; vf); [vf2]);
    ((vf2; vf2); [vf2]);
    ((vf2; vt2); [vT]);
    ((vf2; vt); [vT]);
    ((vf2; vT); [vT]);
    ((vt2; vF); [vt2]);
    ((vt2; vf); [vt]);
    ((vt2; vf2); [vT]);
    ((vt2; vt2); [vt2]);
    ((vt2; vt); [vt]);
    ((vt2; vT); [vT]);
    ((vt; vF); [vt]);
    ((vt; vf); [vT; vt]);
    ((vt; vf2); [vT]);
    ((vt; vt2); [vt]);
    ((vt; vt); [vT; vt]);
    ((vt; vT); [vT]);
    ((vT; vF); [vT]);
    ((vT; vf); [vT]);
    ((vT; vf2); [vT]);
    ((vT; vt2); [vT]);
    ((vT; vt); [vT]);
    ((vT; vT); [vT]);

    (* t1, v1 cases *)
    
    ((vf1; vf1); [vf1]);
    ((vf1; vt1); [vt1]);
    ((vt1; vf1); [vt1]);
    ((vt1; vt1); [vt1]);

    (* invalid cases in level0 *)

    ((vF; vf1); [deadend]);
    ((vF; vt1); [deadend]);
    ((vf1; vF); [deadend]);
    ((vt1; vF); [deadend]);
    ((vf; vf1); [deadend]);
    ((vf; vt1); [deadend]);
    ((vf1; vf); [deadend]);
    ((vt1; vf); [deadend]);
    ((vf2; vf1); [deadend]);
    ((vf2; vt1); [deadend]);
    ((vf1; vf2); [deadend]);
    ((vt1; vf2); [deadend]);
    ((vt2; vf1); [deadend]);
    ((vt2; vt1); [deadend]);
    ((vf1; vt2); [deadend]);
    ((vt1; vt2); [deadend]);
    ((vt; vf1); [deadend]);
    ((vt; vt1); [deadend]);
    ((vf1; vt); [deadend]);
    ((vt1; vt); [deadend]);
    ((vT; vf1); [deadend]);
    ((vT; vt1); [deadend]);
    ((vf1; vT); [deadend]);
    ((vt1; vT); [deadend])
    
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

Check filter.

Check isEmpty.

Fixpoint f1t1filter (matrix : list (list (Forest.node LF))) :=
  match matrix with
  | nil => nil
  | row::tl =>
      let f := filter
                 (fun node =>
                    match node with
                    | Forest.Node _ vA A =>
                        Nat.eqb vA deadend
                    end
                 ) row in
      if isEmpty f then row::(f1t1filter tl)
      else
        f1t1filter tl
  end.

Definition makeMatrix (A : LF) :=
  f1t1filter
    (makeIt
       A
       V
       Nmatrix
       eqb_lf
       leb_lf
       length_lf
       split_lf).

Definition makeRestrictionSteps
  (A : LF) :=
  restrictionSteps
    A
    (makeMatrix A)
    eqb_lf
    leb_lf
    geb_lf
    split_lf
    arrowsK45
    8
    truleK45
.

Definition makeComputeTable
  (A : LF) :=
  let steps := makeRestrictionSteps A in
  computeTable steps.

Fixpoint makeLevel0_aux1 (row : list (Forest.node LF)) :=
  match row with
  | nil => nil
  | (Forest.Node _ _ A)::tl => A::(makeLevel0_aux1 tl)
  end.

Fixpoint makeLevel0_aux (initLabel: nat) (table : list (list nat)) :=
  match table with
  | nil => nil
  | row::tl =>
      (initLabel; row)::(makeLevel0_aux (initLabel+1) tl)
  end.

Definition makeLevel0
  (A : LF) :=
  let table := reverseThisList (makeMatrix A) in
  let subA := makeLevel0_aux1 (pop table nil) in
  let level0 := nodeToNat table in
  (subA; makeLevel0_aux 1 level0).


(*************************************)

(* 

   Testes
 
*)

(*************************************)

Definition P := Atom "p0".
Definition Q := Atom "p1".
Definition U := Atom "p3".

Definition AK45 := (([] (P --> Q)) --> (([] P) --> [] Q)).
Definition AB := P --> [] (<> P).
Definition AT := [] P --> P.
Definition A4 := []P --> [][]P.
Definition AD := []P --> <> P.
Definition A5 := (<> P) --> []<> P.

Definition k1 := ([](P  --> Q)) --> ((<> P) --> <> Q).
Definition k2 := (<> (P \/ Q)) --> ((<> P) \/ <> Q).
Definition k3 := ((<> P) --> [] Q) --> [] (P --> Q).
Definition k4 := (~ <> (P /\ ~ P)).

Compute makeLevel0 A5.

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
    arrowsK45
    8
    smallest lazymode truleK45
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
    arrowsK45
    8
    D
    [Transitive] (* TODO: Euclidianity *)
    smallest lazymode truleK45
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
    arrowsK45
    8
    D
    [Transitive] (* TODO: Euclidianity *)
    smallest lazymode truleK45
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
    arrowsK45
    Val
    8
    (makeAllRn A smallest lazymode)
    D
    truleK45
.

Require Coq.extraction.Extraction.

Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction
  makeCheckAllModels makeComputeTable makeThisRn makeLevel0.





