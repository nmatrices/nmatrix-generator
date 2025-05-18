(**

    This file is an implementation of the modal cube using RNmatrices.

 ***)

Require Import Forest.
Require Import List.
Require Import String.
Require Import Arith.
Require Import rnk.
Require Import Model.
Import ListNotations.

Arguments Pair {X} {Y}.

Notation "( A ; B )" := (Pair A B).

(** Language specifics **)

Inductive LF :=
| Atom : string -> LF
| Neg : LF -> LF
| Box : LF -> LF
| Dia : LF -> LF
| Impl : LF -> LF -> LF
| Conj : LF -> LF -> LF
| Disj : LF -> LF -> LF.

Notation "! A" := (Atom A) (at level 10).
Notation "~ A" := (Neg A).
Notation "[] A" := (Box A) (at level 80).
Notation "<> A" := (Dia A) (at level 80).
Notation "A ~> B" := (Impl A B) (at level 90).
Notation "A /\ B" := (Conj A B).
Notation "A \/ B" := (Disj A B).

Fixpoint eqb_lf (A : LF) (B : LF) :=
  match A with
  | Atom P => match B with
              | Atom Q => if (String.eqb P Q) then true
                          else false
              | _ => false
              end
  | ~ P => match B with
           | ~ Q => eqb_lf P Q
           | _ => false
           end
  | [] P => match B with
           | [] Q => eqb_lf P Q
           | _ => false
            end
  | <> P => match B with
            | <> Q => eqb_lf P Q
            | _ => false
            end
  | P ~> Q => match B with
              | R ~> T => andb (eqb_lf P R) (eqb_lf Q T)
              | _ => false
              end
  | P /\ Q => match B with
              | R /\ T => andb (eqb_lf P R) (eqb_lf Q T)
              | _ => false
              end
  | P \/ Q => match B with
              | R \/ T => andb (eqb_lf P R) (eqb_lf Q T)
              | _ => false
              end
  end.

Fixpoint length_lf (A : LF) :=
  match A with
  | Atom P => 0
  | ~ P => 1 + length_lf P
  | [] P => 1 + length_lf P
  | <> P => 1 + length_lf P
  | P ~> Q => 1 + length_lf P + length_lf Q
  | P /\ Q => 1 + length_lf P + length_lf Q
  | P \/ Q => 1 + length_lf P + length_lf Q
  end.

Definition leb_lf (A : LF) (B : LF) :=
  Nat.leb (length_lf A) (length_lf B).

Definition geb_lf (A : LF) (B : LF) :=
  negb (leb (length_lf A) (length_lf B)).

Fixpoint split_lf (L : LF) :=
  match L with
  | Atom A => (Atom A)::nil
  | ~ A => (~ A)::(split_lf A)
  | [] A => ([] A)::(split_lf A)
  | <> A => (<> A)::(split_lf A)
  | A ~> B => (A ~> B)::((split_lf A)++(split_lf B))
  | A /\ B => (A /\ B)::((split_lf A)++(split_lf B))
  | A \/ B => (A \/ B)::((split_lf A)++(split_lf B))
  end.

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

(* Truth-table definitions *)

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
 
(*
Definition neg_def :=
  [
    (vF, D);
    (vf, D);
    (vf1, D);
    (vf2, D);
    (vt2, F);
    (vt1, F);
    (vt, F);
    (vT, F)
  ].*)

Definition box_def :=
  [
    (vF, F);
    (vf, F);
    (vf1, D);
    (vf2, D);
    (vt2, F);
    (vt1, D);
    (vt, F);
    (vT, D)
  ].
Definition dia_def :=
  [
    (vF, F);
    (vf, D);
    (vf1, F);
    (vf2, D);
    (vt2, F);    
    (vt1, F);
    (vt, D);
    (vT, D)
  ].

Definition impl_def :=
  [
    ((vF; vF); [vT]);
    ((vF; vf1); [vT]);
    ((vF; vf); [vT]);
    ((vF; vf2); [vT]);
    ((vF; vt1); [vT]);
    ((vF; vt); [vT]);
    ((vF; vt2); [vT]);
    ((vF; vT); [vT]);
    ((vf1; vF); [vt2]);
    ((vf1; vf1); [vt1]);
    ((vf1; vf); [vt]);
    ((vf1; vf2); [vT]);
    ((vf1; vt1); [vt1]);
    ((vf1; vt); [vt]);
    ((vf1; vt2); [vt2]);
    ((vf1; vT); [vT]);
    ((vf; vF); [vt]);
    ((vf; vf1); [vT]);
    ((vf; vf); [vT; vt]);
    ((vf; vf2); [vT]);
    ((vf; vt1); [vT]);
    ((vf; vt); [vT; vt]);
    ((vf; vt2); [vt]);
    ((vf; vT); [vT]);
    ((vf2; vF); [vt2]);
    ((vf2; vf1); [vt1]);
    ((vf2; vf); [vt]);
    ((vf2; vf2); [vT]);
    ((vf2; vt1); [vt1]);
    ((vf2; vt); [vt]);
    ((vf2; vt2); [vt2]);
    ((vf2; vT); [vT]);
    ((vt1; vF); [vF]);
    ((vt1; vf1); [vf1]);
    ((vt1; vf); [vf]);
    ((vt1; vf2); [vf2]);
    ((vt1; vt1); [vt1]);
    ((vt1; vt); [vt]);
    ((vt1; vt2); [vt2]);
    ((vt1; vT); [vT]);
    ((vt; vF); [vf]);
    ((vt; vf1); [vf2]);
    ((vt; vf); [vf2; vf]);
    ((vt; vf2); [vf2]);
    ((vt; vt1); [vT]);
    ((vt; vt); [vT; vt]);
    ((vt; vt2); [vt]);
    ((vt; vT); [vT]);
    ((vt2; vF); [vf2]);
    ((vt2; vf1); [vf2]);
    ((vt2; vf); [vf2]);
    ((vt2; vf2); [vf2]);
    ((vt2; vt1); [vT]);
    ((vt2; vt); [vT]);
    ((vt2; vt2); [vT]);
    ((vt2; vT); [vT]);
    ((vT; vF); [vF]);
    ((vT; vf1); [vf1]);
    ((vT; vf); [vf]);
    ((vT; vf2); [vf2]);
    ((vT; vt1); [vt1]);
    ((vT; vt); [vt]);
    ((vT; vt2); [vt2]);
    ((vT; vT); [vT])
  ].

  (*
  [
    ((vF; vF); D);
    ((vF; vf1); D);
    ((vF; vf); D);
    ((vF; vf2); D);
    ((vF; vt1); D);
    ((vF; vt); D);
    ((vF; vt2); D);
    ((vF; vT); D);
    ((vf1; vF); D);
    ((vf1; vf1); D);
    ((vf1; vf); D);
    ((vf1; vf2); D);
    ((vf1; vt1); D);
    ((vf1; vt); D);
    ((vf1; vt2); D);
    ((vf1; vT); D);
    ((vf; vF); D);
    ((vf; vf1); D);
    ((vf; vf); D);
    ((vf; vf2); D);
    ((vf; vt1); D);
    ((vf; vt); D);
    ((vf; vt2); D);
    ((vf; vT); D);
    ((vf2; vF); D);
    ((vf2; vf1); D);
    ((vf2; vf); D);
    ((vf2; vf2); D);
    ((vf2; vt1); D);
    ((vf2; vt); D);
    ((vf2; vt2); D);
    ((vf2; vT); D);
    ((vt1; vF); F);
    ((vt1; vf1); F);
    ((vt1; vf); F);
    ((vt1; vf2); F);
    ((vt1; vt1); D);
    ((vt1; vt); D);
    ((vt1; vt2); D);
    ((vt1; vT); D);
    ((vt; vF); F);
    ((vt; vf1); F);
    ((vt; vf); F);
    ((vt; vf2); F);
    ((vt; vt1); D);
    ((vt; vt); D);
    ((vt; vt2); D);
    ((vt; vT); D);
    ((vt2; vF); F);
    ((vt2; vf1); F);
    ((vt2; vf); F);
    ((vt2; vf2); F);
    ((vt2; vt1); D);
    ((vt2; vt); D);
    ((vt2; vt2); D);
    ((vt2; vT); D);
    ((vT; vF); F);
    ((vT; vf1); F);
    ((vT; vf); F);
    ((vT; vf2); F);
    ((vT; vt1); D);
    ((vT; vt); D);
    ((vT; vt2); D);
    ((vT; vT); D)
  ].*)

Definition conj_def :=
  [
    ((vF; vF); F);
    ((vF; vf1); F);
    ((vF; vf); F);
    ((vF; vf2); F);
    ((vF; vt1); F);
    ((vF; vt); F);
    ((vF; vt2); F);
    ((vF; vT); F);
    ((vf1; vF); F);
    ((vf1; vf1); F);
    ((vf1; vf); F);
    ((vf1; vf2); F);
    ((vf1; vt1); F);
    ((vf1; vt); F);
    ((vf1; vt2); F);
    ((vf1; vT); F);
    ((vf; vF); F);
    ((vf; vf1); F);
    ((vf; vf); F);
    ((vf; vf2); F);
    ((vf; vt1); F);
    ((vf; vt); F);
    ((vf; vt2); F);
    ((vf; vT); F);
    ((vf2; vF); F);
    ((vf2; vf1); F);
    ((vf2; vf); F);
    ((vf2; vf2); F);
    ((vf2; vt1); F);
    ((vf2; vt); F);
    ((vf2; vt2); F);
    ((vf2; vT); F);
    ((vt1; vF); F);
    ((vt1; vf1); F);
    ((vt1; vf); F);
    ((vt1; vf2); F);
    ((vt1; vt1); D);
    ((vt1; vt); D);
    ((vt1; vt2); D);
    ((vt1; vT); D);
    ((vt; vF); F);
    ((vt; vf1); F);
    ((vt; vf); F);
    ((vt; vf2); F);
    ((vt; vt1); D);
    ((vt; vt); D);
    ((vt; vt2); D);
    ((vt; vT); D);
    ((vt2; vF); F);
    ((vt2; vf1); F);
    ((vt2; vf); F);
    ((vt2; vf2); F);
    ((vt2; vt1); D);
    ((vt2; vt); D);
    ((vt2; vt2); D);
    ((vt2; vT); D);
    ((vT; vF); F);
    ((vT; vf1); F);
    ((vT; vf); F);
    ((vT; vf2); F);
    ((vT; vt1); D);
    ((vT; vt); D);
    ((vT; vt2); D);
    ((vT; vT); D)
  ].

Definition disj_def :=
  [
    ((vF; vF); F);
    ((vF; vf1); F);
    ((vF; vf); F);
    ((vF; vf2); F);
    ((vF; vt1); D);
    ((vF; vt); D);
    ((vF; vt2); D);
    ((vF; vT); D);
    ((vf1; vF); F);
    ((vf1; vf1); F);
    ((vf1; vf); F);
    ((vf1; vf2); F);
    ((vf1; vt1); D);
    ((vf1; vt); D);
    ((vf1; vt2); D);
    ((vf1; vT); D);
    ((vf; vF); F);
    ((vf; vf1); F);
    ((vf; vf); F);
    ((vf; vf2); F);
    ((vf; vt1); D);
    ((vf; vt); D);
    ((vf; vt2); D);
    ((vf; vT); D);
    ((vf2; vF); F);
    ((vf2; vf1); F);
    ((vf2; vf); F);
    ((vf2; vf2); F);
    ((vf2; vt1); D);
    ((vf2; vt); D);
    ((vf2; vt2); D);
    ((vf2; vT); D);
    ((vt1; vF); D);
    ((vt1; vf1); D);
    ((vt1; vf); D);
    ((vt1; vf2); D);
    ((vt1; vt1); D);
    ((vt1; vt); D);
    ((vt1; vt2); D);
    ((vt1; vT); D);
    ((vt; vF); D);
    ((vt; vf1); D);
    ((vt; vf); D);
    ((vt; vf2); D);
    ((vt; vt1); D);
    ((vt; vt); D);
    ((vt; vt2); D);
    ((vt; vT); D);
    ((vt2; vF); D);
    ((vt2; vf1); D);
    ((vt2; vf); D);
    ((vt2; vf2); D);
    ((vt2; vt1); D);
    ((vt2; vt); D);
    ((vt2; vt2); D);
    ((vt2; vT); D);
    ((vT; vF); D);
    ((vT; vf1); D);
    ((vT; vf); D);
    ((vT; vf2); D);
    ((vT; vt1); D);
    ((vT; vt); D);
    ((vT; vt2); D);
    ((vT; vT); D)
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
  | B ~> C =>
      bin_op A B C partialV 0 0 impl_def eqb_lf
  | B \/ C =>
      bin_op A B C partialV 0 0 disj_def eqb_lf
  | B /\ C =>
      bin_op A B C partialV 0 0 conj_def eqb_lf
  end.



Definition arrows :=
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
 
(*
Definition arrows :=
  [
    (vt, [[vf]]);
    (vf, [[vt]])
  ].
*)

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
      
Definition trule :=
  (joinRules [boxRule; ax5] false V)
    ++(joinRules [axD] true V).

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
    404
    trule
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

(*Notation "<>s A" := (~ ([] (~ A))) (at level 90).*)
Notation "[]s A" := (~ (<> (~ A))) (at level 90).

Definition P := Atom "p0".
Definition Q := Atom "p1".
Definition U := Atom "p3".

Definition AK := (([] (P ~> Q)) ~> (([] P) ~> [] Q)).
Definition AB := P ~> [] (<> P).
Definition AT := [] P ~> P.
Definition A4 := []P ~> [][]P.
Definition AD := []P ~> <> P.
Definition A5 := <> P ~> []<> P.

(*
Compute reverseThisList (nodeToNat (makeMatrix (AK))).
 *)

Definition f2 (A : LF) := ((~A) /\ []A).
Definition t2 (A : LF) := ((A) /\ []~A).

Definition co1 (A : LF) := (f2(A) ~> t2(f2(A)))/\~t2(A).
Definition co2 (A : LF) := t2(A) ~> f2(A).
Definition co3 (A : LF) := (~t2(A)) /\ (f2(A) \/ ~f2(A)).


Compute makeComputeTable (<>P~><><>P).

Compute makeComputeTable ((<>~P) ~> []~[]P).

Compute makeComputeTable (([]P) ~> ~~[]P).


Compute co2 P.

Compute reverseThisList (nodeToNat (makeMatrix (co3 P))).

Compute makeComputeTable ((f2(P)) /\ ~t2(P)).

Compute makeComputeTable ((P /\ []P)/\<>P).

Compute makeComputeTable ((<>(P ~> Q) ~> ([] P ~> <> Q))).
(*Compute makeComputeTable ((<>(P ~> Q) ~> ([]<> P ~> <> Q))).*)
Compute makeComputeTable (((([] P ~> <> Q)) ~> <>(P ~> Q))).








Definition k3 := ((<> P) ~> [] Q) ~> [](P ~> Q).

Definition LK2 := (<>(P ~> Q)) ~> ([] P ~> <> Q).

Compute reverseThisList (nodeToNat (makeMatrix (LK2))).

Compute reverseThisList (nodeToNat (makeMatrix (P ~> P))).






















Compute makeComputeTable (AK).

Definition k1 := ([](P  ~> Q)) ~> ((<>s P) ~> <>s Q).
Definition k2 := (<>s (P \/ Q)) ~> ((<>s P) \/ <>s Q).
Definition k3 := ((<>s P) ~> [] Q) ~> [] (P ~> Q).
(* Definition k4 := (~ <> (P /\ ~ P)).*)

Compute makeComputeTable ([] k1).

Compute makeComputeTable AB.

(* Nessa lógica, valem AK, AD, AM e A4.*)

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
    404
    smallest lazymode trule
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
    404
    D
    [Reflexive]
    smallest lazymode trule
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
    404
    D
    [Reflexive]
    smallest lazymode trule
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
  | p ~> q =>
      orb (Val q model w) (negb (Val p model w))
  end.

Definition makeCheckAllModels
  (make : LF -> list (list (Forest.node LF)))
  (A : LF)
  (smallest lazymode : bool)
  :=
  checkAllModels
    A
    (make A)
    eqb_lf leb_lf geb_lf
    split_lf
    arrows
    Val
    3
    (makeAllRn make A smallest lazymode)
    [1;2]
    tKT
.

Require Coq.extraction.Extraction.

Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction
  makeCheckAllModels makeMakeIt makeComputeTable makeThisRn.

(*****

The following functions/definitions are required by the deep-first search method.

 ******)

Definition iscons
  (A B : pair LF nat)
  :=
  negb
    (orb
       (andb
          (orb
             (eqb_lf (proj_l A) (~ (proj_l B)))
             (eqb_lf (proj_l B) (~ (proj_l A))))
          (Nat.eqb (proj_r A) (proj_r B))
       )
       (andb
          (eqb_lf (proj_l A) (proj_l B))
          (negb (Nat.eqb (proj_r A) (proj_r B))))).

Definition logicbt
  (A : LF)
  (v : nat)
  (atomicMask : list nat)
  (modulo : list (pair LF nat))
  (V : list (pair LF nat))
  :=
  match A with
  | Atom p =>
      if isElementInList v atomicMask Nat.eqb then
        bleaf nil false
      else
        bleaf nil true
  | [] B =>
      let candidates := getCandidatesUn box_def v in
      if isEmpty candidates then bleaf nil false
      else
        genbun B candidates modulo V iscons
  | ~ B =>
      let candidates := getCandidatesUn neg_def v in
      if isEmpty candidates then bleaf nil false
      else
        genbun B candidates modulo V iscons
  | B ~> C =>
      let candidates := getCandidatesBin impl_def v in
      if isEmpty candidates then bleaf nil false
      else
        genbbin B C candidates modulo V iscons
  end.

Fixpoint genSynTree (A : LF)
  :=
  match A with
  | Atom _ => sun A sleaf
  | ~ B => sun A (genSynTree B)
  | [] B => sun A (genSynTree B)
  | B ~> C =>
      sun A
        (sbin
           (genSynTree B)
           (genSynTree C))
  end.

Definition logicsemt
  (A : LF)
  (v : list (pair LF nat))
  (toExpand : list LF)
  :=
  let cmp_pair := (fun x y => pair_eqb x y Nat.eqb Nat.eqb) in
  match A with
  | Atom p => smleaf nil v
  | ~ B =>
      let vB := applyTo v B 404 eqb_lf in
      let ndvals := applyTo neg_def vB nil Nat.eqb in
      gensemtree A ndvals v toExpand
  | [] B =>
      let vB := applyTo v B 404 eqb_lf in
      let ndvals := applyTo box_def vB nil Nat.eqb in
      gensemtree A ndvals v toExpand
  | B ~> C =>
      let vB := applyTo v B 404 eqb_lf in
      let vC := applyTo v C 404 eqb_lf in
      let ndvals := applyTo impl_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  end.



(*
Definition depfirst
  {X : Type}
  (A : X)
  (goal : nat)
  (atomval : list (pair X nat))
  (max : nat)
  (V : list nat)
  (arrows : list (pair nat (list nat)))
  (atomicMask dots : list nat)
  (logicst : X -> list (pair X nat) -> list X -> semtree)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic: X -> nat -> list nat -> list (pair X nat) -> list (pair X nat) -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
 *)
Compute
  depfirst
    ([]([] P ~> P))
    2
    [(P, 1)]
    1000
    [0;1;2]
    tKT
    arrows
    nil nil
    logicsemt
    eqb_lf
    leb_lf
    length_lf
    split_lf
    logicbt
    iscons
    genSynTree
.

