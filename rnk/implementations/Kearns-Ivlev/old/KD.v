(**

    This KD is an adaptation of Kearns-Ivlev tables and was introduced in "More Modal Semantics Without Possible Worlds" (Omori & Skurt).

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
(*| Disj : LF -> LF -> LF*)
| Impl : LF -> LF -> LF.

Notation "! A" := (Atom A) (at level 10).
Notation "~ A" := (Neg A).
Notation "[] A" := (Box A) (at level 80).
Notation "<> A" := (Dia A) (at level 80).
(* Notation "A \/ B" := (Disj A B). *)
Notation "A ~> B" := (Impl A B) (at level 90).

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
  (*| P \/ Q => match B with
              | R \/ T => andb (eqb_lf P R) (eqb_lf Q T)
              | _ => false
              end*)
  | P ~> Q => match B with
              | R ~> T => andb (eqb_lf P R) (eqb_lf Q T)
              | _ => false
              end
  end.

Fixpoint length_lf (A : LF) :=
  match A with
  | Atom P => 0
  | ~ P => 1 + length_lf P
  | [] P => 1 + length_lf P
  | <> P => 1 + length_lf P
  (*| P \/ Q => 1 + length_lf P + length_lf Q*)
  | P ~> Q => 1 + length_lf P + length_lf Q
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
  (*| A \/ B => (A \/ B)::((split_lf A)++(split_lf B))*)
  | A ~> B => (A ~> B)::((split_lf A)++(split_lf B))
  end.

(* Truth-table definitions *)

Definition vF := 0.
Definition vf1 := 1.
Definition vf := 2.
Definition vf2 := 3.
Definition vt1 := 4.
Definition vt := 5.
Definition vt2 := 6.
Definition vT := 7.

(*

Here,

v(A) = vF means "A is impossible"
v(A) = vf(1/2) means "A is contingently false"
v(A) = vt(1/2) means "A is contingently true"
v(A) = vT means "A is necessary"

 *)

Definition V := [vF; vf; vf2; vt; vt2; vT].

Definition D := [vt; vt2; vT].
Definition F := [vf; vf2; vF].

Definition neg_def :=
  [
    (vF, [vT]);
    (vf, [vt]);
    (vf2, [vt2]);
    (vt, [vf]);
    (vt2, [vf2]);
    (vT, [vF])
  ].
(*
Definition box_def :=
  [
    (vF, F);
    (vf1, D);
    (vf, F);
    (vf2, D);
    (vt1, D);
    (vt, F);
    (vt2, F);
    (vT, D)
  ].
 *)
Definition box_def :=
  [
    (vF, [vF; vf; vf2]);
    (vf, [vF; vf; vf2]);
    (vf2, [vT; vt; vt2]);
    (vt, [vF; vf; vf2]);
    (vt2, [vF; vf; vf2]);
    (vT, [vT; vt; vt2])
  ].

Definition dia_def :=
  [
    (vF, [vF; vf; vf2]);
    (vf, [vT; vt; vt2]);
    (vf2, [vT; vt; vt2]);
    (vt, [vT; vt; vt2]);
    (vt2, [vF; vf; vf2]);
    (vT, [vT; vt; vt2])
  ].

(*
Definition impl_def :=
  [
    ((vF; vF); [vT; vt]);
    ((vF; vf1); [vT]);
    ((vF; vf); [vT; vt]);
    ((vF; vf2); [vT]);
    ((vF; vt1); [vT]);
    ((vF; vt); [vT; vt]);
    ((vF; vt2); [vT; vt]);
    ((vF; vT); [vT]);
    ((vf1; vF); [vt2]);
    ((vf1; vf1); [vt1]);
    ((vf1; vf); [vt]);
    ((vf1; vf2); [vT]);
    ((vf1; vt1); [vt1]);
    ((vf1; vt); [vt]);
    ((vf1; vt2); [vt2]);
    ((vf1; vT); [vT]);
    ((vf; vF); [vT; vt]);
    ((vf; vf1); [vT]);
    ((vf; vf); [vT; vt]);
    ((vf; vf2); [vT]);
    ((vf; vt1); [vT]);
    ((vf; vt); [vT; vt]);
    ((vf; vt2); [vT; vt]);
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
    ((vt; vF); [vf2; vf]);
    ((vt; vf1); [vf2]);
    ((vt; vf); [vf2; vf]);
    ((vt; vf2); [vf2]);
    ((vt; vt1); [vT]);
    ((vt; vt); [vT; vt]);
    ((vt; vt2); [vT; vt]);
    ((vt; vT); [vT]);
    ((vt2; vF); [vf2; vf]);
    ((vt2; vf1); [vf2]);
    ((vt2; vf); [vf2; vf]);
    ((vt2; vf2); [vf2]);
    ((vt2; vt1); [vT]);
    ((vt2; vt); [vT; vt]);
    ((vt2; vt2); [vT; vt]);
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

 *)

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

Definition disj_def :=
  [
    ((vF; vF); [vF]);
    ((vF; vt); [vt]);
    ((vF; vf); [vf]);
    ((vF; vT); [vT]);
    ((vt; vF); [vt]);
    ((vt; vt); [vT; vt]);
    ((vt; vf); [vT; vt]);
    ((vt; vT); [vT]);
    ((vf; vF); [vf]);
    ((vf; vt); [vT; vt]);
    ((vf; vf); [vf]);
    ((vf; vT); [vT]);
    ((vT; vF); [vT]);
    ((vT; vt); [vT]);
    ((vT; vf); [vT]);
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
  (*| B \/ C =>
      bin_op A B C partialV 0 0 disj_def eqb_lf*)
  | B ~> C =>
      bin_op A B C partialV 0 0 impl_def eqb_lf
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

Definition nec (A : LF) := Some (A, [vt1; vt; vt2; vT]).
Definition imp (A : LF) := Some (A, [vf1; vf; vf2; vF]).
Definition deadend (A : LF) := Some (A, [404]).

Definition trule :=
  [
    ((vT, [nec]), true);
    ((vt1, [deadend]), true);
    ((vt2, [imp]), true);
    ((vf1, [deadend]), true);
    ((vf2, [nec]), true);
    ((vF, [imp]), true)
  ].

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

(*************************************)

(* 

   Testes
 
*)

(*************************************)

Notation "<>s A" := (~ ([] (~ A))) (at level 90).
Notation "[]s A" := (~ (<> (~ A))) (at level 90).

Definition P := Atom "p0".
Definition Q := Atom "p1".
Definition U := Atom "p3".

Definition AK := ([](P ~> Q) ~> ([]P ~> []Q)).
Definition AB := P ~> []<> P.
Definition AM := [] P ~> P.
Definition A4 := []P ~> [][]P.
Definition AD := []P ~> <> P.
Definition A5 := <> P ~> []<> P.



Compute makeComputeTable ((<> P)).


Compute (reverseThisList (nodeToNat (makeMatrix ((AD))))).


(*

Definition vF := 0.
Definition vf1 := 1.
Definition vf := 2.
Definition vf2 := 3.
Definition vt1 := 4.
Definition vt := 5.
Definition vt2 := 6.
Definition vT := 7.

*)



(*

Definition vF := 0.
Definition vf1 := 1.
Definition vf := 2.
Definition vf2 := 3.
Definition vt1 := 4.
Definition vt := 5.
Definition vt2 := 6.
Definition vT := 7.

*)


Compute makeComputeTable (AK).

Definition k1 := ([](P  ~> Q)) ~> ((<>s P) ~> <>s Q).
Definition k2 := (<>s (P \/ Q)) ~> ((<>s P) \/ <>s Q).
Definition k3 := ((<>s P) ~> [] Q) ~> [] (P ~> Q).
(* Definition k4 := (~ <> (P /\ ~ P)).*)

Compute makeComputeTable ([] k1).

Compute makeComputeTable AB.

(* Nessa lógica, valem AK, AD, AM e A4.*)

Require Import Model.

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

