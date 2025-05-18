
(** S4 with conjunction and disjunction.  Alternative truth table implementation.

    * Here, we define the language with conjunction and disjunction
    * as primitive operators.  

***)

Require Import Forest.
Require Import List.
Require Import String.
Require Import Arith.
Require Import rnk.
Require Import Model.
Require Import String.
Import ListNotations.

Arguments Pair {X} {Y}.

Notation "( A ; B )" := (Pair A B).

(** Language specifics **)

Inductive extendedLF :=
| Atom : string -> extendedLF
| Neg : extendedLF -> extendedLF
| Box : extendedLF -> extendedLF
| Conj : extendedLF -> extendedLF -> extendedLF
| Disj : extendedLF -> extendedLF -> extendedLF
| Impl : extendedLF -> extendedLF -> extendedLF.

Notation "! A" := (Atom A) (at level 10).
Notation "~ A" := (Neg A).
Notation "A \/ B" := (Disj A B).
Notation "A /\ B" := (Conj A B).
Notation "[] A" := (Box A) (at level 80).
Notation "A ~> B" := (Impl A B) (at level 90).

Definition P := Atom "p0".
Definition Q := Atom "p1".
Definition U := Atom "p2".

Fixpoint eqb_elf (A : extendedLF) (B : extendedLF) :=
  match A with
  | Atom P => match B with
              | Atom Q => if (String.eqb P Q) then true
                          else false
              | _ => false
              end
  | ~ P => match B with
           | ~ Q => eqb_elf P Q
           | _ => false
           end
  | [] P => match B with
           | [] Q => eqb_elf P Q
           | _ => false
            end
  | P ~> Q => match B with
              | R ~> T => andb (eqb_elf P R) (eqb_elf Q T)
              | _ => false
              end
  | P \/ Q => match B with
              | R \/ T => andb (eqb_elf P R) (eqb_elf Q T)
              | _ => false
              end
  | P /\ Q => match B with
              | R /\ T => andb (eqb_elf P R) (eqb_elf Q T)
              | _ => false
              end
  end.

Fixpoint length_elf (A : extendedLF) :=
  match A with
  | Atom P => 0
  | ~ P => 1 + length_elf P
  | [] P => 1 + length_elf P
  | P ~> Q => 1 + length_elf P + length_elf Q
  | P \/ Q => 1 + length_elf P + length_elf Q
  | P /\ Q => 1 + length_elf P + length_elf Q
  end.

Definition leb_elf (A : extendedLF) (B : extendedLF) :=
  Nat.leb (length_elf A) (length_elf B).

Definition geb_elf (A : extendedLF) (B : extendedLF) :=
  negb (Nat.leb (length_elf A) (length_elf B)).

Fixpoint split_elf (L : extendedLF) :=
  match L with
  | Atom A => (Atom A)::nil
  | ~ A => (~ A)::(split_elf A)
  | [] A => ([] A)::(split_elf A)
  | A ~> B => (A ~> B)::((split_elf A)++(split_elf B))
  | A \/ B => (A \/ B)::((split_elf A)++(split_elf B))
  | A /\ B => (A /\ B)::((split_elf A)++(split_elf B))
  end.

(* Truth-table definitions *)

Definition neg_def :=
  [
    (0; [1; 2]);
    (1; [0]);
    (2; [0])
  ].

Definition box_def :=
  [
    (0; [0]);
    (1; [0]);
    (2; [2])
  ].

Definition impl_def :=
  [
    ((0; 0); [1;2]);
    ((0; 1); [1;2]);
    ((0; 2); [2]);
    ((1; 0); [0]);
    ((1; 1); [1;2]);
    ((1; 2); [2]);
    ((2; 0); [0]);
    ((2; 1); [1]);
    ((2; 2); [2])
  ].

Definition disj_def :=
  [
    ((0; 0); [0]);
    ((0; 1); [1;2]);
    ((0; 2); [2]);
    ((1; 0); [1;2]);
    ((1; 1); [1;2]);
    ((1; 2); [2]);
    ((2; 0); [2]);
    ((2; 1); [2]);
    ((2; 2); [2])
  ].

Definition conj_def :=
  [
    ((0; 0); [0]);
    ((0; 1); [0]);
    ((0; 2); [0]);
    ((1; 0); [0]);
    ((1; 1); [1]);
    ((1; 2); [1]);
    ((2; 0); [0]);
    ((2; 1); [1]);
    ((2; 2); [2])
  ].

(** S4 **)

Definition S4
  (B A : extendedLF)
  (partialV : btree extendedLF)
  (V : list nat)
  (allVs : list (btree extendedLF))
  : btree extendedLF
  :=
  match A with
  | Atom B => Leaf _ true
  | Neg B =>
      unary_op A B partialV 0 neg_def eqb_elf
  | Box B =>
      unary_op A B partialV 0 box_def eqb_elf
  | Impl B C =>
      bin_op A B C partialV 0 0 impl_def eqb_elf
  | Disj B C =>
      bin_op A B C partialV 0 0 disj_def eqb_elf
  | Conj B C =>
      bin_op A B C partialV 0 0 conj_def eqb_elf
  end.

Definition arrows :=
  [
    (1, [[0]])
  ].

Definition nec (A : extendedLF) := Some (A, [2]).

Definition tS4 :=
  [
    ((2, [nec]), true)
  ].

Definition makeMatrix (A : extendedLF) :=
  makeIt
    A
    [0;1;2]
    S4
    eqb_elf
    leb_elf
    length_elf
    split_elf.

Definition makeRestrictionSteps
  (A : extendedLF) :=
  restrictionSteps
    A
    (makeMatrix A)
    eqb_elf
    leb_elf
    geb_elf
    split_elf
    arrows
    3
    tS4
.

Definition makeComputeTable
  (A : extendedLF) :=
  let steps := makeRestrictionSteps A in
  computeTable steps.

Definition makeArrangeKM
  (A : extendedLF)
  (smallest lazymode : bool)
  :=
  arrangeKM
    A
    (makeMatrix A)
    eqb_elf
    leb_elf
    geb_elf
    split_elf
    arrows
    3
    smallest lazymode
    tS4
.

Definition makeAllRn
  (A : extendedLF)
  (smallest lazymode : bool)
  :=
  rnkripke
    A
    (makeMatrix A)
    eqb_elf
    leb_elf
    geb_elf
    length_elf
    split_elf
    arrows
    3
    [1;2]
    [Transitive;Reflexive]
    smallest lazymode
    tS4
.

Definition makeThisRn
  (w : nat)
  (A : extendedLF)
  (smallest lazymode : bool)
  :=
  (rnkripke
    A
    (makeMatrix A)
    eqb_elf
    leb_elf
    geb_elf
    length_elf
    split_elf
    arrows
    3
    [1;2]
    [Transitive;Reflexive]
    smallest lazymode
    tS4
  )
.
(*************************************)

(* 

   Testes
 
*)

(*************************************)

Notation "<> A" := (~ ([] (~ A))) (at level 90).

Definition AK := ([](P ~> Q) ~> ([]P ~> []Q)).
Definition AB := P ~> [] <> P.
Definition AM := []P ~> P.
Definition A4 := []P ~> [][]P.
Definition AD := []P ~> <>P.
Definition A5 := <>P ~> []<>P.

Definition k3 := ((<> P) ~> [] Q) ~> (P ~> Q).


Compute reverseThisList (nodeToNat (makeMatrix (k3))).


Compute makeComputeTable ([]([]P \/ []~[]P)).

(* Val : X -> list (node X) -> nat -> bool *)
Fixpoint Val
  (A : extendedLF)
  (model : list (node extendedLF))
  (w : nat) :=
  let accW := getAllAccessedWorld model w in
  match A with
  | ! _ => checkValInW A w model eqb_elf
  | ~ p => negb (Val p model w)
  | p /\ q => andb (Val p model w) (Val q model w)
  | p \/ q => orb (Val p model w) (Val q model w)
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

(*

Definition checkAllModels
  {X : Type}
  (A : X)
  (V : list nat)
  (logic : X -> X -> btree X -> list nat -> list (btree X) -> btree X)
  (eqb_X leb_X geb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (cmp0 cmp1 cmp2 cmp3 : nat -> bool)
  (Val : X -> list (node X) -> nat -> bool)
  (default : nat)
  :=
 *)

Definition makeCheckAllModels
  (make : extendedLF -> list (list (Forest.node extendedLF)))
  (A : extendedLF)
  (smallest lazymode : bool)
  :=
  checkAllModels
    A
    (make A)
    eqb_elf leb_elf geb_elf
    split_elf
    arrows
    Val
    4
    (makeAllRn make A smallest lazymode)
    [1;2]
    tS4
.

Definition prop1 := ([](P  ~> Q)) ~> ((<> P) ~> <> Q).

(* Compute (makeAllRn makeMakeIt_otf AB false false). *)
(*
Compute makeCheckAllModels makeMakeIt_otf prop1 false false.
*)

Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].


Recursive Extraction
  makeCheckAllModels makeMakeIt makeComputeTable makeThisRn existb forallnegb.

(*****

The following functions/definitions are required by the deep-first search method.

 ******)

Definition iscons
  (A B : pair extendedLF nat)
  :=
  negb
    (orb
       (andb
          (orb
             (eqb_elf (proj_l A) (~ (proj_l B)))
             (eqb_elf (proj_l B) (~ (proj_l A))))
          (Nat.eqb (proj_r A) (proj_r B))
       )
       (andb
          (eqb_elf (proj_l A) (proj_l B))
          (negb (Nat.eqb (proj_r A) (proj_r B))))).

Fixpoint logicbt
  (l : list (pair extendedLF nat))
  (t : backtree (pair extendedLF nat))
  (V : list (pair extendedLF nat))
  (atomicMask : list nat)
  :=
  match l with
  | nil => bleaf nil true
  | (A, v)::tl =>
      if isConsistent A v iscons V then
        match A with
        | Atom p =>
            if isElementInList v atomicMask Nat.eqb then
              bleaf nil false
            else
              logicbt tl t V atomicMask
        | [] B =>
            let candidates := getCandidatesUn box_def v in
            if isEmpty candidates then bleaf nil false
            else
              genbun B candidates tl V iscons
        | ~ B =>
            let candidates := getCandidatesUn neg_def v in
            if isEmpty candidates then bleaf nil false
            else
              genbun B candidates tl V iscons
        | B /\ C =>
            let candidates := getCandidatesBin conj_def v in
            if isEmpty candidates then bleaf nil false
            else
              genbbin B C candidates tl V iscons
        | B ~> C =>
            let candidates := getCandidatesBin impl_def v in
            if isEmpty candidates then bleaf nil false
            else
              genbbin B C candidates tl V iscons
        | B \/ C =>
            let candidates := getCandidatesBin disj_def v in
            if isEmpty candidates then bleaf nil false
            else
              genbbin B C candidates tl V iscons
        end
      else
        bleaf nil false
  end.

Fixpoint genSynTree (A : extendedLF)
  :=
  match A with
  | Atom _ => sun A sleaf
  | ~ B => sun A (genSynTree B)
  | [] B => sun A (genSynTree B)
  | B /\ C =>
      sun A
        (sbin
           (genSynTree B)
           (genSynTree C))
  | B \/ C =>
      sun A
        (sbin
           (genSynTree B)
           (genSynTree C))
  | B ~> C =>
      sun A
        (sbin
           (genSynTree B)
           (genSynTree C))
  end.

Definition logicsemt
  (A : extendedLF)
  (v : list (pair extendedLF nat))
  (toExpand : list extendedLF)
  :=
  let cmp_pair := (fun x y => pair_eqb x y Nat.eqb Nat.eqb) in
  match A with
  | Atom p => smleaf nil v
  | ~ B =>
      let vB := applyTo v B 404 eqb_elf in
      let ndvals := applyTo neg_def vB nil Nat.eqb in
      gensemtree A ndvals v toExpand
  | [] B =>
      let vB := applyTo v B 404 eqb_elf in
      let ndvals := applyTo box_def vB nil Nat.eqb in
      gensemtree A ndvals v toExpand
  | B ~> C =>
      let vB := applyTo v B 404 eqb_elf in
      let vC := applyTo v C 404 eqb_elf in
      let ndvals := applyTo impl_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  | B /\ C =>
      let vB := applyTo v B 404 eqb_elf in
      let vC := applyTo v C 404 eqb_elf in
      let ndvals := applyTo conj_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  | B \/ C =>
      let vB := applyTo v B 404 eqb_elf in
      let vC := applyTo v C 404 eqb_elf in
      let ndvals := applyTo disj_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  end.

Definition findcm (A : extendedLF) (atomval : list (pair extendedLF nat)) :=
  depfirst
    A
    0
    atomval
    1000
    [0;1;2]
    tS4
    arrows
    nil
    nil
    logicsemt
    eqb_elf
    leb_elf
    length_elf
    split_elf
    logicbt
    iscons
    genSynTree.

Definition p0 := Atom "p0" .
Definition p1 := Atom "p1" .
Definition p2 := Atom "p2" .
Definition p3 := Atom "p3" .
Definition p4 := Atom "p4" .
Definition p5 := Atom "p5" .
Definition p6 := Atom "p6" .
Definition p7 := Atom "p7" .
Definition p8 := Atom "p8" .
Definition p9 := Atom "p9" .
Definition p10 := Atom "p10" .
Definition p11 := Atom "p11" .
Definition p12 := Atom "p12" .
Definition p13 := Atom "p13" . 
Definition p14 := Atom "p14" .
Definition p15 := Atom "p15" .
Definition p16 := Atom "p16" .
Definition p17 := Atom "p17" .
Definition p18 := Atom "p18" .
Definition p19 := Atom "p19" .
Definition p20 := Atom "p20" .
Definition p21 := Atom "p21" .

Compute findcm (<> P ~> [] <> P) [(P, 0)].
