Require Import Forest.
Require Import rnk.
Require Import Model.
Require Import List.
Require Import String.
Require Import Arith.
Import ListNotations.

Inductive iLF :=
| iAtom : string -> iLF
| iNeg : iLF -> iLF
| iDisj : iLF -> iLF -> iLF
| iConj : iLF -> iLF -> iLF
| iImpl : iLF -> iLF -> iLF.

Definition vT := 2.
Definition vU := 1.
Definition vF := 0.

Notation "! A" := (iAtom A) (at level 10).
Notation "~ A" := (iNeg A).
Notation "A ~> B" := (iImpl A B) (at level 90).
Notation "A \/ B" := (iDisj A B).
Notation "A /\ B" := (iConj A B).
Notation "A <~> B" := ((A ~> B) /\ (B ~> A)) (at level 90).

Fixpoint eqb_ilf (A : iLF) (B : iLF) :=
  match A with
  | ! P => match B with
           | iAtom Q =>
               if (String.eqb P Q) then true
               else false
              | _ => false
              end
  | ~ P => match B with
           | ~ Q => eqb_ilf P Q
           | _ => false
           end
  | P \/ Q => match B with
              | R \/ T => andb (eqb_ilf P R) (eqb_ilf Q T)
              | _ => false
              end
  | P /\ Q => match B with
              | R /\ T => andb (eqb_ilf P R) (eqb_ilf Q T)
              | _ => false
              end
  | P ~> Q => match B with
              | R ~> T => andb (eqb_ilf P R) (eqb_ilf Q T)
              | _ => false
              end
  end.

Fixpoint length_ilf (A : iLF) :=
  match A with
  | ! P => 0
  | ~ P => 1 + length_ilf P
  | P \/ Q => 1 + length_ilf P + length_ilf Q
  | P /\ Q => 1 + length_ilf P + length_ilf Q     
  | P ~> Q => 1 + length_ilf P + length_ilf Q
  end.

Definition leb_ilf (A : iLF) (B : iLF) :=
  Nat.leb (length_ilf A) (length_ilf B).

Definition geb_ilf (A : iLF) (B : iLF) :=
  negb (Nat.leb (length_ilf A) (length_ilf B)).

Fixpoint split_ilf (L : iLF) :=
  match L with
  | ! A => (! A)::nil
  | ~ A => (~ A)::(split_ilf A)
  | A \/ B => (A \/ B)::((split_ilf A)++(split_ilf B))
  | A /\ B => (A /\ B)::((split_ilf A)++(split_ilf B))
  | A ~> B => (A ~> B)::((split_ilf A)++(split_ilf B))
  end.

Definition P := iAtom "p0".
Definition Q := iAtom "p1".
Definition R := iAtom "p2".
Definition T := iAtom "p3".


(* TRUTH TABLES *)

Definition neg_def :=
  [
    (vF, [vU; vT]);
    (vU, [vU; vT]);
    (vT, [vF])
  ].

Definition impl_def :=
  [
    ((vF, vF), [vU; vT]);
    ((vF, vU), [vU; vT]);
    ((vF, vT), [vT]);
    ((vU, vF), [vU; vT]);
    ((vU, vU), [vU; vT]);
    ((vU, vT), [vT]);
    ((vT, vF), [vF]);
    ((vT, vU), [vF]);
    ((vT, vT), [vT])
  ].

Definition disj_def :=
  [
    ((vF, vF), [vF]);
    ((vF, vU), [vF]);
    ((vF, vT), [vT]);
    ((vU, vF), [vF]);
    ((vU, vU), [vF]);
    ((vU, vT), [vT]);
    ((vT, vF), [vT]);
    ((vT, vU), [vT]);
    ((vT, vT), [vT])
  ].

Definition conj_def :=
  [
    ((vF, vF), [vF]);
    ((vF, vU), [vF]);
    ((vF, vT), [vF]);
    ((vU, vF), [vF]);
    ((vU, vU), [vF]);
    ((vU, vT), [vF]);
    ((vT, vF), [vF]);
    ((vT, vU), [vF]);
    ((vT, vT), [vT])
  ].

(***)

Definition IPL
  (B A : iLF)
  (partialV : btree iLF)
  (V : list nat)
  (allVs : list (btree iLF))
  : btree iLF
  :=
  match A with
  | iAtom B => Leaf _ true
  | iNeg B =>
      unary_op A B partialV 0 neg_def eqb_ilf
  | iImpl B C =>
      bin_op A B C partialV 0 0 impl_def eqb_ilf
  | iDisj B C =>
      bin_op A B C partialV 0 0 disj_def eqb_ilf
  | iConj B C =>
      bin_op A B C partialV 0 0 conj_def eqb_ilf
  end.

Definition arrows :=
  [
    (vU, [[vF]])
  ].

Definition monoto (A : iLF) := Some (A, [vT]).

Definition tIPL :=
  [
    ((vT, [monoto]), true)
  ].

(**)

Definition makeMatrix (A : iLF) :=
  makeIt
    A
    [0;2]
    IPL
    eqb_ilf
    leb_ilf
    length_ilf
    split_ilf.

Definition makeAllRn
  (A : iLF)
  (smallest lazymode : bool) :=
  rnkripke
    A
    (makeMatrix A)
    eqb_ilf
    leb_ilf
    geb_ilf
    length_ilf
    split_ilf
    arrows
    4
    [2]
    [Transitive;Reflexive]
    smallest lazymode tIPL
.

Definition makeThisRn
  (w : nat)
  (A : iLF)
  (smallest lazymode : bool)
  :=
  rnkripke
    A
    (makeMatrix A)
    eqb_ilf
    leb_ilf
    geb_ilf
    length_ilf
    split_ilf
    arrows
    4
    [2]
    [Transitive;Reflexive]
    smallest lazymode tIPL 
.

(***)

(* Model checking *)

Fixpoint Val
  (A : iLF)
  (model : list (node iLF))
  (w : nat) :=
  let accW := getAllAccessedWorld model w in
  match A with
  | ! _ => checkValInW A w model eqb_ilf
  | ~ p => forallnegb (map (Val p model) accW)
  | p /\ q => andb (Val p model w) (Val q model w)
  | p \/ q => orb (Val p model w) (Val q model w)
  | p ~> q =>
      Model.forallb (
          map
            (fun k =>
               if (Val p model k) then
                 (Val q model k)
                else true)
            accW)
  end.


(***)


(** *********************   **)



Definition makeCheckAllModels
  (A : iLF)
  (smallest lazymode : bool)
  :=
  checkAllModels
    A
    (makeMatrix A)
    eqb_ilf leb_ilf geb_ilf
    split_ilf
    arrows
    Val
    3
    (makeAllRn A smallest lazymode)
    [vT]
    tIPL
.

Definition makeCheckThisModel
  (w : nat)
  (A : iLF)
  (smallest lazymode : bool)
  :=
  checkAllModels
    A
    (makeMatrix A)
    eqb_ilf leb_ilf geb_ilf
    split_ilf
    arrows
    Val
    3
    (makeThisRn w A smallest lazymode)
    [vT]
    tIPL
.

Definition makeRestrictionSteps
  (A : iLF) :=
  restrictionSteps
    A
    (makeMatrix A)
    eqb_ilf
    leb_ilf
    geb_ilf
    split_ilf
    arrows
    3
    tIPL
.

Definition makeComputeTable
  (A : iLF) :=
  let steps := makeRestrictionSteps A in
  computeTable steps.

Definition makeArrangeKM
  (A : iLF)
  (mode_all lazymode : bool)
  :=
  arrangeKM
    A
    (makeMatrix A)
    eqb_ilf
    leb_ilf
    geb_ilf
    split_ilf
    arrows
    3
    mode_all lazymode tIPL
.


Compute reverseThisList (nodeToNat (makeMatrix ((~~(P ~> ~~P)) /\ ~~~P))).

Compute makeComputeTable ((P ~> ~~P)).


Definition waj := ((((P ~> Q) ~> P) ~> P) ~> Q) ~> Q. (* Lei de Wajsberg *)

Definition peirce := (((P ~> Q) ~> P) ~> P).

Compute rearrangeModels (makeThisRn 1 (~(P /\ ~Q)) false false).
Compute rearrangeModels (makeThisRn 1 waj true false).

(*
Compute makeComputeTable makeMakeIt peirce.

Compute rearrangeModels (makeThisRn 1 makeMakeIt_otf (~(P /\ ~Q)) false false).

Compute makeCheckAllModels makeMakeIt_otf (~(~P /\ ~Q)) false false.

Compute makeCheckAllModels makeMakeIt_otf (((P ~> Q) ~> R)~> T) false true.
*)
Definition p1 := P ~> (~ (~ P)).
Definition p2 := (~ P) ~> (~ (~ (~ P))).
Definition p3 := ~ ( P /\ (~ P)).
Definition p4 := (~ (~ (P \/ (~ P)))).
Definition p5 := (~ (P \/ (Q)) <~> ((~ P) /\ (~ ( Q)))).
Definition p5_ida := (~ (P \/ (Q)) ~> ((~ P) /\ (~ ( Q)))).
Definition p6 := (P \/ (~ P)) ~> (~ (~ P) ~> P).
Definition p7 := (P ~> ( Q)) ~> (~ (P /\ (~ ( Q)))).
Definition p8 := (P ~> (~ ( Q))) <~> (~ (P /\ ( Q))).
Definition p8_ida := (P ~> (~ ( Q))) ~> (~ (P /\ ( Q))). 
Definition p9 := ((~ (~ P)) /\ (~ (~ ( Q)))) <~> (~ (~ (P /\ ( Q)))).
Definition p9_ida := ((~ (~ P)) /\ (~ (~ ( Q)))) ~> (~ (~ (P /\ ( Q)))).
Definition p10 := ((~ (~ P)) ~> (~ (~ ( Q)))) <~> (~ (~ (P ~> ( Q)))).
Definition p10_ida := ((~ (~ P)) ~> (~ (~ ( Q)))) ~> (~ (~ (P ~> ( Q)))).
Definition p11 := ((~ (~ P)) ~> ( Q)) ~> ((~ ( Q)) ~> (~ P)).

Compute makeComputeTable makeMakeIt (p9).

(****)

Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction
  makeCheckAllModels makeMakeIt makeComputeTable makeThisRn existb.

(*****

The following functions/definitions are required by the deep-first search method.

 ******)

Definition iscons
  (A B : pair iLF nat)
  :=
  negb
    (orb
       (andb
          (orb
             (eqb_ilf (proj_l A) (~ (proj_l B)))
             (eqb_ilf (proj_l B) (~ (proj_l A))))
          (Nat.eqb (proj_r A) (proj_r B))
       )
       (andb
          (eqb_ilf (proj_l A) (proj_l B))
          (negb (Nat.eqb (proj_r A) (proj_r B))))).


Fixpoint logicbt
  (l : list (pair iLF nat))
  (t : backtree (pair iLF nat))
  (V : list (pair iLF nat))
  (atomicMask : list nat)
  :=
  match l with
  | nil => bleaf nil true
  | (A, v)::tl =>
      if isConsistent A v iscons V then
        match A with
        | iAtom p =>
            if isElementInList v atomicMask Nat.eqb then
              bleaf nil false
            else
              logicbt tl t V atomicMask
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

Fixpoint genSynTree (A : iLF)
  :=
  match A with
  | iAtom _ => sun A sleaf
  | ~ B => sun A (genSynTree B)
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
  (A : iLF)
  (v : list (pair iLF nat))
  (toExpand : list iLF)
  :=
  let cmp_pair := (fun x y => pair_eqb x y Nat.eqb Nat.eqb) in
  match A with
  | iAtom p => smleaf nil v
  | ~ B =>
      let vB := applyTo v B 404 eqb_ilf in
      let ndvals := applyTo neg_def vB nil Nat.eqb in
      gensemtree A ndvals v toExpand
  | B ~> C =>
      let vB := applyTo v B 404 eqb_ilf in
      let vC := applyTo v C 404 eqb_ilf in
      let ndvals := applyTo impl_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  | B /\ C =>
      let vB := applyTo v B 404 eqb_ilf in
      let vC := applyTo v C 404 eqb_ilf in
      let ndvals := applyTo conj_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  | B \/ C =>
      let vB := applyTo v B 404 eqb_ilf in
      let vC := applyTo v C 404 eqb_ilf in
      let ndvals := applyTo disj_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  end.

Definition findcm (A : iLF) (atomval : list (pair iLF nat)) :=
  depfirst
    A
    vF
    atomval
    100
    [vF; vU; vT]
    tIPL
    arrows
    [vU]
    nil
    logicsemt
    eqb_ilf
    leb_ilf
    length_ilf
    split_ilf
    logicbt
    iscons
    genSynTree.

Compute findcm (~p5) [(P, vF); (Q, vF)].
