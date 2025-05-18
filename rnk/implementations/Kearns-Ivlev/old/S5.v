(**

   S4 by Kearns (1981).

 **)

Require Import Forest.
Require Import List.
Require Import String.
Require Import Arith.
Require Import rnk.
Require Import String.
Require Import Model.
Import ListNotations.

Arguments Pair {X} {Y}.

Notation "( A ; B )" := (Pair A B).

(** Language specifics **)

Inductive LF :=
| Atom : string -> LF
| Neg : LF -> LF
| Box : LF -> LF
| Conj : LF -> LF -> LF
| Disj : LF -> LF -> LF
| Impl : LF -> LF -> LF
| Dia : LF -> LF.

Notation "! A" := (Atom A) (at level 10).
Notation "~ A" := (Neg A).
Notation "A \/ B" := (Disj A B).
Notation "A /\ B" := (Conj A B).
Notation "[] A" := (Box A) (at level 80).
Notation "<> A" := (Dia A) (at level 80).
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
  | P ~> Q => match B with
              | R ~> T => andb (eqb_lf P R) (eqb_lf Q T)
              | _ => false
              end
  | P \/ Q => match B with
              | R \/ T => andb (eqb_lf P R) (eqb_lf Q T)
              | _ => false
              end
  | P /\ Q => match B with
              | R /\ T => andb (eqb_lf P R) (eqb_lf Q T)
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
  | P \/ Q => 1 + length_lf P + length_lf Q
  | P /\ Q => 1 + length_lf P + length_lf Q
  end.

Definition leb_lf (A : LF) (B : LF) :=
  Nat.leb (length_lf A) (length_lf B).

Definition geb_lf (A : LF) (B : LF) :=
  negb (Nat.leb (length_lf A) (length_lf B)).

Fixpoint split_lf (L : LF) :=
  match L with
  | Atom A => (Atom A)::nil
  | ~ A => (~ A)::(split_lf A)
  | [] A => ([] A)::(split_lf A)
  | <> A => (<> A)::(split_lf A)
  | A ~> B => (A ~> B)::((split_lf A)++(split_lf B))
  | A \/ B => (A \/ B)::((split_lf A)++(split_lf B))
  | A /\ B => (A /\ B)::((split_lf A)++(split_lf B))
  end.

(* Truth-table definitions *)

Definition vF := 0.
Definition vf := 1.
Definition vt := 2.
Definition vT := 3.

Definition V := [vF; vt; vf; vT].
Definition D := [vt; vT].

Definition neg_def :=
  [
    (vF; [vT]);
    (vt; [vf]);
    (vf; [vt]);
    (vT; [vF])
  ].

Definition box_def :=
  [
    (vF; [vF]);
    (vt; [vF]);
    (vf; [vF]);
    (vT; [vT])
  ].

Definition dia_def :=
  [
    (vF; [vF]);
    (vt; [vT]);
    (vf; [vT]);
    (vT; [vT])
  ].

Definition impl_def :=
  [
    ((vF; vF); [vT]);
    ((vF; vt); [vT]);
    ((vF; vf); [vT]);
    ((vF; vT); [vT]);
    ((vt; vF); [vf]);
    ((vt; vt); [vT; vt]);
    ((vt; vf); [vf]);
    ((vt; vT); [vT]);
    ((vf; vF); [vt]);
    ((vf; vt); [vT; vt]);
    ((vf; vf); [vT; vt]);
    ((vf; vT); [vT]);
    ((vT; vF); [vF]);
    ((vT; vt); [vt]);
    ((vT; vf); [vf]);
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

Definition conj_def :=
  [
    ((vF; vF); [vF]);
    ((vF; vt); [vF]);
    ((vF; vf); [vF]);
    ((vF; vT); [vF]);
    ((vt; vF); [vF]);
    ((vt; vt); [vt]);
    ((vt; vf); [vf; vF]);
    ((vt; vT); [vt]);
    ((vf; vF); [vF]);
    ((vf; vt); [vf; vF]);
    ((vf; vf); [vf; vF]);
    ((vf; vT); [vf]);
    ((vT; vF); [vF]);
    ((vT; vt); [vt]);
    ((vT; vf); [vf]);
    ((vT; vT); [vT])
  ].

(** S5 **)

Definition S5
  (B A : LF)
  (partialV : btree LF)
  (V : list nat)
  (allVs : list (btree LF))
  : btree LF
  :=
  match A with
  | Atom B => Leaf _ true
  | Neg B =>
      unary_op A B partialV 0 neg_def eqb_lf
  | Box B =>
      unary_op A B partialV 0 box_def eqb_lf
  | Dia B =>
      unary_op A B partialV 0 dia_def eqb_lf
  | Impl B C =>
      bin_op A B C partialV 0 0 impl_def eqb_lf
  | Disj B C =>
      bin_op A B C partialV 0 0 disj_def eqb_lf
  | Conj B C =>
      bin_op A B C partialV 0 0 conj_def eqb_lf
  end.

(** S5 **)

(*

> arrows

As arrows definem as pré-relações (<).

Exemplo:

(vf; [vT]) -- se v(A) = vf, então w(A) = vT

> trules

As trules (ou regras) definem os critérios para a existênca da relação.

Dados v e w, uma regra determina se "v < w" ou não.

A ordem é importante aqui, por isso as regras são de duas espécies:

(LR, RL)

LR = (R, true) rules left to right (ex. se v(A) = T, então w(A) = T ou w(A) = vf )

RL = (R, false) rules right to left (ex. se w(A) = T, então v(A) = T ou v(A) = vf )

Cada regra é uma função que transforma uma fórmula A de v em uma condição para A em w, representada por (A, [wA0, ..., wAn]).

 *)

Definition arrows :=
  [
    (vt, [[vF]; [vf]]);
    (vf, [[vT]; [vt]])
  ].

Definition nec (A : LF) := Some (A, [vT]).
Definition imp (A : LF) := Some (A, [vF]).

Definition tS5 :=
  [
    ((vT, [nec]), true);
    ((vF, [imp]), true);
    ((vT, [nec]), false);
    ((vF, [imp]), false)
  ].

Definition makeMatrix (A : LF) :=
  makeIt
    A
    V
    S5
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
    3
    tS5.

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
    3
    smallest lazymode tS5
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
    3
    D
    [Transitive;Reflexive;Symmetry]
    smallest lazymode tS5
.

Definition makeThisRn
  (w : nat)
  (A : LF)
  (smallest lazymode : bool)
  :=
  (rnkripke
    A
    (makeMatrix A)
    eqb_lf
    leb_lf
    geb_lf
    length_lf
    split_lf
    arrows
    3
    D
    [Transitive;Reflexive;Symmetry]
    smallest lazymode tS5
  )
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
  | p /\ q => andb (Val p model w) (Val q model w)
  | p \/ q => orb (Val p model w) (Val q model w)
  | <> p =>
      existb (
          map
            (fun k =>
               (Val p model k))
            accW
        )
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

Definition makeCheckAllModels
  (make : eLF -> list (list (Forest.node eLF)))
  (A : eLF)
  (smallest lazymode : bool)
  :=
  checkAllModels
    A
    (make A)
    eqb_elf leb_elf geb_elf
    split_elf
    arrows
    pruning_0 pruning_1 pruning_2 pruning_3
    Val
    4
    (makeAllRn make A smallest lazymode)
    [vt;vT]
.
 *)


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
    4
    (makeAllRn A smallest lazymode)
    D
    tS5
.

(*************************************)

(* 

   Testes
 
*)

(*************************************)

(*Notation "[] A" := (~ (<> (~ A))) (at level 90).*)

Notation "<>s A" := (~ [] ~ A) (at level 70).
Notation "[]s A" := (~ <> ~ A) (at level 70).

Definition P := Atom "p0".
Definition Q := Atom "p1".
Definition U := Atom "p2".

Definition AK := (([]s (P ~> Q)) ~> (([]s P) ~> []s Q)).
Definition AB := P ~> []<> P.
Definition AM := []P ~> P.
Definition A4 := [] P ~> [][] P.
Definition AD := []P ~> <> P.
Definition A5 := <>s P ~> []s <>s P.
Definition GL := ([] ([] P ~> P)) ~> [] P.

Compute reverseThisList (nodeToNat (makeMatrix ((P \/ ~P)))).

Compute makeComputeTable ((P \/ ~P)).

Compute makeComputeTable (A5).

Definition k1 := ([](P  ~> Q)) ~> ((<> P) ~> <> Q).
Definition k1s := ([](P  ~> Q)) ~> ((<>s P) ~> <>s Q).

Definition k2 := (<>(P \/ Q)) ~> ((<> P) \/ <> Q).
Definition k2s := (<>s(P \/ Q)) ~> ((<>s P) \/ <>s Q).

Definition k3 := ((<> P) ~> [] Q) ~> [] (P ~> Q).
Definition k3s := ((<>s P) ~> [] Q) ~> [] (P ~> Q).

Definition k4 := (~ <> (P /\ ~ P)).
Definition k4s := (~ <>s (P /\ ~ P)).

Compute reverseThisList (nodeToNat (makeMatrix (k2))).

Compute List.length (proj_r (makeComputeTable (k1s))).

Compute makeCheckAllModels GL false true.


(****************)
(*   CODE EXT   *)
(****************)


Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].


Recursive Extraction
  makeCheckAllModels makeMatrix makeComputeTable makeThisRn existb forallnegb getNodeA.

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


Fixpoint logicbt
  (l : list (pair LF nat))
  (t : backtree (pair LF nat))
  (V : list (pair LF nat))
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
        | <> B =>
            let candidates := getCandidatesUn dia_def v in
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
        | B <~> C =>
            let candidates := getCandidatesBin bimpl_def v in
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

Fixpoint genSynTree (A : LF)
  :=
  match A with
  | Atom _ => sun A sleaf
  | ~ B => sun A (genSynTree B)
  | [] B => sun A (genSynTree B)
  | <> B => sun A (genSynTree B)
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
  | B <~> C =>
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
  | <> B => 
      let vB := applyTo v B 404 eqb_lf in
      let ndvals := applyTo dia_def vB nil Nat.eqb in
      gensemtree A ndvals v toExpand
  | B ~> C =>
      let vB := applyTo v B 404 eqb_lf in
      let vC := applyTo v C 404 eqb_lf in
      let ndvals := applyTo impl_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  | B <~> C =>
      let vB := applyTo v B 404 eqb_lf in
      let vC := applyTo v C 404 eqb_lf in
      let ndvals := applyTo bimpl_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  | B /\ C =>
      let vB := applyTo v B 404 eqb_lf in
      let vC := applyTo v C 404 eqb_lf in
      let ndvals := applyTo conj_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  | B \/ C =>
      let vB := applyTo v B 404 eqb_lf in
      let vC := applyTo v C 404 eqb_lf in
      let ndvals := applyTo disj_def (vB, vC) nil cmp_pair in
      gensemtree A ndvals v toExpand
  end.

Definition findcm (A : LF) (atomval : list (pair LF nat)) :=
  depfirst
    A
    vF
    atomval
    1000
    tV
    tS5
    arrows
    nil
    nil
    logicsemt
    eqb_lf
    leb_lf
    length_lf
    split_lf
    logicbt
    iscons
    genSynTree.

Check tS5.

(** TESTES ***)

Definition r0 := Atom "r0".
Definition r1 := Atom "r1".
Definition r2 := Atom "r2".
Definition r3 := Atom "r3".
Definition r4 := Atom "r4".
Definition r5 := Atom "r5".

Compute arrows.

Definition tV := [vF; vt; vf; vT].

Compute
  back2back
    (<>P ~> []<>P)
    tV
    [[ ((<>P ~> []<>P), vT); (P, 0)]]
    tS5 nil nil
    eqb_lf leb_lf length_lf split_lf logicbt iscons.


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


Definition s4_ipc_5 := (((((([](([](([] p1) ~> ((((([] p1) /\ ([] p2)) /\ ([] p3)) /\ ([] p4)) /\ ([] p5)))) ~> (p1 /\ ~ p1))) /\ ([](([](([] p2) ~> ((((([] p1) /\ ([] p2)) /\ ([] p3)) /\ ([] p4)) /\ ([] p5)))) ~> (p1 /\ ~ p1)))) /\ (p1 \/ ~p1)) /\ ([](([](([] p4) ~> ((((([] p1) /\ ([] p2)) /\ ([] p3)) /\ ([] p4)) /\ ([] p5)))) ~> (p1 /\ ~ p1)))) /\ ([](([](([] p5) ~> ((((([] p1) /\ ([] p2)) /\ ([] p3)) /\ ([] p4)) /\ ([] p5)))) ~> (p1 /\ ~ p1)))) ~> (p1 /\ ~ p1)).

Definition s4_ipc_4 := ((((([](([](([] p1) ~> (((([] p1) /\ ([] p2)) /\ ([] p3)) /\ ([] p4)))) ~> (p1 /\ ~ p1))) /\ (p1 \/ ~ p1)) /\ ([](([](([] p3) ~> (((([] p1) /\ ([] p2)) /\ ([] p3)) /\ ([] p4)))) ~> (p1 /\ ~ p1)))) /\ ([](([](([] p4) ~> (((([] p1) /\ ([] p2)) /\ ([] p3)) /\ ([] p4)))) ~> (p1 /\ ~ p1)))) ~> (p1 /\ ~ p1)).

Compute findcm (~(s4_ipc_5)) [(p1, 0); (p2, 0); (p3, 0); (p4, 0); (p5, 0)].

