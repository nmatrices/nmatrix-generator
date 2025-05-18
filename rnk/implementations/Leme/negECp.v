
(**

* Ecumenical propositional with signature {~c , ~i , \/ , /\ , ->c , ->i, @ }, where @ A means "A has a classical proof".

 ***)

Require Import Forest.
Require Import List.
Require Import String.
Require Import Arith.
Require Import rnk.
Require Import Model.
Import ListNotations.

Fixpoint fold
  {X Y : Type}
  (f : X -> Y -> Y)
  (l : list X)
  (b : Y)
  : Y :=
  match l with
  | nil => b
  | h::tl =>
      f h (fold f tl b)
  end.

Arguments Pair {X} {Y}.

Notation "( A ; B )" := (Pair A B).

Definition vT := 5.
Definition vTc := 4.
Definition vt := 3.
Definition vu := 2.
Definition vU := 1.
Definition vF := 0.

(** Language specifics **)

Inductive eLF :=
| Atom : string -> eLF
| NegI : eLF -> eLF
| NegC : eLF -> eLF
| ProofC : eLF -> eLF
| Conj : eLF -> eLF -> eLF
| Disj : eLF -> eLF -> eLF
| ImplI : eLF -> eLF -> eLF
| ImplC : eLF -> eLF -> eLF.

Notation "! A" := (Atom A) (at level 10).
Notation "~i A" := (NegI A) (at level 10).
Notation "~c A" := (NegC A) (at level 10).
Notation "@ A" := (ProofC A) (at level 10).
Notation "A /\ B" := (Conj A B).
Notation "A \/ B" := (Disj A B).
Notation "A ->i B" := (ImplI A B) (at level 90).
Notation "A ->c B" := (ImplC A B) (at level 90).

Definition P := Atom "P".
Definition Q := Atom "Q".
Definition R := Atom "R".
Definition U := Atom "U".

Fixpoint eqb_elf (A : eLF) (B : eLF) :=
  match A with
  | Atom P => match B with
              | Atom Q => if (String.eqb P Q) then true
                          else false
              | _ => false
              end
  | ~i P => match B with
           | ~i Q => eqb_elf P Q
           | _ => false
           end
  | ~c P => match B with
            | ~c Q => eqb_elf P Q
            | _ => false
            end
  | @ P => match B with
            | @ Q => eqb_elf P Q
            | _ => false
            end
  | P /\ Q => match B with
              | R /\ T => andb (eqb_elf P R) (eqb_elf Q T)
              | _ => false
              end
  | P ->i Q => match B with
               | R ->i T => andb (eqb_elf P R) (eqb_elf Q T)
               | _ => false
               end
  | P \/ Q => match B with
               | R \/ T => andb (eqb_elf P R) (eqb_elf Q T)
               | _ => false
               end
  | P ->c Q => match B with
               | R ->c T => andb (eqb_elf P R) (eqb_elf Q T)
               | _ => false
               end
  end.

Fixpoint length_elf (A : eLF) :=
  match A with
  | Atom P => 0
  | ~i P => 1 + length_elf P
  | ~c P => 1 + length_elf P                         
  | @ P => 1 + length_elf P                         
  | P /\ Q => 1 + length_elf P + length_elf Q
  | P ->i Q => 1 + length_elf P + length_elf Q
  | P \/ Q => 1 + length_elf P + length_elf Q
  | P ->c Q => 1 + length_elf P + length_elf Q
  end.

Definition leb_elf (A : eLF) (B : eLF) :=
  Nat.leb (length_elf A) (length_elf B).

Definition geb_elf (A : eLF) (B : eLF) :=
  negb (leb (length_elf A) (length_elf B)).

Fixpoint split_elf (L : eLF) :=
  match L with
  | Atom A => (Atom A)::nil
  | ~i A => (~i A)::(split_elf A)
  | ~c A => (~c A)::(split_elf A)
  | @ A => (@ A)::(split_elf A)
  | A /\ B => (A /\ B)::((split_elf A)++(split_elf B))
  | A ->i B => (A ->i B)::((split_elf A)++(split_elf B))
  | A \/ B => (A \/ B)::((split_elf A)++(split_elf B))
  | A ->c B => (A ->c B)::((split_elf A)++(split_elf B))
  end.

(* Truth-table definitions *)

Definition ECp_negI_def :=
  [
    (vF; [vU; vT]);
    (vU; [vU; vT]);
    (vu; [vU; vT]);
    (vt; [vF]);
    (vTc; [vF]);
    (vT; [vF])
  ].

Definition ECp_proofC_def :=
  [
    (vF; [vF; vu; vt]);
    (vU; [vF; vu; vt]);
    (vu; [vF; vu; vt]);
    (vt; [vT]);
    (vTc; [vU; vT]);
    (vT; [vT])
  ].
(*
Definition ECp_proofCc_def :=
  [
    (vF; [vF; vu; vt]);
    (vU; [vF; vu; vt]);
    (vu; [vF; vu; vt]);
    (vt; [vU; vT]);
    (vT; [vU; vT])
  ].
*)
Definition ECp_negC_def :=
  [
    (vF; [vTc]);
    (vU; [vTc]);
    (vu; [vTc]);
    (vt; [vF]);
    (vTc; [vF]);
    (vT; [vF])
  ].

Definition ECp_conj_def :=
  [
    ((vF; vF); [vF]);
    ((vF; vU); [vF]);
    ((vF; vu); [vF]);
    ((vF; vt); [vF]);
    ((vF; vTc); [vF]);
    ((vF; vT); [vF]);
    ((vU; vF); [vF]);
    ((vU; vU); [vF]);
    ((vU; vu); [vF]);
    ((vU; vt); [vF]);
    ((vU; vTc); [vF]);
    ((vU; vT); [vF]);
    ((vu; vF); [vF]);
    ((vu; vU); [vF]);
    ((vu; vu); [vF]);
    ((vu; vt); [vF]);
    ((vu; vTc); [vF]);
    ((vu; vT); [vF]);
    ((vt; vF); [vF]);
    ((vt; vU); [vF]);
    ((vt; vu); [vF]);
    ((vt; vt); [vT]);
    ((vt; vTc); [vT]);
    ((vt; vT); [vT]);
    ((vTc; vF); [vF]);
    ((vTc; vU); [vF]);
    ((vTc; vu); [vF]);
    ((vTc; vt); [vT]);
    ((vTc; vTc); [vT]);
    ((vTc; vT); [vT]);
    ((vT; vF); [vF]);
    ((vT; vU); [vF]);
    ((vT; vu); [vF]);
    ((vT; vt); [vT]);
    ((vT; vTc); [vT]);
    ((vT; vT); [vT])
  ].

Definition ECp_implI_def :=
  [
    ((vF; vF); [vU; vT]);
    ((vF; vU); [vU; vT]);
    ((vF; vu); [vU; vT]);
    ((vF; vt); [vT]);
    ((vF; vTc); [vT]);
    ((vF; vT); [vT]);
    ((vU; vF); [vU; vT]);
    ((vU; vU); [vU; vT]);
    ((vU; vu); [vU; vT]);
    ((vU; vt); [vT]);
    ((vU; vTc); [vT]);
    ((vU; vT); [vT]);
    ((vu; vF); [vU; vT]);
    ((vu; vU); [vU; vT]);
    ((vu; vu); [vU; vT]);
    ((vu; vt); [vT]);
    ((vu; vTc); [vT]);
    ((vu; vT); [vT]);
    ((vt; vF); [vF]);
    ((vt; vU); [vF]);
    ((vt; vu); [vF]);
    ((vt; vt); [vT]);
    ((vt; vTc); [vT]);
    ((vt; vT); [vT]);
    ((vTc; vF); [vF]);
    ((vTc; vU); [vF]);
    ((vTc; vu); [vF]);
    ((vTc; vt); [vT]);
    ((vTc; vTc); [vT]);
    ((vTc; vT); [vT]);
    ((vT; vF); [vF]);
    ((vT; vU); [vF]);
    ((vT; vu); [vF]);
    ((vT; vt); [vT]);
    ((vT; vTc); [vT]);
    ((vT; vT); [vT])
  ].

Definition ECp_disj_def :=
  [
    ((vF; vF); [vF]);
    ((vF; vU); [vF]);
    ((vF; vu); [vF]);
    ((vF; vt); [vT]);
    ((vF; vTc); [vT]);
    ((vF; vT); [vT]);
    ((vU; vF); [vF]);
    ((vU; vU); [vF]);
    ((vU; vu); [vF]);
    ((vU; vt); [vT]);
    ((vU; vTc); [vT]);
    ((vU; vT); [vT]);
    ((vu; vF); [vF]);
    ((vu; vU); [vF]);
    ((vu; vu); [vF]);
    ((vu; vt); [vT]);
    ((vu; vTc); [vT]);
    ((vu; vT); [vT]);
    ((vt; vF); [vT]);
    ((vt; vU); [vT]);
    ((vt; vu); [vT]);
    ((vt; vt); [vT]);
    ((vt; vTc); [vT]);
    ((vt; vT); [vT]);
    ((vTc; vF); [vT]);
    ((vTc; vU); [vT]);
    ((vTc; vu); [vT]);
    ((vTc; vt); [vT]);
    ((vTc; vTc); [vT]);
    ((vTc; vT); [vT]);
    ((vT; vF); [vT]);
    ((vT; vU); [vT]);
    ((vT; vu); [vT]);
    ((vT; vt); [vT]);
    ((vT; vTc); [vT]);
    ((vT; vT); [vT])
  ].

Definition ECp_implC_def :=
  [
    ((vF; vF); [vTc]);
    ((vF; vU); [vTc]);
    ((vF; vu); [vTc]);
    ((vF; vt); [vTc]);
    ((vF; vTc); [vTc]);
    ((vF; vT); [vTc]);
    ((vU; vF); [vTc]);
    ((vU; vU); [vTc]);
    ((vU; vu); [vTc]);
    ((vU; vt); [vTc]);
    ((vU; vTc); [vTc]);
    ((vU; vT); [vTc]);
    ((vu; vF); [vTc]);
    ((vu; vU); [vTc]);
    ((vu; vu); [vTc]);
    ((vu; vt); [vTc]);
    ((vu; vT); [vTc]);
    ((vt; vF); [vF]);
    ((vt; vU); [vF]);
    ((vt; vu); [vF]);
    ((vt; vt); [vTc]);
    ((vt; vTc); [vTc]);
    ((vt; vT); [vTc]);
    ((vTc; vF); [vF]);
    ((vTc; vU); [vF]);
    ((vTc; vu); [vF]);
    ((vTc; vt); [vTc]);
    ((vTc; vt); [vTc]);
    ((vTc; vT); [vTc]);
    ((vT; vF); [vF]);
    ((vT; vU); [vF]);
    ((vT; vu); [vF]);
    ((vT; vt); [vTc]);
    ((vTc; vt); [vTc]);
    ((vT; vT); [vTc])
  ].

Definition negECp
  (B A : eLF)
  (partialV : btree eLF)
  (V : list nat)
  (allVs : list (btree eLF))
  : btree eLF
  :=
  match A with
  | Atom B => Leaf _ true
  | NegI B =>
      unary_op A B partialV 0 ECp_negI_def eqb_elf
  | NegC B =>
      unary_op A B partialV 0 ECp_negC_def eqb_elf
  | ProofC B =>
      unary_op A B partialV 0 ECp_proofC_def eqb_elf
  | ImplI B C =>
      bin_op A B C partialV 0 0 ECp_implI_def eqb_elf
  | ImplC B C =>
      bin_op A B C partialV 0 0 ECp_implC_def eqb_elf
  | Disj B C =>
      bin_op A B C partialV 0 0 ECp_disj_def eqb_elf
  | Conj B C =>
      bin_op A B C partialV 0 0 ECp_conj_def eqb_elf
  end.

Definition arrows :=
  [
    (vU, [[vF]]);
    (vt, [[vT]]);
    (vu, [[vT; vF]])
  ].

Definition monoto (A : eLF) := Some (A, [vt; vT]).

Definition circleF (A : eLF) :=
  match A with
  | @ _ => Some (A, [vF])
  | _ => None
  end.

Definition tnegECp :=
  [
    ((vT, [monoto]), true);
    ((vt, [monoto]), true);
    ((vF, [circleF]), true)
  ].

(***********)

(**** Definitions for rnk. ********)
(*************)

(**)

Definition makeMatrix (A : eLF) :=
  makeIt
    A
    [vF;vT]
    negECp
    eqb_elf
    leb_elf
    length_elf
    split_elf.

Definition makeAllRn
  (A : eLF)
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
    404
    [vt;vTc;vT]
    [Transitive;Reflexive]
    smallest lazymode tnegECp
.

Definition makeThisRn
  (w : nat)
  (A : eLF)
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
    404
    [vt;vTc;vT]
    [Transitive;Reflexive]
    smallest lazymode tnegECp
.

(***)

(* Model checking *)

Fixpoint Val
  (A : eLF)
  (model : list (node eLF))
  (w : nat) :=
  let accW := getAllAccessedWorld model w in
  match A with
  | ! _ =>
      checkValInW A w model eqb_elf
  | ~i p =>
      forallnegb (map (Val p model) accW)
  | ~c p =>
      negb (Val p model w)
  | @ p =>
      Model.forallb
        (map
           (fun w' =>
              let accW' := getAllAccessedWorld model w' in
              Model.existb
                (map
                   (fun w'' =>
                      Val p model w''
                   )
                   accW'
           ))
           accW)
  | p /\ q =>
      andb (Val p model w) (Val q model w)
  | p \/ q =>
      orb (Val p model w) (Val q model w)
  | p ->c q =>
      orb (negb (Val p model w)) (Val q model w)
  | p ->i q =>
      Model.forallb (
          map
            (fun k =>
               if (Val p model k) then
                 (Val q model k)
               else true)
            accW)
  end.

Definition makeCheckAllModels
  (A : eLF)
  (smallest lazymode : bool)
  :=
  checkAllModels
    A
    (makeMatrix A)
    eqb_elf leb_elf geb_elf
    split_elf
    arrows
    Val
    404
    (makeAllRn A smallest lazymode)
    [vt;vTc;vT]
    tnegECp
.

Definition makeCheckThisModel
  (w : nat)
  (A : eLF)
  (smallest lazymode : bool)
  :=
  checkAllModels
    A
    (makeMatrix A)
    eqb_elf leb_elf geb_elf
    split_elf
    arrows
    Val
    404
    (makeThisRn w A smallest lazymode)
    [vt;vTc;vT]
    tnegECp
.

Definition makeRestrictionSteps
  (A : eLF) :=
  restrictionSteps
    A
    (makeMatrix A)
    eqb_elf
    leb_elf
    geb_elf
    split_elf
    arrows
    404
    tnegECp
.

Definition makeComputeTable
  (A : eLF) :=
  let steps := makeRestrictionSteps A in
  computeTable steps.

Definition makeArrangeKM
  (A : eLF)
  (mode_all lazymode : bool)
  :=
  arrangeKM
    A
    (makeMatrix A)
    eqb_elf
    leb_elf
    geb_elf
    split_elf
    arrows
    404
    mode_all lazymode tnegECp
.

Definition truthTable (A : eLF) := makeComputeTable A.

Compute reverseThisList (nodeToNat (makeMatrix ((~i P) ->i (P ->i Q)))). 


(**

"@ A" means "A has a classical proof", or "A is a classical tautology".

 **)

(** Glivenko's theorem (double negation translation): "A" is a classical tautology iff "~ ~ A" is an intuitionistic tautology. **)


Definition g_atom := ((@ P) ->i (~i~i P)) /\ ((~i~i P) ->i (@ P)).
Definition g_bola := ((@ (@ P)) ->i (~i~i (@ P))) /\ ((~i~i (@ P)) ->i (@ (@ P))).
Definition g_negC := ((@ (~c P)) ->i (~i~i (~c P))) /\ ((~i~i (~c P)) ->i (@ (~c P))).
Definition g_negI := ((@ (~i P)) ->i (~i~i (~i P))) /\ ((~i~i (~i P)) ->i (@ (~i P))).
Definition g_conj := ((@ (P /\ Q)) ->i (~i~i (P /\ Q))) /\ ((~i~i (P /\ Q)) ->i (@ (P /\ Q))).
Definition g_disj := ((@ (P \/ Q)) ->i (~i~i (P \/ Q))) /\ ((~i~i (P \/ Q)) ->i (@ (P \/ Q))).

Definition g_disj2 := ((@ P) \/ (~i P)) ->i ((~i~i P) \/ (~i P)).
Definition g_disj3 := ((~i~i P) \/ (~i P)) ->i ((@ P) \/ (~i P)).
Definition g_disj4 := ((~i~i P) \/ (Q \/ R)) ->i ((@ P) \/ (Q \/ R)).
Definition g_disj5 := ((@ P) \/ (Q \/ R)) ->i ((~i~i P) \/ (Q \/ R)).
Definition g_disj6 := ((~i~i P) \/ (Q ->i R)) ->i ((@ P) \/ (Q ->i R)).
Definition g_disj7 := ((@ P) \/ (Q ->i R)) ->i ((~i~i P) \/ (Q ->i R)).

Definition g_disj22 := ((P) \/ @(~i P)) ->i (( P) \/ ~i~i(~i P)).
Definition g_disj23 := (( P) \/ ~i~i(~i P)) ->i ((P) \/ @(~i P)).



Definition g_implI := ((@ (P ->i Q)) ->i (~i~i (P ->i Q))) /\ ((~i~i (P ->i Q)) ->i (@ (P ->i Q))).
Definition g_implC := ((@ (P ->c Q)) ->i (~i~i (P ->c Q))) /\ ((~i~i (P ->c Q)) ->c (@ (P ->c Q))).

Compute truthTable (((~c P) ->i ~i P)).

Compute reverseThisList (nodeToNat (makeMatrix (g_disj2))).

Compute truthTable ((~c P) ->i @ (~c P)).
Compute truthTable ((@ ~c P) ->i ~c P).

(** If A is an intuitionistic tautology, then it is a classical tautology. However, if P is a classical tautology, then it may not be an intuitionistic tautology. **)

Definition i_impl_c := P ->i @ P.
Definition c_impl_i_fail := @ P ->i P.

Compute truthTable (@ P).

Compute truthTable i_impl_c.

Compute truthTable c_impl_i_fail.

(** Distributivity of @ with respect to other conectives: **)

Definition bola_distr_implC := @ (P ->c Q) ->i (@ P ->c @ Q).
Definition bola_distr_implI := @ (P ->i Q) ->i (@ P ->i @ Q).
Definition bola_distr_conj:= @ (P /\ Q) ->i (@ P /\ @ Q).
Definition bola_distr_negC := @ (~c P) ->i ~c @ P.
Definition bola_distr_negI := (~i~i (~i P)) ->i ~i ~i~i P.

Definition bola_distr_disj_fail := (@ (P \/ Q)) ->i ((@ P) \/ @ Q).

Compute truthTable bola_distr_disj_fail.

Compute truthTable ((~i~i P) ->i P).

Compute makeCheckAllModels makeMakeIt bola_distr_disj_fail true false.

(** Disjunctive property holds iff "P V Q" is an intuitionistic tautology. **)

Definition DisjProp_1 := (P \/ Q) /\ (~i P) ->i Q.
Definition DisjProp_2 := (P \/ Q) /\ (~i Q) ->i P.
Definition DisjProp_3 := (P \/ Q) /\ @ (~c P) ->i Q.
Definition DisjProp_4 := (P \/ Q) /\ @ (~c Q) ->i P.

Definition DisjProp_c_fail1 := @ (P \/ Q) /\ (~i P) ->i Q.
Definition DisjProp_c_fail2 := @ (P \/ Q) /\ (~i Q) ->i P.
Definition DisjProp_c_fail3 := ((@ (P \/ Q)) /\ (@ (~c P))) ->i Q.
Definition DisjProp_c_fail3dn := ((~i~i (P \/ Q)) /\ (~i~i (~c P))) ->i Q.
Definition DisjProp_c_fail4 := @ (P \/ Q) /\ @ (~c Q) ->i P.

Compute truthTable DisjProp_c_fail4.

(******** MODUS PONENS *********)

(* valid MP *)

Definition MP1 := P /\ @ (P ->c Q) ->c @ Q.
Definition MP2 := P /\ @ (P ->c Q) ->i @ Q.
Definition MP3 := P /\ (P ->c Q) ->c Q.
Definition MP4 := P /\ (P ->c Q) ->i Q.

Compute truthTable (MP1 /\ MP2 /\ MP3 /\ MP4).

(* invalid MP *)

Definition invMP1 := P /\ @ (P ->c Q) ->i Q.
Definition invMP2 := P /\ @ (P ->c Q) ->c Q.
Definition invMP3 := P /\ @ (P ->i Q) ->i Q.
Definition invMP4 := P /\ @ (P ->i Q) ->c Q.

Compute truthTable invMP1.


(******)


Compute truthTable ((@ ~c P) ->i ~c @ P).
Compute reverseThisList (nodeToNat (makeMakeIt ((@ ~c P) ->i ~c @ P))). 


(*******************)
(* CODE EXTRACTION *)
(*******************)

Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction
  makeCheckAllModels makeMakeIt makeMakeIt_otf makeComputeTable makeThisRn existb forallnegb getNodeA.
