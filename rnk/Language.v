(** Modal language specifics **)

Require Import Forest.
Require Import List.
Require Import String.
Require Import Arith.
Require Import rnk.
Require Import Model.
Import ListNotations.

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
Notation "A --> B" := (Impl A B) (at level 90).
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
  | P --> Q => match B with
              | R --> T => andb (eqb_lf P R) (eqb_lf Q T)
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
  | P --> Q => 1 + length_lf P + length_lf Q
  | P /\ Q => 1 + length_lf P + length_lf Q
  | P \/ Q => 1 + length_lf P + length_lf Q
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
  | A --> B => (A --> B)::((split_lf A)++(split_lf B))
  | A /\ B => (A /\ B)::((split_lf A)++(split_lf B))
  | A \/ B => (A \/ B)::((split_lf A)++(split_lf B))
  end.


Require Coq.extraction.Extraction.

Require Coq.extraction.ExtrOcamlString.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction
   eqb_lf leb_lf geb_lf split_lf.

