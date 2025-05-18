Require Import Arith.
Require Import List.
Import ListNotations.

(**

Implementação da operação power (de powerset): _power_ recebe uma lista de elementos tipo X (genérico) e retorna a lista de todas as sublistas.

* Exemplo

Entrada: A B C D

    A 1
    B 2
    C 3
    D 4

    AB 2
    AC 3
    AD 4
    BC 3
    BD 4
    CD 4

    ABC 3
    ABD 4
    ACD 4
    BCD 4

    ABCD 4

 **)


Inductive indexed (X : Type) :=
| i (n : nat) (v : X).

Fixpoint getValueAtPosition {X : Type} (l : list X) (p : nat) (default: X) :=
  match l with
  | nil => default
  | h::tl => if (beq_nat p 0) then h else getValueAtPosition tl (p-1) default
  end.

Fixpoint combine {X : Type} (k : nat) (v : list X) (l : list X) (startValue : nat) (default: X) :=
  match k with
  | O => nil
  | S n => (i _ (startValue+1) (v++(getValueAtPosition l startValue default)::nil))
             :: combine n v l (startValue + 1) default
  end.

Definition getIndex {X : Type} (el : indexed X) :=
  match el with
  | i _ k _ => k
  end.

Definition getValue {X : Type} (el : indexed X) :=
  match el with
  | i _ _ v => v
  end.

Fixpoint break {X : Type} (l : list X) (startIndex : nat):=
  match l with
  | nil => nil
  | h::tl => (i _ startIndex (h::nil))::(break tl (startIndex + 1))
  end.

Fixpoint combinator {X : Type} (li : list (indexed (list X))) (l : list X) (default : X) :=
  match li with
  | nil => nil
  | h::tl =>
      ((combine ((length l)-(getIndex h)) (getValue h) l (getIndex h) default))++(combinator tl l default)
  end.

Fixpoint select {X : Type} (li : list (indexed (list X))) (size : nat) :=
  match li with
  | nil => nil
  | h::tl => if ((getIndex h) <? size) then h :: (select tl size) else (select tl size)
  end.

Fixpoint power_r {X : Type} (li : list (indexed (list X))) (l : list X) (default : X) (i : nat) :=
  match i with
  | O => nil
  | S k =>
      let next := (combinator (select li (length l)) l default) in
      (next) ++ (power_r (select next (length l)) l default k)
  end.

Fixpoint getAllValuesFromIndexedList {X : Type} (l : list (indexed (list X))) : list (list X) :=
  match l with
  | nil => nil
  | h::tl => (getValue h)::(getAllValuesFromIndexedList tl)
  end.

Definition power {X : Type} (l : list X) (default : X) :=
  let b := break l 1 in
  getAllValuesFromIndexedList (b++(power_r b l default (length l))).
