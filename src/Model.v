(**************

Model checking.

****************)

(* Modelo extracter *)

Require Import Arith.
Require Import Coq.Arith.EqNat.
Require Import Forest.
Require Import rnk.
Require Import List.
Require Import Arith.
Import ListNotations.

Fixpoint findRowByIndex
  {X : Type}
  (matrix : list (pair nat (list X)))
  (index : nat) :=
  match matrix with
  | nil => nil
  | h::tl =>
      if Nat.eqb index (proj_l h) then
        proj_r h
      else
        findRowByIndex tl index
  end.

Fixpoint checkValInW
  {X : Type}
  (A : X)
  (w : nat)
  (l : list (node X))
  (cmp : X -> X -> bool)
  :=
  match l with
  | nil => false
  | h::tl =>
      match h with
      | Node sf k =>
          if Nat.eqb w k then
            match sf with
            | sign b L =>
                if (cmp A L) then b
                else checkValInW A w tl cmp
            end
          else checkValInW A w tl cmp
      | _ => checkValInW A w tl cmp
      end
  end.

Fixpoint getAllAccessedWorld
  {X : Type}
  (l : list (node X))
  (w : nat)
  :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | Rel _ k j =>
          if Nat.eqb w k then
            j::(getAllAccessedWorld tl w)
          else
            getAllAccessedWorld tl w
      | _ => getAllAccessedWorld tl w
      end
  end.

Fixpoint checkAll
  {X : Type}
  (A : X)
  (l : list nat)
  (lN : list (node X))
  (cmp : X -> X -> bool)
  :=
  match l with
  | nil => true
  | h::tl =>
      andb
        (checkValInW A h lN cmp)
        (checkAll A tl lN cmp)
  end.

Fixpoint checkAllFalse
  {X : Type}
  (A : X)
  (l : list nat)
  (lN : list (node X))
  (cmp : X -> X -> bool)
  :=
  match l with
  | nil => true
  | h::tl =>
      andb
        (negb (checkValInW A h lN cmp))
        (negb (checkAllFalse A tl lN cmp))
  end.

Fixpoint getAllTrueIn
  {X : Type}
  (A : X)
  (l : list nat)
  (ekm: list (node X))
  (cmp : X -> X -> bool)
  :=
  match l with
  | nil => nil
  | h::tl =>
      if checkValInW A h ekm cmp then
        h::(getAllTrueIn A tl ekm cmp)
      else
        getAllTrueIn A tl ekm cmp
  end.

Fixpoint forallb (l : list bool) :=
  match l with
  | nil => true
  | h::tl =>
      andb h (forallb tl)
  end.

Fixpoint existb (l : list bool) :=
  match l with
  | nil => false
  | h::tl =>
      orb h (existb tl)
  end.

Fixpoint forallnegb (l : list bool) :=
  match l with
  | nil => true
  | h::tl =>
      andb (negb h) (forallnegb tl)
  end.

Fixpoint valIsHeredit_aux
  {X : Type}
  (A : X)
  (accW : list nat)
  (ekm : list (node X))
  (cmp : X -> X -> bool)
  :=
  match accW with
  | nil => true
  | h::tl =>
      andb
        (checkValInW A h ekm cmp)
        (valIsHeredit_aux A tl ekm cmp)
  end.
  
Fixpoint valIsHeredit
  {X : Type}
  (atomicNodes : list (node X))
  (ekm : list (node X))
  (cmp : X -> X -> bool)
  :=
  match atomicNodes with
  | nil => true
  | h::tl =>
      match h with
      | Node Sf w =>
          match Sf with
          | sign b A =>
              if b then
                let accW := getAllAccessedWorld ekm w in
                andb
                  (valIsHeredit_aux A accW ekm cmp)
                  (valIsHeredit tl ekm cmp)
              else
                valIsHeredit tl ekm cmp
          end
      | _ => valIsHeredit tl ekm cmp
      end
  end.

Fixpoint closeToH_aux2
  {X : Type}
  (A : X)
  (accW : list nat)
  (ekm : list (node X))
  :=
  match accW with
  | nil => nil
  | h::tl => (Node (sign true A) h)::(closeToH_aux2 A tl ekm)
  end.
  
Fixpoint closeToH_aux1
  {X : Type}
  (atomics : list (node X))
  (ekm : list (node X))
  :=
  match atomics with
  | nil => nil
  | h::tl =>
      match h with
      | Node Sf w =>
          match Sf with
          | sign b A =>
              if b then
                let accW := getAllAccessedWorld ekm w in
                let newNodes := closeToH_aux2 A accW ekm in
                newNodes++(closeToH_aux1 tl ekm)
              else
                (Node Sf w)::closeToH_aux1 tl ekm
          end
      | _ => closeToH_aux1 tl ekm
      end
  end.

(*******************************)

Fixpoint checkAllModels_aux3
  {X : Type}
  (subA : list X)
  (root : nat)
  (model : list (node X))
  (Val : X -> list (node X) -> nat -> bool)
  (valuation : list nat)
  (D : list nat)
  :=
  match subA, valuation with
  | A::tl1, vA::tl2  =>
      let VA := Val A model root in
      if andb (isElementInList vA D Nat.eqb) VA then
        true::(checkAllModels_aux3 tl1 root model Val tl2 D)
      else
        if andb (negb (isElementInList vA D Nat.eqb)) (negb VA) then
          true::(checkAllModels_aux3 tl1 root model Val tl2 D)
        else
          false::(checkAllModels_aux3 tl1 root model Val tl2 D)
  | _, _ => nil
  end.

Fixpoint checkAllModels_aux
  {X : Type}
  (matrix : list (pair nat (list nat)))
  (subA : list X)
  (l : list (pair nat (pair (list (node X)) (list nat))))
  (Val : X -> list (node X) -> nat -> bool)
  (D : list nat)
  :=
  match l with
  | nil => nil
  | h::tl =>
      let root := proj_l h in
      let model := proj_l (proj_r h) in
      let valuation := findRowByIndex matrix root in
      (root, (checkAllModels_aux3 subA root model Val valuation D))
        ::(checkAllModels_aux matrix subA tl Val D)
  end.

Fixpoint checkAllModels_aux2
  (matrix : list (pair nat (list nat)))
  (models_res : list (pair nat (list bool)))
  :=
  match models_res with
  | h2::tl2 =>
      let index := proj_l h2 in
      let row := findRowByIndex matrix index in
      (index, (row, (proj_r h2)))::(checkAllModels_aux2 matrix tl2)
  | nil => nil
  end.

Definition checkAllModels
  {X : Type}
  (A : X)
  (M : list (list (Forest.node X)))
  (*(V : list nat)
  (logic : X -> X -> btree X -> list nat -> list (btree X) -> btree X)*)
  (eqb_X leb_X geb_X : X -> X -> bool)
  (*(length_X : X -> nat)*)
  (split : X -> list X)
  (arrows : list (pair nat (list (list nat))))
  (Val : X -> list (node X) -> nat -> bool)
  (default : nat)
  (models : list (pair nat (pair (list (node X)) (list nat))))
  (D : list nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  let steps :=
    restrictionSteps
      A
      M
      (*V
      logic*)
      eqb_X
      leb_X
      geb_X
      (*length_X*)
      split
      arrows
      default trules
  in
  let table := computeTable steps in
  let matrix := proj_r table in
  let subA := proj_l table in
  let models_res := checkAllModels_aux matrix subA models Val D in
  (rearrangeModels models, (subA, (checkAllModels_aux2 matrix models_res))).


