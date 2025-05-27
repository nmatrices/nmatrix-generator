(* Add LoadPath "../" as Main. *)

Require Import Forest.
Require Import PowerSet.
Require Import List.
Require Import String.
Require Import Arith.
Import ListNotations.

Arguments Pair {X} {Y}.

Notation "( A , B )" := (Pair A B).

Inductive Target (X : Type) :=
| Some : X -> Target X
| None : Target X.

Arguments Some {X}.
Arguments None {X}.

Fixpoint applyTo
  {X Y : Type}
  (f : list (pair X Y))
  (n : X)
  (undef : Y)
  (cmp_x : X -> X -> bool)
  :=
  match f with
  | nil => undef
  | (x, y)::tl =>
      if cmp_x n x then y
      else
        applyTo tl n undef cmp_x
  end.

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

Definition isEmpty {X : Type} (l : list X) :=
  match l with
  | nil => true
  | _ => false
  end.

Fixpoint isElementInList
  {X : Type}
  (n : X)
  (l : list X)
  (cmp : X -> X -> bool)
  :=
  match l with
  | nil => false
  | h::tl =>
      if cmp n h then true
      else
        isElementInList n tl cmp
  end.

(*
Fixpoint validate
  {X : Type}
  (trules : list (pair nat (list nat)))
  (eqb_X : X -> X -> bool)
  (v w : list (pair X nat))
  :=
  match v with
  | nil => true
  | (A, vA)::tl =>
      let targets := applyTo trules vA nil Nat.eqb in
      if negb (isEmpty targets) then
        let wA := applyTo w A 404 eqb_X in
        if
          andb
            (negb (Nat.eqb wA 404))
            (negb (isElementInList wA targets Nat.eqb)) then
          false
        else
          validate trules eqb_X tl w
      else
        validate trules eqb_X tl w
  end.
 *)

Fixpoint validate_aux
  {X : Type}
  (A : X)
  (transf : list (X -> Target (pair X (list nat))))
  (eqb_X : X -> X -> bool)
  (w : list (pair X nat))
  :=
  match transf with
  | nil => true
  | f::tl =>
      let target := f A in
      match target with
      | None =>
          true
      | Some (B, targets) =>
          let wB := applyTo w B 8 eqb_X in
          if
            andb
              (negb (Nat.eqb wB 8))
              (negb (isElementInList wB targets Nat.eqb)) then
            false
          else
            validate_aux A tl eqb_X w
      end
  end.
  
Fixpoint validate
  {X : Type}
  (trules : list (pair nat (list (X -> Target (pair X (list nat))))))
  (eqb_X : X -> X -> bool)
  (v w : list (pair X nat))
  :=
  match v with
  | nil => true
  | (A, vA)::tl =>
      let transf := applyTo trules vA nil Nat.eqb in
      if negb (isEmpty transf) then
        if validate_aux A transf eqb_X w then
          validate trules eqb_X tl w
        else
          false
      else
        validate trules eqb_X tl w
  end.


Inductive Frame :=
| Reflexive :  Frame
| Transitive : Frame
| Symmetry : Frame.

Definition eqb_frame (f1 f2 : Frame) :=
  match f1,f2 with
  | Reflexive, Reflexive => true
  | Transitive, Transitive => true
  | Symmetry, Symmetry => true
  | _, _ => false
  end.

Definition Refl (constraints : list Frame) :=
  isElementInList Reflexive constraints eqb_frame.
Definition Trans (constraints : list Frame) :=
  isElementInList Transitive constraints eqb_frame.
Definition Sym (constraints : list Frame) :=
  isElementInList Symmetry constraints eqb_frame.

Compute isElementInList Reflexive [Transitive; Reflexive] eqb_frame.

Fixpoint findVal
  {X : Type}
  (A : X)
  (v : list (node X))
  (eqb_X : X -> X -> bool)
  (default : nat) :=
  match v with
  | nil => default
  | h::tl =>
      match h with
      | Node _ val B =>
          if eqb_X A B then val
          else findVal A tl eqb_X default
      end
  end.

Fixpoint isCompatible
  {X : Type}
  (v1 v2 v1c v2c : list (node X))
  (cmp2 cmp3 : pair X nat -> list (Forest.node X) -> list (Forest.node X) -> bool)
  :=
  match v1,v2 with
  | h1::tl1, h2::tl2 =>
      match h1 with
      | Node _ val1 A =>
          if cmp2 (A, val1) v1c v2c then
            match h2 with
            | Node _ val2 B =>
                if cmp3 (B, val2) v1c v2c then
                  isCompatible tl1 tl2 v1c v2c cmp2 cmp3
                else
                  false
            end
          else
            isCompatible tl1 tl2 v1c v2c cmp2 cmp3
      end
  | _, _ => true
  end.

Fixpoint nodeToPair {X : Type} (l : list (Forest.node X)) :=
  match l with
  | nil => nil
  | (Forest.Node _ v A)::tl => (A, v)::(nodeToPair tl)
  end.

(** This auxiliar function return every line id in val that validate cval **)
Fixpoint restriction_aux2_v2
  {X : Type}
  (A : X)
  (val : (list (pair nat (list (node X)))))
  (cval : list (node X))
  (root target : nat)
  (eqb_X : X -> X -> bool)
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match val with
  | nil => nil
  | h::tl =>
      (*let trules' := map (fun x => proj_l x) (filter (fun x => proj_r x) trules) in*)
      let trules' := map (fun x => proj_l x) (filter (fun x => negb (proj_r x)) trules) in
      let index := proj_l h in
      let w := nodeToPair (proj_r h) in
      let wA := applyTo w A default eqb_X in
      if Nat.eqb wA target then
        let compatible := (* isCompatible cval vals cval vals cmp2 cmp3 *)
         (* andb 
            (validate lR eqb_X (nodeToPair cval) (nodeToPair cval))*)
            (validate trules' eqb_X (nodeToPair cval) w)
        in
        if compatible then
          index::
            (restriction_aux2_v2 A tl cval root target  eqb_X default trules)
        else
          restriction_aux2_v2 A tl cval root target eqb_X default trules
      else
        restriction_aux2_v2 A tl cval root target eqb_X default trules
  end.

Fixpoint restriction_aux3_v2
  {X : Type}
  (A : X)
  (val : (list (pair nat (list (node X)))))
  (cpcval : list (node X))
  (root : nat)
  (childs : list (list nat))
  (eqb_X : X -> X -> bool)
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match childs with
  | nil => nil
  | targets::tl =>
      let new :=
        map
        (fun target => (target, (restriction_aux2_v2
           A val cpcval
           root target
           eqb_X
           default trules)))
      targets in    
      new::(restriction_aux3_v2 A val cpcval root tl eqb_X default trules)
  end.

Check (2, 2).

Compute fold (fun x y => x++y) [[1];[2]] nil.

Fixpoint isThereAnyEmpty (l : list (pair nat (list nat))) :=
  match l with
  | nil => false
  | h::tl => if isEmpty (proj_r h) then true else isThereAnyEmpty tl
  end.

Fixpoint restriction_aux1_v2
  {X : Type}
  (val : list (pair nat (list (node X))))
  (cval cpcval : list (node X))
  (*(allValidators : list (pair X (list nat)))*)
  (root : nat)
  (childs : list (list nat))
  (eqb_X : X -> X -> bool)
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match cval with
  | nil => nil
  | h::tl =>
      match h with
      | Node _ v A =>
          if Nat.eqb v root then
            let validators :=
              restriction_aux3_v2
                A val cpcval
                root
                childs
                eqb_X
                default
                trules
            in
            let cands :=
              fold
                (fun x y => x++y)
                (filter
                   (fun cands' =>
                      negb (isThereAnyEmpty cands')
                   )
                   validators) nil in
            if isEmpty cands then
              (A, [])
                ::(restriction_aux1_v2
                     val
                     tl
                     cpcval
                     root childs eqb_X
                     default trules)
            else
              (A, cands)
                ::(restriction_aux1_v2
                     val
                     tl
                     cpcval
                     root childs eqb_X
                     default trules)
          else
            restriction_aux1_v2
              val tl cpcval root childs eqb_X default trules 
      end
  end.

(**

 (U, [F]);
 (t, [T]);
 (u, [F; T]);

 **)


Check findVal.


Fixpoint restriction_aux4_v2
  {X : Type}
  (val : list (pair nat (list (node X))))
  (vals : list (node X))
  (arrows : list (pair nat (list (list nat))))
  (eqb_X : X -> X -> bool)
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match arrows with
  | nil => nil
  | (root, childs)::tl =>
      (restriction_aux1_v2 val vals vals root childs eqb_X default trules)
        ++(restriction_aux4_v2 val vals tl eqb_X default trules)
  end.

(*Check restriction_aux4_v2.*)
(*
Fixpoint restriction_aux40_v2
  {X : Type}
  (val : list (pair nat (list (node X))))
  (vals : list (node X))
  (arrows : list (list (pair nat (list nat))))
  (eqb_X : X -> X -> bool)
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match arrows with
  | nil => nil
  | h::tl =>
      l
      
*)
(*
Fixpoint hasSomeU
  {X : Type}
  (cval : list (node X))
  (cmp : nat -> bool)
  :=
  match cval with
  | nil => false
  | h::tl =>
      match h with
      | Node _ v A =>
          if cmp v then
            true
          else
            hasSomeU tl cmp
      end
  end.
 *)


Fixpoint checkAutoRule
  {X : Type}
  (autorules : list (pair nat (list (X -> Target (pair X (list nat))))))
  (eqb_X : X -> X -> bool)
  (v cv : list (pair X nat))
  (validators : list (pair X (list (pair nat (list nat)))))
  :=
  match v with
  | nil => validators
  | (A, vA)::tl =>
      let transf := applyTo autorules vA nil Nat.eqb in
      if negb (isEmpty transf) then
        if validate_aux A transf eqb_X cv then
          checkAutoRule autorules eqb_X tl cv validators
        else
          checkAutoRule autorules eqb_X tl cv ((A, [])::validators)
      else
        checkAutoRule autorules eqb_X tl cv validators
  end.

(*
[(MATRIZ; [(n; (list (A; list))),...]) , ....]
 *)
Fixpoint restriction_aux_v2
  {X : Type}
  (val cpval : list (pair nat (list (node X))))
  (arrows : list (pair nat (list (list nat))))
  (eqb_X : X -> X -> bool)
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match val with
  | nil => nil
  | h::tl =>
      let autorules := map (fun x => proj_l x) (filter (fun x => proj_r x) trules) in
      let index := proj_l h in
      let vals := proj_r h in
      let checkAuto := checkAutoRule autorules eqb_X (nodeToPair vals) (nodeToPair vals) nil in
      if isEmpty checkAuto then
        if validate autorules eqb_X (nodeToPair vals) (nodeToPair vals) then
          let allValidators :=
            (restriction_aux4_v2 cpval vals arrows eqb_X default trules)
          in
          (index, allValidators)
            ::(restriction_aux_v2 tl cpval arrows eqb_X default trules)
        else
          restriction_aux_v2 tl cpval arrows eqb_X default trules
      else
        (index, checkAuto)
          ::(restriction_aux_v2 tl cpval arrows eqb_X default trules)
  end.

Fixpoint removeAt {X : Type} (n : nat) (l : list X) :=
  match n, l with
  | 0, nil => nil
  | 0, h::tl => tl
  | S m, nil => nil
  | S m, h::tl => h::(removeAt m tl)
  end.

Fixpoint removeAtIndexedList {X : Type} (n : nat) (l : list (pair nat X)) :=
  match l with
  | nil => nil
  | h::tl =>
      let index := proj_l h in
      if Nat.eqb index n then tl
      else h::(removeAtIndexedList n tl)
  end.

Fixpoint thereSomeNil
  {X : Type}
  (l : (list (pair X (list (pair nat (list nat)))))) :=
  match l with
  | nil => false
  | h::tl =>
      let vals := proj_r h in
      if Nat.eqb (List.length vals) 0 then
        true
      else
        thereSomeNil tl
  end.
  
Fixpoint removeNonValid
  {X : Type}
  (val : list (pair nat (list (node X))))
  (l : list (pair nat (list (pair X (list (pair nat (list nat))))))) :=
  match l with
  | nil => val
  | h::tl =>
      let index := proj_l h in
      let validators := proj_r h in
      if thereSomeNil validators then
        removeNonValid (removeAtIndexedList index val) tl
      else
        removeNonValid val tl
  end.

Fixpoint isThereSomethingToRemove
  {X : Type}
  (allValidators : list (pair nat (list (pair X (list (pair nat (list nat))))))) :=
  match allValidators with
  | nil => false
  | h::tl =>
      let validators := proj_r h in
      if thereSomeNil validators then true
      else
        isThereSomethingToRemove tl
  end.

Fixpoint restriction_aux0_v2
  {X : Type}
  (val : list (pair nat (list (node X))))
  (max : nat)
  (arrows : list (pair nat (list (list nat))))
  (eqb_X : X -> X -> bool)
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match max with
  | O => (val, nil)::nil
  | S n =>
      let validators := restriction_aux_v2 val val arrows eqb_X default trules in
      let newMatrix := removeNonValid val validators in
      if isThereSomethingToRemove validators then
        (val, validators)
          ::(restriction_aux0_v2 newMatrix n arrows eqb_X default trules)
      else
        (val, validators)::nil
  end.

Fixpoint indexingList {X : Type} (l : list X) (i : nat) :=
  match l with
  | nil => nil
  | h::tl => (i , h)::(indexingList tl (i+1))
  end.

(*

HIPOTESE DE TRABALHO
Se "val" ja estiver reduzida ao maximo, então o programa abaixo simplesmente retorna todos os modelos asap.

*)

Definition restriction_v2
  {X : Type}
  (val : list (list (node X)))
  (arrows : list (pair nat (list (list nat))))
  (eqb_X : X -> X -> bool)
  :=
  let indexedVals := indexingList val 1 in
  restriction_aux0_v2 indexedVals (List.length indexedVals) arrows eqb_X.

(*

Fixpoint restriction_aux2
  {X : Type}
  (A : X)
  (val : (list (list (node X))))
  (cval : list (node X))
  (cmp1 cmp2 cmp3 : nat -> bool)
  (eqb_X : X -> X -> bool)
  :=
  match val with
  | nil => false
  | h::tl =>
      let vA := findVal A h eqb_X 404 in
      if cmp1 vA then
        let compatible := isCompatible cval h cmp2 cmp3 in
        if compatible then true
        else
          restriction_aux2 A tl cval cmp1 cmp2 cmp3 eqb_X
      else
        restriction_aux2 A tl cval cmp1 cmp2 cmp3 eqb_X
  end.

Fixpoint restriction_aux1
  {X : Type}
  (val : (list (list (node X))))
  (cval cpcval : list (node X))
  (cmp0 cmp1 cmp2 cmp3 : nat -> bool)
  (eqb_X : X -> X -> bool)
  :=
  match cval with
  | nil => true
  | h::tl =>
      match h with
      | Node _ v A =>
          if cmp0 v then
            if (restriction_aux2 A val cpcval cmp1 cmp2 cmp3 eqb_X)
            then
              restriction_aux1 val tl cpcval cmp0 cmp1 cmp2 cmp3 eqb_X
            else
              false
          else
            restriction_aux1 val tl cpcval cmp0 cmp1 cmp2 cmp3 eqb_X
      end
  end.
          
Fixpoint restriction_aux
  {X : Type}
  (val cpval : list (list (node X)))
  (cmp0 cmp1 cmp2 cmp3 : nat -> bool)
  (eqb_X : X -> X -> bool)
  :=
  match val with
  | nil => nil
  | h::tl =>
      if (restriction_aux1 cpval h h cmp0 cmp1 cmp2 cmp3 eqb_X) then
        h::(restriction_aux tl cpval cmp0 cmp1 cmp2 cmp3 eqb_X)
      else
        restriction_aux tl cpval cmp0 cmp1 cmp2 cmp3 eqb_X
  end.
      
Fixpoint restriction_aux0
  {X : Type}
  (val : list (list (node X)))
  (max : nat)
  (cmp0 cmp1 cmp2 cmp3 : nat -> bool)
  (eqb_X : X -> X -> bool)
  :=
  match max with
  | O => val
  | S n =>
      let newVal := restriction_aux val val cmp0 cmp1 cmp2 cmp3 eqb_X in
      restriction_aux0 newVal n cmp0 cmp1 cmp2 cmp3 eqb_X
  end.

Definition restriction
  {X : Type}
  (val : list (list (node X)))
  (cmp0 cmp1 cmp2 cmp3 : nat -> bool)
  (eqb_X : X -> X -> bool)
  :=
  restriction_aux0 val (List.length val) cmp0 cmp1 cmp2 cmp3 eqb_X. *)

Definition makeIt
  {X : Type}
  (A : X)
  (V : list nat)
  (logic : X -> X -> btree X -> list nat -> list (btree X) -> btree X)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  :=
   (
  MakeWithoutPrune
    eqb_X
    leb_X
    length_X
    split
    logic
    A
    A
    V
    )
.
(*
Fixpoint makeItAll
  {X : Type}
  (l : list X)
  (cmp0 cmp1 cmp2 cmp3 : nat -> bool)
  (logic : X -> X -> btree X -> list nat -> list (btree X) -> btree X)
  (eqb_X leb_X geb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (V : list nat)
  :=
  match l with
  | nil => nil
  | h::tl =>
      Pair
        (reverseListOrder (Decompose eqb_X geb_X split h))
        (reverseThisList
           (nodeToNat
              (restriction
                 (makeIt h V logic eqb_X leb_X length_X split)
                 cmp0 cmp1 cmp2 cmp3 eqb_X)
        ))::
        (makeItAll tl cmp0 cmp1 cmp2 cmp3 logic eqb_X leb_X geb_X length_X split V)
  end.
*)
Fixpoint nodeToNatAll_aux2
  {X : Type}
  (l : list (node X)) :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | Node _ val B => val::(nodeToNatAll_aux2 tl)
      end
  end.

Fixpoint nodeToNatAll_aux
  {X : Type}         
  (l : list (pair nat (list (node X)))) :=
  match l with
  | nil => nil
  | h::tl =>
      let index := proj_l h in
      let vals := proj_r h in
      (index, reverseListOrder (nodeToNatAll_aux2 vals))::(nodeToNatAll_aux tl)
  end.

Fixpoint nodeToNatAll
  {X : Type}
  (l : list (pair (list (pair nat (list (node X))))
               (list (pair nat (list (pair X (list (pair nat (list nat))))))))) :=
  match l with
  | nil => nil
  | h::tl =>
      let indexedVals := proj_l h in
      let validators := proj_r h in
      ((nodeToNatAll_aux indexedVals), validators)::(nodeToNatAll tl)
  end.

Definition subf
  {X : Type}
  (A : X)
  (eqb_X geb_X : X -> X -> bool)
  (split : X -> list X)
  :=
  reverseListOrder (Decompose eqb_X geb_X split A).

Definition restrictionSteps
  {X : Type}
  (A : X)
  (matrix : list (list (Forest.node X)))
  (*(V : list nat)
  (logic : X -> X -> btree X -> list nat -> list (btree X) -> btree X)*)
  (eqb_X leb_X geb_X : X -> X -> bool)
  (*(length_X : X -> nat)*)
  (split : X -> list X)
  (arrows : list (pair nat (list (list nat))))
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  let res :=
    (nodeToNatAll
       (restriction_v2
          matrix
          arrows
          eqb_X default
          trules
    )) in
  let subs := subf A eqb_X geb_X split in
  (subs, res).

Definition restrictionStepsWithNode
  {X : Type}
  (A : X)
  (matrix : list (list (node X)))
  (*(V : list nat)*)
  (*(logic : X -> X -> btree X -> list nat -> list (btree X) -> btree X)*)
  (eqb_X leb_X geb_X : X -> X -> bool)
  (*(length_X : X -> nat)*)
  (split : X -> list X)
  (arrows : list (pair nat (list (list nat))))
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  let res :=
    restriction_v2
      matrix
      arrows eqb_X default trules
  in
  let subs := subf A eqb_X geb_X split in
  (subs, res).

Fixpoint getFormulas
  {X : Type}
  (l : list (node X)) :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | Node _ _ A => A::(getFormulas tl)
      end
  end.
(*                                       
Definition makeLogic
  {X : Type}
  (A : X) :=
  let matrix := reverseThisList (restriction (makeIt A)) in
  let subA := getFormulas (pop matrix nil) in 
  (subA; (nodeToNat matrix)).

Definition makeS4wp (A : extendedLF) :=
  (subf A; (reverseThisList (nodeToNat (makeIt A)))).

Fixpoint makeS4all (l : list extendedLF) :=
  match l with
  | nil => nil
  | h::tl => (makeS4 h)::(makeS4all tl)
  end.
*)
Fixpoint divide_aux (l : list nat) :=
  match l with
  | nil => false
  | h::tl =>
      if Nat.eqb h 1 then true
      else divide_aux tl
  end.

Fixpoint divide_aux1 (l : list (pair nat (list nat))) :=
  match l with
  | nil => nil
  | h::tl =>
      if (divide_aux (proj_r h)) then
        h::(divide_aux1 tl)
      else
        (divide_aux1 tl)
  end.

Fixpoint divide_aux2 (l : list (pair nat (list nat))) :=
  match l with
  | nil => nil
  | h::tl =>
      if negb (divide_aux (proj_r h)) then
        h::(divide_aux2 tl)
      else
        (divide_aux2 tl)
  end.

Definition divide (l : list (pair nat (list nat))) :=
  (divide_aux1 l, divide_aux2 l).

Fixpoint getLast {X : Type} (l : list X) :=
  match l with
  | nil => nil
  | h::tl =>
      if (Nat.eqb (List.length tl) 0) then
        [h]
      else
        getLast tl
  end.

Definition computeTable
  {X : Type}
  (steps : pair (list X) (list (pair (list (pair nat (list nat)))
                                  (list (pair nat (list (pair X (list (pair nat (list nat))))))))))
  :=
  (proj_l steps, (proj_l (pop (getLast (proj_r steps)) (nil, nil)))).

Definition computeTableWithNode
  {X : Type}
  (A : X)
  (matrix : list (list (node X)))
  (*(V : list nat)
  (logic : X -> X -> btree X -> list nat -> list (btree X) -> btree X)*)
  (eqb_X leb_X geb_X : X -> X -> bool)
 (* (length_X : X -> nat) *)
  (split : X -> list X)
  (arrows : list (pair nat (list (list nat))))
  (default : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  let steps :=
    restrictionStepsWithNode
      A matrix eqb_X leb_X geb_X split
      arrows
      default trules
  in
  (proj_l steps, (proj_l (pop (getLast (proj_r steps)) (nil, nil)))).

Definition computeValidators
  {X : Type}
  (steps : pair (list X) (list (pair (list (pair nat (list nat)))
               (list (pair nat (list (pair X (list (pair nat (list nat))))))))))
  :=
  proj_r (pop (getLast (proj_r (steps))) (nil, nil)).

(**


RNMATRIX ---> Kripke Models

workplace.


**)

Fixpoint eqb_lX {X : Type} (l1 l2 : list X) (cmp : X -> X -> bool) :=
  match l1, l2 with
  | h1::tl1, h2::tl2 =>
      if cmp h1 h2 then eqb_lX tl1 tl2 cmp
      else false
  | nil, nil => true
  | _, _ => false
  end.
(*
Fixpoint isInList (l1 : list nat) (l : list (list nat)) :=
  match l with
  | nil => false
  | h::tl =>
      if eqb_lnat l1 h then true
      else isInList l1 tl
  end.*)

Fixpoint isInList (n : nat) (l : list nat) :=
  match l with
  | nil => false
  | h::tl =>
      if Nat.eqb n h then true
      else isInList n tl
  end.

Fixpoint convergeArrows (l : (list (pair nat (list nat)))) :=
  match l with
  | nil => nil
  | (_, arrows)::tl =>
      arrows ++ (convergeArrows tl)
  end.

Fixpoint arrangeKM_lazymode2
  (l : list nat)
  (ws : list nat) :=
  match l with
  | nil => ws
  | h::tl =>
      if isInList h ws then
        arrangeKM_lazymode2 tl ws
      else
        arrangeKM_lazymode2 tl (h::ws)
  end.

Fixpoint arrangeKM_lazymode1
  {X : Type}
  (v : nat)
  (l : list (pair X (list (pair nat (list nat)))))
  (ws : list nat) :=
  match l with
  | nil => ws
  | h::tl =>
      let new := arrangeKM_lazymode2 (convergeArrows (proj_r h)) ws in
      arrangeKM_lazymode1 v tl new
  end.

Fixpoint eqb_list
  {X : Type}
  (eqb : X -> X -> bool)
  (l1 l2 : list X)
  :=
  match l1,l2 with
  | nil, nil => true 
  | h::tl, nil => false
  | nil, h::tl => false
  | h1::tl1, h2::tl2 =>
      if eqb h1 h2 then eqb_list eqb tl1 tl2
      else false
  end.

Fixpoint injectList (l1 : list nat) (l2 : list (list nat)) :=
  match l2 with
  | nil => nil
  | h::tl =>
      (sort (RemoveAmbiguity Nat.eqb (l1++h)) Nat.leb)::(injectList l1 tl)
  end.

Fixpoint injectAllLists (l1 l2 : list (list nat)) :=
  match l1 with
  | nil => nil
  | h::tl =>
      (injectList h l2)++(injectAllLists tl l2)
  end.
(*
Compute injectAllLists (injectAllLists
  [[1]; [2]; [3]; [1; 2]; [1; 3]; [2; 3]; [1; 2; 3]]
  [[4]; [5]; [6]; [4; 5]; [4; 6]; [5; 6]; [4; 5; 6]])
  [[7]; [8]; [9]; [7; 8]; [7; 9]; [8; 9]; [7; 8; 9]].*)

Fixpoint arrangeKM_aux3
  (valdsPower : list (list (list nat)))
  :=
  match valdsPower with
  | nil => nil
  | h::nil => h
  | h::tl =>
      RemoveAmbiguity (eqb_list Nat.eqb) (injectAllLists h (arrangeKM_aux3 tl))
  end.

Compute filter
  (fun x => Nat.eqb (List.length x) 3)
  (arrangeKM_aux3
     [[[1]; [2]; [3]; [1; 2]; [1; 3]; [2; 3]; [1; 2; 3]];
      [[4]; [5]; [6]; [4; 5]; [4; 6]; [5; 6]; [4; 5; 6]];
      [[7]; [8]; [9]; [7; 8]; [7; 9]; [8; 9]; [7; 8; 9]]]).

Compute 2 <=? 3.

Definition list_leqb {X : Type} (l1 l2 : list X) := (List.length l1) <=? (List.length l2).

Compute Nat.eqb 2 3.
Check sort.

Definition m := sort
                  (arrangeKM_aux3
                     [[[1]; [2]; [3]; [1; 2]; [1; 3]; [2; 3]; [1; 2; 3]];
                      [[4]; [1]; [6]; [4; 5]; [4; 6]; [5; 6]; [4; 5; 6]];
                      [[7]; [8]; [9]; [7; 8]; [7; 9]; [8; 9]; [7; 8; 9]]])
                  list_leqb.

Compute (List.length (pop m nil)).

Compute m.

Check (2 , 3).

Fixpoint arrangeKM_aux2
  {X : Type}
  (valds : list (pair X (list nat)))
    :=
  match valds with
  | nil => nil
  | h::tl =>
      (power (proj_r h) 0)::(arrangeKM_aux2 tl)
  end.

Fixpoint arrangeKM_aux4
  (index : nat)
  (allValds : list (list nat))
  :=
  match allValds with
  | nil => nil
  | h::tl =>
      (index, h)::(arrangeKM_aux4 index tl)
  end.

Fixpoint joinPreModels_aux
  {X : Type}
  (index : X)
  (pm : list (pair nat (list nat))) :=
  match pm with
  | nil => nil
  | (_, targets)::tl =>
      (index, targets)::(joinPreModels_aux index tl)
  end.

Fixpoint joinPreModels
  {X : Type}
  (valds : list (pair X (list (pair nat (list nat))))) :=
  match valds with
  | nil => nil
  | (index, arrows)::tl =>
      (joinPreModels_aux index arrows)++(joinPreModels tl)
  end.

Fixpoint findBestChoice_aux
  {X : Type}
  (valds : list (pair X (list nat)))
  (n : nat)
  :=
  match valds with
  | nil => 0
  | h::tl =>
      if isElementInList n (proj_r h) Nat.eqb then
        1 + (findBestChoice_aux tl n)
      else
        findBestChoice_aux tl n
  end.

Fixpoint findBestChoice
  {X : Type}
  (valds : list (pair X (list nat)))
  (arrows : list nat)
  (h_score : nat)
  (best_choice : nat)
  :=
  match arrows with
  | nil => best_choice
  | arrow::tl =>
      let score := findBestChoice_aux valds arrow in
      if h_score <=? score then
        findBestChoice valds tl score arrow
      else
        findBestChoice valds tl h_score best_choice
  end.
      
Fixpoint findSmallestModel
  {X : Type}
  (valds valdscp : list (pair X (list nat)))
  :=
  match valds with
  | nil => nil
  | h::tl =>
      (findBestChoice valdscp (proj_r h) 0 0)::(findSmallestModel tl valdscp)
  end.

Fixpoint arrangeKM_aux1
  {X : Type}
  (smallest lazymode : bool)
  (l : list (pair nat (list (pair X (list (pair nat (list nat)))))))
    :=
  match l with
  | nil => nil
  | h::tl =>
      let index := proj_l h in
      let valds := proj_r h in
      if lazymode then
        let accByIndex := arrangeKM_lazymode1 index valds nil in
        [(index, accByIndex)]
          ++(arrangeKM_aux1 smallest lazymode tl)
      else
        if Nat.eqb (List.length (joinPreModels valds)) 0 then
          [(index, nil)]
            ++(arrangeKM_aux1 smallest lazymode tl)
        else
          let pm_joined := joinPreModels valds in
          if negb smallest then
            let accByIndex := arrangeKM_aux2 pm_joined in
            let premodels := arrangeKM_aux3 accByIndex in
            (arrangeKM_aux4 index premodels)
              ++(arrangeKM_aux1 smallest lazymode tl)
          else
            (*
            let sortPreModels := sort premodels list_leqb in
            let allSelected :=
              filter
                (fun x => Nat.eqb (List.length x) (List.length (pop sortPreModels nil)))
                sortPreModels in     
            (arrangeKM_aux4 index allSelected)*)
            [(index, (findSmallestModel pm_joined pm_joined))]
              ++(arrangeKM_aux1 smallest lazymode tl)
  end.
      
Definition arrangeKM
  {X : Type}
  (A : X)
  (matrix : list (list (Forest.node X)))
  (*(V : list nat)
  (logic : X -> X -> btree X -> list nat -> list (btree X) -> btree X)*)
  (eqb_X leb_X geb_X : X -> X -> bool)
  (*(length_X : X -> nat)*)
  (split : X -> list X)
  (arrows : list (pair nat (list (list nat))))
  (default : nat)
  (smallest lazymode : bool)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  let steps :=
    restrictionSteps
      A matrix
      eqb_X leb_X geb_X split
      arrows
      default trules
  in
  let table := computeTable steps in
  let validators := computeValidators steps in
  arrangeKM_aux1 smallest lazymode validators.

Inductive SignedLF (X : Type) :=
| sign (b : bool) (L : X).

Arguments sign {X}.

Inductive node (X : Type) :=
| Node (SL : SignedLF X) (n : nat)
| Rel : bool -> nat -> nat -> node X.

Arguments Node {X}.
Arguments Rel {X}.

Definition eqb_SignedLF
  {X : Type}
  (S1 S2 : SignedLF X)
  (cmp : X -> X -> bool) :=
  match S1 with
  | sign b1 L1 =>
      match S2 with
      | sign b2 L2 =>
          if xorb b1 b2 then false
          else cmp L1 L2
      end
  end.

Definition min {X : Type} (n : node X) :=
  match n with
  | Node _ k => k
  | Rel _ k j => k
  end.

Definition max {X : Type} (n : node X) :=
  match n with
  | Node _ k => k
  | Rel _ k j => j
  end.

Notation "a =? b" := (eqb_SignedLF a b).

(*********)

Require Import Coq.Arith.EqNat.

Definition eqb_node_R
  {X : Type}
  (A : node X)
  (B : node X) :=
  match A with
  | Rel _ k j =>
      match B with
      | Rel _ k1 j1 => if andb (beq_nat k k1) (beq_nat j j1) then true
                   else false
      | _ => false
      end
  | _ => false        
  end.

Definition eqb_node
  {X : Type}
  (cmp : X -> X -> bool)
  (A : node X)
  (B : node X)
  :=
  match A with
  | Node S1 k1 =>
      match B with
      | Node S2 k2 =>
          if (Nat.eqb k1 k2) then eqb_SignedLF S1 S2 cmp
          else false
      | _ => false
      end
  | _ => eqb_node_R A B        
  end.

Fixpoint checkIfNodeIsInList
  {X : Type}
  (A : node X)
  (l : list (node X))
  (cmp : X -> X -> bool)
  :=
  match l with
  | nil => false
  | h::tl => orb (eqb_node cmp A h) (checkIfNodeIsInList A tl cmp)
  end.

Fixpoint CloseRToTransitivity
  {X : Type}
  (n : node X)
  (ln : list (node X))
  (cp_ln : list (node X))
  (cmp : X -> X -> bool) : list (node X)
  :=
  match ln with
  | nil => nil
  | h::tl => match h with
             | Node _ k => CloseRToTransitivity n tl cp_ln cmp
             | Rel b k j => if (beq_nat j (min n))
                        then if negb (checkIfNodeIsInList (Rel b k (max n)) cp_ln cmp)
                             then ((Rel false k (max n))) (*((Rel true k (max n))) para marcar que foi adicionado aqui*)
                                    ::(CloseRToTransitivity n tl cp_ln cmp)
                             else (CloseRToTransitivity n tl cp_ln cmp)
                        else (CloseRToTransitivity n tl cp_ln cmp)
             end
  end.

Fixpoint RemoveAmbiguity
  {X : Type}
  (ln : list (node X))
  (cmp : X -> X -> bool)
  :=
  match ln with
  | nil => nil
  | h::tl => if checkIfNodeIsInList h tl cmp then
               RemoveAmbiguity tl cmp
             else h::(RemoveAmbiguity tl cmp)
  end.

Definition Transitivity
  {X : Type}
  (n : node X)
  (ln : list (node X))
  (cmp : X -> X -> bool)
  :=
  RemoveAmbiguity (CloseRToTransitivity n ln ln cmp) cmp.

Fixpoint closeToTrans_aux
  {X : Type}
  (l cl : list (node X))
  (cmp : X -> X -> bool)
  :=
  match l with
  | nil => nil
  | h::tl =>
      let closeThis := Transitivity h cl cmp in
      if negb (Nat.eqb (List.length closeThis) 0)
      then (Transitivity h cl cmp)++(closeToTrans_aux tl cl cmp)
      else (closeToTrans_aux tl cl cmp)
  end.

Definition closeToTrans
  {X : Type}
  (l : list (node X))
  (cmp : X -> X -> bool)
  := closeToTrans_aux l l cmp.

Fixpoint testeTrans
  {X : Type}
  (l : list (pair nat (pair (list (node X)) (list nat))))
  (cmp : X -> X -> bool)
  :=
  match l with
  | nil => nil
  | h::tl =>
      let closure := closeToTrans (proj_l (proj_r h)) cmp in
      (closure)::(testeTrans tl cmp)
  end.


(***********)

Fixpoint getOnlyR {X : Type} (l : list (node X)) : list (node X) :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | Rel b k j => (Rel b k j)::(getOnlyR tl)
      | _ => getOnlyR tl
      end
  end.

Fixpoint getOnlyNode {X : Type} (l : list (node X)) : list (node X) :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | Node sf w => (Node sf w)::(getOnlyNode tl)
      | _ => getOnlyNode tl
      end
  end.

Definition separateNodeList {X : Type}
  (l : list (node X)) : pair (list (node X)) (list (node X)) :=
  ((getOnlyNode l), (getOnlyR l)).

Fixpoint rnkripke_aux4
  {X : Type}
  (atoms : list X)
  (row : list (Forest.node X))
  (w : nat)
  (eqb_X : X -> X -> bool)
  (default : nat)
  (Designated : list nat)
  :=
  match atoms with
  | nil => nil
  | A::tl =>
      let vA := findVal A row eqb_X default in
      if isElementInList vA Designated Nat.eqb then
        (Node (sign true A) w)::(rnkripke_aux4 tl row w eqb_X default Designated)
      else
        (Node (sign false A) w)::(rnkripke_aux4 tl row w eqb_X default Designated)
  end.

Fixpoint rnkripke_aux3
  {X : Type}
  (atoms : list X)
  (matrix : list (pair nat (list (Forest.node X))))
  (w : nat)
  (eqb_X : X -> X -> bool)
  (default : nat)
  (Designated : list nat)
  :=
  match matrix with
  | nil => nil
  | h::tl =>
      let index := proj_l h in
      let row := proj_r h in
      if Nat.eqb index w then
        rnkripke_aux4 atoms row w eqb_X default Designated
      else
        rnkripke_aux3 atoms tl w eqb_X default Designated
  end.

Fixpoint avoidRepetition
  {X : Type}
  (add new : list (node X))
  (eqb_X : X -> X -> bool)
  :=
  match add with
  | nil => new
  | h::tl =>
      if isElementInList h new (eqb_node eqb_X) then
        avoidRepetition tl new eqb_X
      else
        avoidRepetition tl (h::new) eqb_X
  end.

Fixpoint rnkripke_aux2
  {X : Type}
  (atoms : list X)
  (matrix : list (pair nat (list (Forest.node X))))
  (w0 : nat)
  (l : list nat)
  (eqb_X : X -> X -> bool)
  (default : nat)
  (Designated : list nat)
  (constraints : list Frame)
  (model : list (node X))
  :=
  match l with
  | nil =>
      if Refl constraints then
        (avoidRepetition [Rel true w0 w0] model eqb_X)
      else
        model
  | h::tl =>
      let atomVals := rnkripke_aux3 atoms matrix h eqb_X default Designated in
      let newModel := (avoidRepetition ((Rel false w0 h)::atomVals) model eqb_X) in
      rnkripke_aux2 atoms matrix w0 tl eqb_X default Designated constraints newModel
  end.

Definition rnkripke_aux1
  {X : Type}
  (atoms : list X)
  (matrix : list (pair nat (list (Forest.node X))))
  (v : pair nat (list nat))
  (eqb_X : X -> X -> bool)
  (default : nat)
  (Designated : list nat)
  (constraints : list Frame)
  : pair nat (pair (list (node X)) (list nat))
  :=
  let index := proj_l v in
  let l := proj_r v in
  let atomVals := rnkripke_aux3 atoms matrix index eqb_X default Designated in
  let initialModel :=
    (rnkripke_aux2 atoms matrix index l eqb_X default Designated constraints nil) in
  (index,
   ((avoidRepetition atomVals initialModel eqb_X),
   (index::nil))).

Fixpoint closeToReflexivity
  {X : Type}
  (l newList : list (node X))
  : list (node X)
  :=
  match l with
  | nil => newList
  | h::tl =>
      match h with
      | Rel t a b =>
          if isElementInList (Rel t a a) newList (eqb_node_R) then
            if isElementInList (Rel t b b) newList (eqb_node_R) then
              closeToReflexivity tl newList
            else
              closeToReflexivity tl ((Rel true b b)::newList)
          else
            if isElementInList (Rel t b b) newList (eqb_node_R) then
              closeToReflexivity tl ((Rel true a a)::newList)
            else
              closeToReflexivity tl ((Rel true a a)::(Rel true b b)::newList)
      | _ => closeToReflexivity tl newList
      end
  end.

(****** Symmetric closure *********)

Fixpoint closeToSym_aux
  {X : Type}
  (l : list (node X))
  (nl : list (node X))
  :=
  match l with
  | nil => nl
  | h::tl =>
      match h with
      | Rel t a b =>  
          closeToSym_aux tl ((Rel t a b)::(Rel true b a)::nl)
      | _ => closeToSym_aux tl nl
      end
  end.

Definition closeToSym
  {X : Type}
  (l : list (node X))
  :=
  closeToSym_aux l l.
      
(**********************************)

Fixpoint closeR_aux1
  {X : Type}
  (index : nat)
  (l : list (node X))
  (newR : list (node X))
  (allV : list (pair nat (pair (list (node X)) (list nat))))
  (visited : list nat)
  (eqb_X : X -> X -> bool)
  (constraints : list Frame)
  :=
  match l with
  | nil =>
      if Refl constraints then
        let closedrefl := closeToReflexivity newR newR in
        if Trans constraints then
          let closedtrans := (avoidRepetition (closeToTrans closedrefl eqb_X) closedrefl eqb_X) in
          if Sym constraints then
            let closedsym := (avoidRepetition (closeToSym closedtrans) closedtrans eqb_X) in
            (closedsym, visited)
          else
            (closedtrans, visited)
        else
          if Sym constraints then
            let closedsym := (avoidRepetition (closeToSym closedrefl) closedrefl eqb_X) in
            (closedsym, visited)
          else
            (closedrefl, visited)
      else
        if Trans constraints then
          let closedtrans := (avoidRepetition (closeToTrans newR eqb_X) newR eqb_X) in
          if Sym constraints then
            let closedsym := (avoidRepetition (closeToSym closedtrans) closedtrans eqb_X) in
            (closedsym, visited)
          else
            (closedtrans, visited)
        else
          if Sym constraints then
            let closedsym := (avoidRepetition (closeToSym newR) newR eqb_X) in
            (closedsym, visited)
          else
            (newR, visited)
  | h::tl =>
      match h with
      | Rel _ minH maxH =>
          let target :=
            pop
              (filter (fun x => Nat.eqb (proj_l x) maxH) allV)
              (0, (nil, nil))
          in
          let target_index := proj_l target in
          let target_rels := proj_l (proj_r target) in
          if isElementInList maxH visited (Nat.eqb)
          then
            closeR_aux1 index tl newR allV visited eqb_X constraints
          else
            closeR_aux1
              index
              tl
              (((avoidRepetition (target_rels) newR eqb_X)))
              allV
              (maxH::visited)
              eqb_X
              constraints
      | _ => closeR_aux1 index tl newR allV visited eqb_X constraints
      end
  end.

Definition closeR_aux0
  {X : Type}
  (allV : list (pair nat (pair (list (node X)) (list nat))))
  (v : pair nat (pair (list (node X)) (list nat)))
  (eqb_X : X -> X -> bool)
  (constraints : list Frame)
  :=
  let index := proj_l v in
  let l := proj_l (proj_r v) in
  let visited := proj_r (proj_r v) in
  (*let new_visited :=
    if isElementInList index visited (Nat.eqb)
    then visited
    else index::visited
  in*)
  let mv := closeR_aux1 index l l allV visited eqb_X constraints in
  let new_visited := proj_r mv in
  let model := (getOnlyR (proj_l mv))++(getOnlyNode (proj_l mv)) in
  (index, (model, new_visited)).

Fixpoint closeR
  {X : Type}
  (lc l : list (pair nat (pair (list (node X)) (list nat))))
  (eqb_X : X -> X -> bool)
  (constraints : list Frame)
  :=
  match l with
  | nil => nil
  | h::tl => (closeR_aux0 lc h eqb_X constraints)::(closeR lc tl eqb_X constraints)
  end.

Compute [1;12321].

Fixpoint rnkripke_aux0
  {X : Type}
  (atoms : list X)
  (matrix : list (pair nat (list (Forest.node X))))
  (l : list (pair nat (list nat)))
  (eqb_X : X -> X -> bool)
  (default : nat)
  (Designated : list nat)
  (constraints : list Frame)
  :=
  match l with
  | nil => nil
  | h::tl => (rnkripke_aux1 atoms matrix h eqb_X default Designated constraints)::
               (rnkripke_aux0 atoms matrix tl eqb_X default Designated constraints)
  end.

Fixpoint closeR_aux00
  {X : Type}
  (max : nat) 
  (rncp rnkripke : list (pair nat (pair (list (node X)) (list nat))))
  (eqb_X : X -> X -> bool)
  (constraints : list Frame)
  (*(select : (pair nat (pair (list (node X)) (list nat))) -> bool)*)
  :=
  match max with
  | O => rnkripke
  | S n =>
      let new := closeR rncp (*(filter select rnkripke)*) rnkripke eqb_X constraints in
      closeR_aux00 n rncp new eqb_X constraints
  end.

(*
Fixpoint rnkripke_aux00
  {X : Type}
  (l : list (pair nat (list (node X)))) :=
  match l with
  | nil => nil
  | h::tl =>
      (proj_l h; (separateNodeList (proj_r h)))
        ::(rnkripke_aux00 tl)
  end.
 *)


Fixpoint rearrangeModels_aux2
  {X : Type}
  (vals : list (node X))
  (w :  nat)
  :=
  match vals with
  | nil => nil
  | h::tl =>
      match h with
      | Node Sf w' =>
          if Nat.eqb w w' then
            match Sf with
            | sign b A =>
                if b then
                  A::(rearrangeModels_aux2 tl w)
                else
                  rearrangeModels_aux2 tl w
            end
          else
            rearrangeModels_aux2 tl w
      | _ => rearrangeModels_aux2 tl w
      end
  end.        
      
Fixpoint rearrangeModels_aux1
  {X : Type}
  (vals : list (node X))
  (worlds : list nat)
  :=
  match worlds with
  | nil => nil
  | h::tl =>
      (h, (rearrangeModels_aux2 vals h))
        ::(rearrangeModels_aux1 vals tl)
  end.

Fixpoint rearrangeModels
  {X : Type}
  (l : list (pair nat (pair (list (node X)) (list nat))))
  :=
  match l with
  | nil => nil
  | h::tl =>
      let index := proj_l h in
      let worlds := proj_r (proj_r h) in
      let rels := proj_l (proj_r h) in
      (index,
        ((rearrangeModels_aux1 (getOnlyNode rels) worlds),
          (getOnlyR rels)
        )
      )::(rearrangeModels tl)
  end.

Fixpoint filter_smallest
  {X : Type}
  (models modelsc : list (pair nat (pair (list (node X)) (list nat))))
  (visited : list nat)
  :=
  match models with
  | nil => nil
  | model::tl =>
      let index := proj_l model in
      if negb (isElementInList index visited Nat.eqb) then
        let select := filter (fun M => Nat.eqb (proj_l M) index) modelsc in
        let M_sorted :=
          sort
            select
            (fun M1 M2 =>
               (List.length (proj_r (proj_r M1))) <=?
                 (List.length (proj_r (proj_r M2))))
        in
        let smallest :=
          filter (fun M => Nat.eqb (List.length (proj_r (proj_r M)))
                             (List.length (proj_r (proj_r (pop M_sorted (0, (nil, nil))))))) M_sorted
        in
        smallest++(filter_smallest tl modelsc (index::visited))
      else
        filter_smallest tl modelsc visited
  end.

Definition rnkripke
  {X : Type}
  (A : X)
  (matrix : list (list (Forest.node X)))
  (eqb_X leb_X geb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (arrows : list (pair nat (list (list nat))))
  (*(cmp0 cmp1 cmp2 cmp3 : pair X nat -> list (Forest.node X) -> list (Forest.node X) -> bool)*)
  (default : nat)
  (Designated : list nat)
  (constraints : list Frame)
  (*(select : (pair nat (pair (list (node X)) (list nat))) -> bool)*)
  (smallest lazymode : bool)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  let arrange :=
    arrangeKM
      A matrix eqb_X leb_X geb_X split
      arrows default smallest lazymode trules
  in
  let table := proj_r
                 (computeTableWithNode
                    A
                    matrix eqb_X leb_X geb_X split
                    arrows default
                    trules
                 ) in
  let atoms := filter (fun x => Nat.eqb (length_X x) 0) (subf A eqb_X geb_X split) in
  let initialR :=
    rnkripke_aux0 atoms table arrange eqb_X default Designated constraints in
  let relations :=
    closeR_aux00
      ((List.length initialR))
      initialR
      initialR
      eqb_X
      constraints
      (*select*)
  in
  if smallest then
    filter_smallest relations relations nil
  else
    relations.
      

(*

[(1; ([Rel true 1 1; Node (sign false (! "P")) 1]; [1]));
        (2;
        ([Rel true 1 1; Rel true 5 5; Rel true 2 2; 
          Rel false 2 5; Rel false 2 1; Node (sign false (! "P")) 2;
          Node (sign true (! "P")) 5; Node (sign false (! "P")) 1];
        [1; 5; 2]));
        (3;
        ([Rel true 1 1; Rel true 3 3; Rel false 3 1;
          Node (sign false (! "P")) 3; Node (sign false (! "P")) 1];
        [1; 3]));
        (4;
        ([Rel true 5 5; Rel true 4 4; Rel false 4 5;
          Node (sign false (! "P")) 4; Node (sign true (! "P")) 5];
        [5; 4])); (5; ([Rel true 5 5; Node (sign true (! "P")) 5]; [5]))]
     : list (pair nat (pair (list (node eLF)) (list nat)))


 *)


(*
Definition rnkripke_separated (A : extendedLF) :=
  let arrange := arrangeKM A in
  let table := proj_r (computeTableWithNode A) in
  let atoms := filter (fun x => Nat.eqb (length_elf x) 0) (subf A) in
  let initialR := rnkripke_aux0 atoms table arrange in
  let relations := closeR_aux00 (List.length initialR) initialR in
  relations.
 *)

(* Auxiliary functions *)

Fixpoint genTree
  {X : Type}
  (A : X)
  (l : list nat) :=
  match l with
  | nil => Leaf _ true
  | h::tl =>
      if Nat.eqb (List.length tl) 0 then
        (Alpha _ (Forest.Node _ h A) (Leaf _ true))
      else
        Beta _
          (Alpha _ (Forest.Node _ h A) (Leaf _ true))
          (genTree A tl)
  end.

Fixpoint unary_op_aux
  {X : Type}
  (A : X)
  (vB : nat)
  (table : list (pair nat (list nat))) :=
  match table with
  | nil => Leaf _ true
  | h::tl =>
      let x := proj_l h in
      let vals := proj_r h in
      if (Nat.eqb x vB) then
        genTree A vals
      else
        unary_op_aux A vB tl
  end.

Fixpoint unary_op
  {X : Type}
  (A B : X)
  (partialV : btree X)
  (vB : nat)
  (table : list (pair nat (list nat)))
  (eqb_X : X -> X -> bool)
  :=
  match partialV with
  | Leaf _ _ =>
      unary_op_aux A vB table
  | Alpha _ n t =>
      match n with
      | Forest.Node _ v D =>
          if (eqb_X B D) then
            Alpha _ n (unary_op A B t v table eqb_X)
          else Alpha _ n (unary_op A B t vB table eqb_X)
      end
  | Beta _ t1 t2 =>
      Beta _
        (unary_op A B t1 vB table eqb_X)
        (unary_op A B t2 vB table eqb_X)
  end.

Fixpoint bin_op_aux
  {X : Type}
  (A : X)
  (vB vC : nat)
  (table : list (pair (pair nat nat) (list nat))) :=
  match table with
  | nil => Leaf _ true
  | h::tl =>
      let xy := proj_l h in
      let vals := proj_r h in
      if
        andb
          (Nat.eqb (proj_l xy) vB)
          (Nat.eqb (proj_r xy) vC)
      then
        genTree A vals
      else
        bin_op_aux A vB vC tl
  end.

Fixpoint bin_op
  {X : Type}
  (A B C : X)
  (partialV : btree X)
  (vB vC : nat)
  (table : list (pair (pair nat nat) (list nat)))
  (eqb_X : X -> X -> bool)
  :=
  match partialV with
  | Leaf _ _ =>
      bin_op_aux A vB vC table
  | Alpha _ n t =>
      match n with
      | Forest.Node _ v D =>
          if (eqb_X B D) then
            if (eqb_X C D) then
              Alpha _ n (bin_op A B C t v v table eqb_X)
            else
              Alpha _ n (bin_op A B C t v vC table eqb_X)
          else
            if (eqb_X C D) then
              Alpha _ n (bin_op A B C t vB v table eqb_X)
            else Alpha _ n (bin_op A B C t vB vC table eqb_X)
      end
  | Beta _ t1 t2 =>
      Beta _
        (bin_op A B C t1 vB vC table eqb_X)
        (bin_op A B C t2 vB vC table eqb_X)
  end.

(*
(*

Alternative algorithm. "Reducing on the fly".

 *)

(* Reducing on the fly *)

Fixpoint reduceOnTheFly_aux2
  {X : Type}
  (A : X)
  (allVs : list (list (Forest.node X)))
  (v : list (Forest.node X))
  (eqb_X : X -> X -> bool)
  (cmp1 cmp2 cmp3: pair X nat -> list (Forest.node X) -> list (Forest.node X) -> bool)
  (default : nat)
  :=
  match allVs with
  | nil => false
  | h::tl =>
      let wA := findVal A h eqb_X default in
      if cmp1 (A, wA) v h then
        let compatible := isCompatible v h v h cmp2 cmp3 in
        if compatible then true
        else
          reduceOnTheFly_aux2 A tl v eqb_X cmp1 cmp2 cmp3 default
      else
        reduceOnTheFly_aux2 A tl v eqb_X cmp1 cmp2 cmp3 default
  end.
  
Fixpoint reduceOnTheFly_aux
  {X : Type}
  (allVs : list (list (Forest.node X)))
  (v vcp : list (Forest.node X))
  (eqb_X : X -> X -> bool)
  (cmp0 cmp1 cmp2 cmp3 : pair X nat -> list (Forest.node X) -> list (Forest.node X) -> bool)
  (checkV : list (list (Forest.node X)) -> list (Forest.node X) -> bool)
  (default : nat)
  :=
  match v with
  | nil => true
  | h::tl =>
      match h with
      | Forest.Node _ vA A =>
          if cmp0 (A, vA) vcp nil then
            andb
              (checkV allVs vcp)
              (reduceOnTheFly_aux allVs tl vcp eqb_X cmp0 cmp1 cmp2 cmp3 checkV default)
          else
            (reduceOnTheFly_aux allVs tl vcp eqb_X cmp0 cmp1 cmp2 cmp3 checkV default)
      end
  end.

Fixpoint reduceOnTheFly_aux1
  {X : Type}
  (pV : btree X)
  (allVs : list (list (Forest.node X)))
  (v : list (Forest.node X))
  (b : bool)
  (eqb_X : X -> X -> bool)
  (cmp0 cmp1 cmp2 cmp3 : pair X nat -> list (Forest.node X) -> list (Forest.node X) -> bool)
  (checkV : list (list (Forest.node X)) -> list (Forest.node X) -> bool)
  (default : nat)
  :=
  match pV with
  | Leaf _ b' =>
      if andb b b' then
        Leaf _ (reduceOnTheFly_aux allVs v v eqb_X cmp0 cmp1 cmp2 cmp3 checkV default)
      else
        Leaf _ b'
  | Alpha _ N nt =>
      match N with
      | Forest.Node _ vA A =>
          if cmp0 (A, vA) v nil then
            Alpha _ N
              (reduceOnTheFly_aux1
                 nt
                 allVs
                 (N::v)
                 true
                 eqb_X
                 cmp0 cmp1 cmp2 cmp3 checkV default)
          else
            Alpha _ N
              (reduceOnTheFly_aux1
                 nt
                 allVs
                 (N::v)
                 b
                 eqb_X
                 cmp0 cmp1 cmp2 cmp3 checkV default)
      end
  | Beta _ nt1 nt2 =>
      Beta _
        (reduceOnTheFly_aux1 nt1 allVs v b eqb_X cmp0 cmp1 cmp2 cmp3 checkV default)
        (reduceOnTheFly_aux1 nt2 allVs v b eqb_X cmp0 cmp1 cmp2 cmp3 checkV default)
  end.

Definition reduceOnTheFly_aux0
  {X : Type}
  (pV : btree X)
  (allVs : list (list (Forest.node X)))
  (max : nat)
  (eqb_X : X -> X -> bool)
  (cmp0 cmp1 cmp2 cmp3 : pair X nat -> list (Forest.node X) -> list (Forest.node X) -> bool)
  (checkV : list (list (Forest.node X)) -> list (Forest.node X) -> bool)
  (default : nat)
  :=
  let reducedtree :=
    reduceOnTheFly_aux1
      pV
      allVs
      nil
      false
      eqb_X
      cmp0 cmp1 cmp2 cmp3 checkV default
  in
  reducedtree.

(*
Fixpoint getAVals
  {X : Type}
  (A : X)
  (l : list (list (Forest.node X)))
  (eqb_X : X -> X -> bool)
  (default : nat)
  :=
  match l with
  | nil => nil
  | h::tl =>
      let vA := findVal A h eqb_X default in
      (vA)::(getAVals A tl eqb_X default)
  end.

Fixpoint isAllT (l : list nat) :=
  match l with
  | nil => true
  | h::tl =>
      if negb (Nat.eqb h vT) then false
      else isAllT tl
  end.

Fixpoint thereIsNoT (l : list nat) :=
  match l with
  | nil => true
  | h::tl =>
      if Nat.eqb h vT then false
      else isAllT tl
  end.

Fixpoint isAllF (l : list nat) :=
  match l with
  | nil => true
  | h::tl =>
      if negb (Nat.eqb h vF) then false
      else isAllT tl
  end.
 *)

(* Search (list ?X -> list ?X -> bool). *)

Fixpoint cmp_pVs
  {X : Type}
  (l1 l2 : list (list (Forest.node X)))
  (eqb_X : X -> X -> bool)
  :=
  match l1, l2 with
  | h1::tl1, h2::tl2 =>
      if eqb_lX h1 h2 (Forest.eqb_node eqb_X) then
        cmp_pVs tl1 tl2 eqb_X
      else
        false
  | nil, nil => true
  | _, _ => false
  end.
           
Fixpoint reduceOnTheFly_aux00
  {X : Type}
  (pV : btree X)
  (allVs : list (list (Forest.node X)))
  (max : nat)
  (eqb_X : X -> X -> bool)
  (cmp0 cmp1 cmp2 cmp3 : pair X nat -> list (Forest.node X) -> list (Forest.node X) -> bool)
  (checkV : list (list (Forest.node X)) -> list (Forest.node X) -> bool)
  (default : nat)
  :=
  match max with
  | O => pV
  | S n =>
      let reducedtree :=
        reduceOnTheFly_aux1
          pV
          allVs
          nil
          false
          eqb_X
          cmp0 cmp1 cmp2 cmp3 checkV default
      in
      if cmp_pVs (parse reducedtree nil) allVs eqb_X then
        reducedtree
      else
        reduceOnTheFly_aux00
          reducedtree (parse reducedtree nil) n eqb_X cmp0 cmp1 cmp2 cmp3 checkV default
  end.

(***********************************)

(********* REDUCE ON THE FLY *********)

(***********************************)
(*
Fixpoint getAVals (A : iLF) (l : list (list (node iLF))) :=
  match l with
  | nil => nil
  | h::tl =>
      let vA := findVal A h 404 in
      (vA)::(getAVals A tl)
  end.

Fixpoint isAllT (l : list nat) :=
  match l with
  | nil => true
  | h::tl =>
      if negb (Nat.eqb h vT) then false
      else isAllT tl
  end.

Fixpoint thereIsNoT (l : list nat) :=
  match l with
  | nil => true
  | h::tl =>
      if Nat.eqb h vT then false
      else isAllT tl
  end.

Fixpoint isAllF (l : list nat) :=
  match l with
  | nil => true
  | h::tl =>
      if negb (Nat.eqb h vF) then false
      else isAllT tl
  end.
 *)

(*

Definition pruning_0 (a : nat) : bool := Nat.eqb a 1.
Definition pruning_1 (a : nat) : bool := Nat.eqb a 0.
Definition pruning_2 (a : nat) : bool := Nat.eqb a 2.

Definition pruning_4 (a : nat) (A B : LF) : bool := 
if eqb_lf A B then
(Nat.eqb a 0).


if CMP A a then 

*)

Definition reduceOnTheFly
  {X : Type}
  (A B : X)
  (pV : btree X)
  (eqb_X : X -> X -> bool)
  (cmp0 cmp1 cmp2 cmp3 : pair X nat -> list (Forest.node X) -> list (Forest.node X) -> bool)
  (checkV : list (list (Forest.node X)) -> list (Forest.node X) -> bool)
  (default : nat)
  :=
  let allVs := parse pV nil in
  if eqb_X A B then (* this means last column *)
    reduceOnTheFly_aux00 pV allVs (List.length allVs) eqb_X cmp0 cmp1 cmp2 cmp3 checkV default
  else
    reduceOnTheFly_aux0 pV allVs 1 eqb_X cmp0 cmp1 cmp2 cmp3 checkV default.


*)

(******************


Backtracking is a new, deep-based, algorithm for finding counter-models using rNmatrices.

The initial input is a formula A and a truth-value x.

The algorithm then tries to find a (valid) partial valuation v where v(A) = x, using the provided rNmatrix.


 **********************)

Inductive backtree (X : Type) :=
| bleaf : list X -> bool -> backtree X
| bun : X -> backtree X -> backtree X
| bbin : backtree X -> backtree X -> backtree X.

Arguments bleaf {X}.
Arguments bun {X}.
Arguments bbin {X}.

Check backtree nat.

Definition getCandidatesUn
  (unop : list (pair nat (list nat)))
  (v : nat)
  :=
  map
    (fun x => proj_l x)
    (filter
       (fun x => isElementInList v (proj_r x) Nat.eqb)
       unop).

Definition getCandidatesBin
  (binop : list (pair (pair nat nat) (list nat)))
  (v : nat)
  :=
  map
    (fun x => proj_l x)
    (filter
       (fun x => isElementInList v (proj_r x) Nat.eqb)
       binop).

(*

'iscons' is a function that receives two formulas, A and B, and return true iff A is consistent with B

Ex :
orb
          (andb
             (orb (eqb_lf A (~ B)) (eqb_lf B (~ A)))
             (Nat.eqb v v')
          )
          (andb
             (eqb_lf A B)
             (negb (Nat.eqb v v'))) *)
Fixpoint isConsistent
  {X : Type}
  (A : X)
  (v : nat)
  (iscons : pair X nat -> pair X nat -> bool)
  (atoms : list (pair X nat))
  :=
  match atoms with
  | nil => true
  | (B, v')::tl =>
      if negb (iscons (A, v) (B, v')) then
        false
      else
        isConsistent A v iscons tl
  end.

Fixpoint genbun
  {X : Type}
  (A : X)
  (l : list nat)
  (modulo : list (pair X nat))
  (V : list (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  :=
  match l with
  | nil => bleaf nil false
  | h::tl =>
      if isConsistent A h iscons V then
        if isEmpty tl then
          bun (A, h) (bleaf ((A, h)::modulo) true)
        else
          bbin
            (bun (A, h) (bleaf ((A, h)::modulo) true))
            (genbun A tl modulo V iscons)
      else
        genbun A tl modulo V iscons
  end.

Fixpoint genbbin
  {X : Type}
  (A B : X)
  (l : list (pair nat nat))
  (modulo : list (pair X nat))
  (V : list (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  :=
  match l with
  | nil => bleaf nil false
  | (a, b)::tl =>
      if andb (isConsistent A a iscons ((B, b)::V)) (isConsistent B b iscons ((A, a)::V)) then
        if isEmpty tl then
          bun (A, a) (bun (B, b) (bleaf ((A, a)::(B, b)::modulo) true))
        else
          bbin
            (bun (A, a) (bun (B, b) (bleaf ((A, a)::(B, b)::modulo) true)))
            (genbbin A B tl modulo V iscons)
      else
        genbbin A B tl modulo V iscons
  end.

Definition subformulas
  {X : Type}
  (A : X)
  (eqb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  :=
  sort
    (Forest.RemoveAmbiguity
       eqb_X
       (split A))
    (fun x y => (length_X x) <? (length_X y)).


Definition backtracking_aux2
  {X : Type}
  (l : list (pair X nat))
  (t : backtree (pair X nat))
  (V : list (pair X nat))
  (atomicMask : list nat)
  (logic: X -> nat -> list nat -> list (pair X nat) -> list (pair X nat) -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  :=
  match l with
  | nil => bleaf nil true
  | (A, v)::tl =>
      if isConsistent A v iscons V then
        logic A v atomicMask tl V
      else
        bleaf nil false
  end.

Fixpoint backtracking_aux1
  {X : Type}
  (t ct : backtree (pair X nat))
  (val : list (pair X nat))
  (atomicMask : list nat)
  (*(logic: X -> nat -> list nat -> list (pair X nat) -> list (pair X nat) -> backtree (pair X nat))*)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (eqb_X : X -> X -> bool)
  (filtro : list (pair X nat))
  :=
  match t with
  | bleaf lN b =>
      if isEmpty lN then
        bleaf nil b
      else
        if negb b then
          bleaf nil false
        else
          logic lN ct val atomicMask
  | bun (A, v) nt =>
      let fA := applyTo filtro A 8 eqb_X in
      if andb (negb (Nat.eqb fA 8)) (negb (Nat.eqb v fA)) then
        bleaf nil false
      else
        bun (A, v) (backtracking_aux1 nt ct ((A, v)::val) atomicMask logic iscons eqb_X filtro)
  | bbin nt1 nt2 =>
      bbin
        (backtracking_aux1 nt1 ct val atomicMask logic iscons eqb_X filtro)
        (backtracking_aux1 nt2 ct val atomicMask logic iscons eqb_X filtro)
  end.

Fixpoint backtracking_aux0
  {X : Type}
  (max : nat)
  (t : backtree (pair X nat))
  (atomicMask : list nat)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (eqb_X : X -> X -> bool)
  (filtro : list (pair X nat))
  : backtree (pair X nat) :=
  match max with
  | 0 => t
  | S n =>
      let nextt := backtracking_aux1 t t nil atomicMask logic iscons eqb_X filtro in
      backtracking_aux0 n nextt atomicMask logic iscons eqb_X filtro
  end.

Definition eqb_pair
  {X Y : Type}
  (cmp1 : X -> X -> bool)
  (cmp2 : Y -> Y -> bool)
  (a b : pair X Y)
  :=
  match a, b with
  | (x1, y1), (x2, y2) => andb (cmp1 x1 x2) (cmp2 y1 y2)
  end.

Fixpoint parsebt
  {X : Type}
  (t : backtree (pair X nat))
  (i : list (pair X nat))
  (eqb_X : X -> X -> bool)
  : list (list (pair X nat))
  := 
  match t with
  | bleaf lN b =>
      if (b) then i::nil
      else nil
  | bun n nT =>
      if isElementInList n i (eqb_pair eqb_X Nat.eqb) then
        parsebt nT i eqb_X
      else
        parsebt nT (n::i) eqb_X
  | bbin t1 t2 =>
      parsebt t1 i eqb_X ++ parsebt t2 i eqb_X
  end.

Definition backtracking
  {X : Type}
  (A : X)
  (V : list nat)
  (filtro : list (pair X nat))
  (atomicMask : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (filtro : list (pair X nat))
  :=
  if isElementInList A (map (fun x => proj_l x) filtro) eqb_X then
    let firstf := (A, applyTo filtro A 8 eqb_X) in
    let max := 2^(List.length (subformulas A eqb_X length_X split)) in
    let initial := bun firstf (bleaf [firstf] true) in
    parsebt (backtracking_aux0 max initial atomicMask logic iscons eqb_X filtro) nil eqb_X
  else
    let expbackt :=
      fold
        (fun x y => x++y)
        (map
           (fun v =>
              let max := 2^(List.length (subformulas A eqb_X length_X split)) in
              let initial := bun (A, v) (bleaf ((A, v)::nil) true) in
              parsebt (backtracking_aux0 max initial atomicMask logic iscons eqb_X filtro) nil eqb_X)
           V) nil in expbackt.

Fixpoint back2back
  {X : Type}
  (A : X)
  (V : list nat)
  (filtros : list (list (pair X nat)))
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  (v : list (pair X nat))
  (atomicMask : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  :=
  match filtros with
  | nil => nil
  | F::tl =>
      if negb (isEmpty F) then
        (filter
           (fun w  =>
              andb
                (validate (map (fun x => proj_l x) (filter (fun x => proj_r x) trules)) eqb_X v w)
                (validate (map (fun x => proj_l x) (filter (fun x => negb (proj_r x)) trules)) eqb_X w v)
           )
           (backtracking A V F atomicMask eqb_X leb_X length_X split logic iscons F)
        )
          ++(back2back A V tl trules v atomicMask eqb_X leb_X length_X split logic iscons)
      else
        back2back A V tl trules v atomicMask eqb_X leb_X length_X split logic iscons
  end.

(******

"Dependency calculus"

 ******)

Inductive dbtree (X : Type) :=
| dleaf : bool -> list (pair X nat) -> list (list (pair X nat)) -> dbtree X
| dun : list (pair (list (pair X nat)) nat) -> dbtree X -> dbtree X
| dbin : dbtree X -> dbtree X -> dbtree X.

Arguments dleaf {X}.
Arguments dun {X}.
Arguments dbin {X}.

Fixpoint isTriviallyValid
  {X : Type}
  (arrows : list (pair nat (list nat)))
  (v : list (pair X nat)) :=
  match v with
  | nil => true
  | (A, vA)::tl =>
      if isElementInList vA (map (fun x => proj_l x) arrows) Nat.eqb then
        false
      else
        isTriviallyValid arrows tl
  end.

Fixpoint rank
  {X : Type}
  (candidates : list (list (pair X nat)))
  (arrows : list (pair nat (list nat)))
  :=
  match candidates with
  | nil => nil
  | valA::tl =>
      let score :=
        fold
          plus
          (
            map
              (fun arrow =>
                 List.length
                   (filter
                      (fun x => Nat.eqb (proj_r x) (proj_l arrow))
                      valA)
              )
              arrows
          )
          0
      in
      (valA, score)::(rank tl arrows)
  end.

Fixpoint refinebt_aux3
  {X : Type}
  (A B : X)
  (V : list nat)
  (filtros : list (list (pair X nat)))
  (targets : list nat)
  (arrows : list (pair nat (list nat)))
  (arrow : nat)
  (v : list (pair X nat))
  (atomicMask : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match targets with
  | nil => nil
  | target::tl =>
      let expandedF :=
        if isEmpty filtros then [[(B, target)]]
        else
          map (fun x => (B, target)::x) filtros
      in
      let precandidates :=
        back2back B V expandedF trules v atomicMask
          eqb_X leb_X length_X split logic iscons in
      if isEmpty precandidates then
        nil
      else
        let candidates :=
          back2back A V expandedF trules v atomicMask
            eqb_X leb_X length_X split logic iscons
        in
        ((B, arrow),
          sort (rank candidates arrows) (fun x y => (proj_r x) <? (proj_r y)))
          ::(refinebt_aux3 A B V filtros tl
               arrows arrow v atomicMask
               eqb_X leb_X length_X split logic iscons trules)
  end.

Fixpoint refinebt_aux2
  {X : Type}
  (A : X)
  (V : list nat)
  (filtros : list (list (pair X nat)))
  (v vcp : list (pair X nat))
  (arrows : list (pair nat (list nat)))
  (arrow : nat)
  (targets : list nat)
  (candidates : list (pair (pair X nat) (list (pair (list (pair X nat)) nat))))
  (atomicMask : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match v with
  | nil => candidates
  | (B, vB)::tl =>
      if Nat.eqb vB arrow then
        let newC :=
          refinebt_aux3
            A B V filtros targets arrows arrow vcp atomicMask
            eqb_X leb_X length_X split logic iscons trules in
        if isEmpty newC then
          nil
        else
          refinebt_aux2
            A
            V
            filtros
            tl
            vcp
            arrows
            arrow
            targets
            (candidates++newC)
            atomicMask
            eqb_X leb_X length_X split logic iscons trules
      else
        refinebt_aux2
          A V filtros tl vcp arrows arrow targets candidates atomicMask
          eqb_X leb_X length_X split logic iscons trules
  end.

Fixpoint hasArrow {X : Type} (arrow : nat) (v : list (pair X nat)) :=
  match v with
  | nil => false
  | (A, vA)::tl =>
      if Nat.eqb arrow vA then
        true
      else
        hasArrow arrow tl
  end.

(*
Fixpoint incr_baseN_aux (min max : nat) (b : list nat) (control : bool) :=
  match b with
  | nil => nil
  | h::tl =>
      if control then
        if Nat.eqb h max then
          (min)::(incr_baseN_aux min max tl true)
        else
          (h+1)::(incr_baseN_aux min max tl false)
      else
        b
  end.

Fixpoint incr_baseN (min max n : nat) (b : list nat) :=
  match n with
  | O => b
  | S m =>
      let new := incr_baseN_aux min max b true in
      incr_baseN min max m new
  end.

Fixpoint gencomb_aux (min max counter : nat) (l : list nat) :=
  match counter with
  | O => (incr_baseN min max counter l)::nil
  | S n =>
      let val := incr_baseN min max counter l in
      val::(gencomb_aux min max n l)
  end.

Definition gencomb
  (min max : nat)
  (l : list nat)
  :=
  let base := (max - min) + 1 in
  let counter := base^(List.length l)-1 in
  gencomb_aux min max counter l.

Fixpoint createFilter_aux3
  {X : Type}
  (transformations : list (pair nat nat))
  (arrows : list (pair X nat))
  (comb : list nat)
  :=
  match arrows,comb with
  | (A, vA)::tl1, val::tl2 =>
      (A, applyTo transformations val val Nat.eqb)
        ::(createFilter_aux3 transformations tl1 tl2)
  | _, _ => nil
  end.

Fixpoint createFilter_aux2
  {X : Type}
  (transformations : list (pair nat nat))
  (arrows : list (pair X nat))
  (combinations : list (list nat))
  :=
  match combinations with
  | nil => nil
  | comb::tl =>
      (createFilter_aux3 transformations arrows comb)::
        (createFilter_aux2 transformations arrows tl)
  end.

Definition createFilter_aux
  {X : Type}
  (transformations : list (pair nat nat))
  (arrows : list (pair X nat))
  :=
  let base := map (fun _ => 0) arrows in
  let combinations := gencomb 0 ((List.length transformations)-1) base in
  createFilter_aux2 transformations arrows combinations.

Fixpoint createFilter
  {X : Type}
  (v : list (pair X nat))
  (trules : list (pair nat (list (pair nat nat))))
  :=
  match trules with
  | nil => nil
  | (arrow, transformations)::tl =>
      let arrows :=
        filter
          (fun x => Nat.eqb (proj_r x) arrow)
          v
      in
      (createFilter_aux transformations arrows)::(createFilter v tl)
  end.

Definition joinF_aux
  {X : Type}
  (l1 l2 : list (list (pair X nat)))
  :=
  fold
       (fun x y => x++y)
       (map
          (fun x =>
             (map
                (fun y =>
                     x++y
                )
                l2))
          l1)
       nil.

Fixpoint joinF_aux0
  {X : Type}
  (joined : list (list (pair X nat)))
  (l : list (list (list (pair X nat))))
  :=
  match l with
  | nil => joined
  | h::tl =>
      let nj := joinF_aux joined h in
      joinF_aux0 nj tl
  end.

Definition joinF
  {X : Type}
  (l : list (list (list (pair X nat))))
  :=
  match l with
  | nil => nil
  | h::tl =>
      joinF_aux0 h tl
  end.

*)

Inductive syntree {X : Type} :=
| sleaf : syntree
| sun : X -> syntree -> syntree
| sbin : syntree -> syntree -> syntree.

Fixpoint minComm_aux1
  {X : Type}
  (synA : syntree)
  (B : X)
  (V : list X)
  (eqb_X : X -> X -> bool)
  :=
  match synA with
  | sleaf =>
      nil
  | sun A nt =>
      if eqb_X A B then
        A::V
      else
        minComm_aux1 nt B (A::V) eqb_X
  | sbin nt1 nt2 =>
      (minComm_aux1 nt1 B V eqb_X)++(minComm_aux1 nt2 B V eqb_X)  
  end.

Fixpoint minComm_aux0
  {X : Type}
  (defA : X)
  (l1 l2 : list X)
  (eqb_X : X -> X -> bool)
  :=
  match l1 with
  | nil => defA
  | A::tl =>
      if isElementInList A l2 eqb_X then
        A
      else
        minComm_aux0 defA tl l2 eqb_X
  end.

Definition minComm
  {X : Type}
  (A B C : X)
  (genSynTree : X -> syntree)
  (eqb_X : X -> X -> bool)
  :=
  let stA := genSynTree A in
  let branchB := minComm_aux1 stA B nil eqb_X in
  let branchC := minComm_aux1 stA C nil eqb_X in
  minComm_aux0 A branchB branchC eqb_X.

Fixpoint refinebt_aux1
  {X : Type}
  (A : X)
  (V : list nat)
  (v : list (pair X nat))
  (arrows arrowscp : list (pair nat (list nat)))
  (cands : list (pair (pair X nat) (list (pair (list (pair X nat)) nat))))
  (atomicMask : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match arrows with
  | nil => cands
  | (arrow, targets)::tl =>
      if hasArrow arrow v then
        let candidates :=
          refinebt_aux2
            A
            V
            nil
            v v arrowscp arrow targets nil atomicMask
            eqb_X leb_X length_X split logic iscons trules
        in
        if isEmpty candidates then
          nil
        else
          refinebt_aux1 A V v tl
            arrowscp (candidates++cands) atomicMask
            eqb_X leb_X length_X split logic iscons trules
      else
        refinebt_aux1 A V v tl
          arrowscp cands atomicMask
          eqb_X leb_X length_X split logic iscons trules
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

Definition allCovered
  {X : Type}
  (l : list (pair (pair X nat) (list (pair (list (pair X nat)) nat)))) :=
  forallb
    (map
       (fun x =>
          negb (isEmpty (proj_r x)))
       l).

Fixpoint eqb_val
  {X : Type}
  (eqb_X : X -> X -> bool)
  (v w : list (pair X nat))
  :=
  match v with
  | nil => true
  | (A, vA)::tl =>
      let wA := applyTo w A 8 eqb_X in
      if Nat.eqb vA wA then
        eqb_val eqb_X tl w
      else
        false
  end.

Fixpoint createdbtree
  {X : Type}
  (deps : list (pair (pair X nat) (list (pair (list (pair X nat)) nat))))
  (newV : list (pair X nat))
  (visited : list (list (pair X nat)))
  :=
  match deps with
  | nil => dleaf false newV visited
  | (_, candidates)::tl =>
      if isEmpty tl then
        dun 
          (explode candidates)
          (dleaf false (proj_l (pop candidates (nil, 0))) (newV::visited))
      else
        dbin
          (dun
             (explode candidates)
             (dleaf false (proj_l (pop candidates (nil, 0))) (newV::visited))
          )
          (createdbtree tl newV visited)
  end.

Definition findBestA
  {X : Type}
  (A : X)
  (v : list (pair X nat))
  (dots : list nat)
  (genSynTree : X -> syntree)
  (eqb_X : X -> X -> bool):=
  let candidates :=
    map
      (fun x => proj_l x)
      (filter
         (fun val =>
            isElementInList (proj_r val) dots Nat.eqb
         )
         v)
  in
  if negb (isEmpty candidates) then
    let firstc := pop candidates A in
    fold
      (fun B C =>
         minComm A B C genSynTree eqb_X
      )
      candidates
      firstc
  else
    A.

Definition refinebt_aux
  {X : Type}
  (A : X)
  (V : list nat)
  (arrows : list (pair nat (list nat)))
  (v : list (pair X nat))
  (visited : list (list (pair X nat)))
  (atomicMask : list nat)
  (dots : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  if negb (isTriviallyValid arrows v) then
    let bestA := findBestA A v dots genSynTree eqb_X in
    let candidates :=
      refinebt_aux1 bestA V v arrows arrows nil atomicMask
        eqb_X leb_X length_X split logic iscons trules
    in
    if allCovered candidates then
      createdbtree candidates v visited
    else
      dleaf false v nil
  else
    dleaf true v visited.

Fixpoint dbtreecons
  {X : Type}
  (A : X)
  (V : list nat)
  (arrows : list (pair nat (list nat)))
  (t : dbtree X)
  (atomicMask dots : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match t with
  | dleaf status v visited =>
      if isEmpty v then
        dleaf status v visited
      else
        if isElementInList v visited (eqb_val eqb_X) then
          dleaf true v (visited)
        else
          refinebt_aux A V arrows v visited atomicMask dots
            eqb_X leb_X length_X split logic iscons genSynTree trules
  | dun candidates nt =>
      match nt with
      | dleaf status v visited =>
          if status then
            dleaf true v visited
          else
            let next :=
              dbtreecons A V arrows nt atomicMask dots
                eqb_X leb_X length_X split logic iscons genSynTree trules
            in
            dun candidates next
      | _ =>
          let next :=
            dbtreecons A V arrows nt atomicMask dots
              eqb_X leb_X length_X split logic iscons genSynTree trules
          in
          dun candidates next
      end           
  | dbin nt1 nt2 =>
      match nt1, nt2 with
      | dleaf nstat1 v1 visited1, dleaf nstat2 v2 visited2 =>
          if andb nstat1 nstat2 then
            if List.length visited1 <? List.length visited2 then
              dleaf true v1 visited1
            else
              dleaf true v2 visited2
          else
            if nstat1 then
              dleaf true v1 visited1
            else
              if nstat2 then
                dleaf true v2 visited2
              else
                dleaf false nil nil
      | dleaf nstat v visited, _ =>
          if nstat then
            dbin
              (dleaf nstat v visited)
              (dbtreecons A V arrows nt2 atomicMask dots eqb_X leb_X length_X split logic iscons genSynTree trules)
          else
            dleaf nstat v nil
      | _, dleaf nstat v visited =>
          if nstat then
            dbin
              (dbtreecons A V arrows nt1 atomicMask dots eqb_X leb_X length_X split logic iscons genSynTree trules)
              (dleaf nstat v visited)
          else
            dleaf nstat v nil
      | dun cand1 nt1, dun cand2 nt2 =>
          if (List.length cand1) <? (List.length cand2) then
            dbin
              (dbtreecons A V arrows nt1 atomicMask dots eqb_X leb_X length_X split logic iscons genSynTree trules)
              (dun cand2 nt2)
          else
            dbin
              (dun cand1 nt1)
              (dbtreecons A V arrows nt2 atomicMask dots eqb_X leb_X length_X split logic iscons genSynTree trules)
      | _, _ =>
          dbin
            (dbtreecons A V arrows nt1 atomicMask dots eqb_X leb_X length_X split logic iscons genSynTree trules)
            (dbtreecons A V arrows nt2 atomicMask dots eqb_X leb_X length_X split logic iscons genSynTree trules)
      end
  end.

Fixpoint refinebt_aux01
  {X : Type}
  (A : X)
  (V : list nat)
  (arrows : list (pair nat (list nat)))
  (deps : dbtree X)
  (candidate : list (pair X nat))
  (max : nat)
  (atomicMask dots : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match max with
  | O => deps
  | S n =>
      let nextdeps :=
        dbtreecons A V arrows deps atomicMask dots
          eqb_X leb_X length_X split logic iscons genSynTree trules
      in
      match nextdeps with
      | dleaf stat w visited =>
          if stat then
            dleaf true candidate visited
          else
            dleaf false nil nil 
      | _ =>
          refinebt_aux01 A V arrows nextdeps candidate n atomicMask dots
            eqb_X leb_X length_X split logic iscons genSynTree trules
      end
  end.

Fixpoint refinebt_aux00
  {X : Type}
  (A : X)
  (V : list nat)
  (arrows : list (pair nat (list nat)))
  (max : nat)
  (candidates : list (pair (list (pair X nat)) nat))
  (atomicMask dots : list nat)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match candidates with
  | nil => nil
  | h::tl =>
      let start := dleaf false (proj_l h) nil in
      (refinebt_aux01 A V arrows start (proj_l h) max atomicMask dots eqb_X leb_X length_X split logic iscons genSynTree trules)
        ::(refinebt_aux00 A V arrows max tl atomicMask dots eqb_X leb_X length_X split logic iscons genSynTree trules)
  end.
(*
Fixpoint convertToBt
  {X : Type}
  (m : list (list (Forest.node X)))
  :=
  match m with
  | nil => nil
  | val::tl =>
      (map
        (fun node =>
           match node with
           | Forest.Node _ vA A => (A, vA)
           end
        )
        val)::(convertToBt tl)
  end.
*)
Definition checkbt
  {X : Type}
  (A : X)
  (v : nat)
  (V : list nat)
  (arrows : list (pair nat (list nat)))
  (atomicMask dots : list nat)
  (val : list (pair X nat))
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  (max : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  let validation :=
    pop
      (refinebt_aux00 A V arrows max
         (sort (rank [val] arrows)
            (fun x y => (proj_r x) <? (proj_r y)))
         atomicMask dots
         eqb_X leb_X length_X split logic iscons genSynTree trules
      )
      (dleaf false nil nil)
  in
  match validation with
  | dleaf bc l1 l2  =>
      if bc then
        true
      else
        false
  | _ => true
  end.

(******************)

(** Depth first tree gen **)

(* Semantic tree *)

Inductive semtree {X : Type} :=
| smstatus : bool -> list (pair X nat) -> semtree
| smleaf : list X -> list (pair X nat) -> semtree
| smun : pair X nat -> semtree -> semtree
| smbin : semtree -> semtree -> semtree.

Fixpoint gensemtree
  {X : Type}
  (A : X)
  (v : list nat)
  (pv : list (pair X nat))
  (toExpand : list X)
  :=
  match v with
  | nil => smleaf toExpand pv
  | vA::tl =>
      if isEmpty tl then
        smun (A, vA) (smleaf toExpand ((A, vA)::pv))
      else
        smbin
          (smun (A, vA) (smleaf toExpand ((A, vA)::pv)))
          (gensemtree A tl pv toExpand)
  end.

Fixpoint expandsemtree
  {X : Type}
  (A : X)
  (goal : nat)
  (V : list nat)
  (t : semtree)
  (localpv : list (pair X nat))
  (arrows : list (pair nat (list nat)))
  (atomicMask dots : list nat)
  (count : nat)
  (logicst : X -> list (pair X nat) -> list X -> semtree)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  (max : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match t with
  | smstatus b pv => smstatus b pv 
  | smleaf toExpand pv =>
      if negb (isEmpty toExpand) then
        let B := pop toExpand A in
        logicst B pv (explode toExpand)
      else
        let vA := applyTo pv A 8 eqb_X in
        if Nat.eqb vA goal then
          let checkpv :=
            checkbt
              A
              vA
              V arrows atomicMask dots pv
              eqb_X leb_X length_X split logic iscons genSynTree max trules
          in
          if checkpv then
            smstatus true pv
          else
            smstatus false nil
        else
          smstatus false nil
  | smun (C, vC) nt =>
      match nt with
      | smstatus b pv =>
          if b then
            smstatus b pv
          else
            smstatus false nil
      | _ =>
            smun (C, vC)
              (expandsemtree A goal V nt ((C, vC)::localpv)
                 arrows atomicMask dots (count) logicst
                 eqb_X leb_X length_X split logic iscons genSynTree max trules)
      end
  | smbin nt1 nt2 =>
      let next1 := expandsemtree A goal V nt1 localpv arrows
                     atomicMask dots (count) logicst
                     eqb_X leb_X length_X split logic iscons genSynTree max trules in
      match next1 with
      | smstatus b pv =>
          if b then
            smstatus b pv
          else
            let next2 := expandsemtree A goal V nt2 localpv arrows
                           atomicMask dots count logicst
                           eqb_X leb_X length_X split logic iscons genSynTree max trules
            in
            match next2 with
            | smstatus b pv =>
                if b then
                  smstatus b pv
                else
                  smstatus false nil
            | _ =>
                next2
            end 
      | _ =>
          if count <? 2 then
            smbin
              next1
              nt2
          else
            smbin
              next1
              (expandsemtree A goal V nt2 localpv arrows atomicMask dots 0
                 logicst eqb_X leb_X length_X split logic iscons genSynTree max trules)
      end
  end.

Definition maketreedf
  {X : Type}
  (A : X)
  (goal : nat)
  (V : list nat)
  (t : semtree)
  (arrows : list (pair nat (list nat)))
  (atomicMask dots : list nat)
  (logicst : X -> list (pair X nat) -> list X -> semtree)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  (max : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  expandsemtree
    A
    goal
    V
    t
    nil
    arrows
    atomicMask
    dots
    0
    logicst
    eqb_X leb_X length_X split logic iscons genSynTree max trules.

Fixpoint rundf
  {X : Type}
  (A : X)
  (goal : nat)
  (V : list nat)
  (t : semtree)
  (arrows : list (pair nat (list nat)))
  (atomicMask dots : list nat)
  (logicst : X -> list (pair X nat) -> list X -> semtree)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  (max maxcp : nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  :=
  match max with
  | O => t
  | S n =>
      let nt :=
        maketreedf
          A goal V t
          arrows
          atomicMask
          dots
          logicst eqb_X leb_X length_X split logic iscons genSynTree maxcp trules
      in
      match nt with
      | smstatus b pv => nt
      | _ => rundf
               A goal V nt
               arrows
               atomicMask dots
               logicst
               eqb_X leb_X
               length_X
               split
               logic
               iscons
               genSynTree
               n maxcp trules
      end
  end.

Definition createinit
  {X : Type}
  (subA : list X)
  (atomval : list (pair X nat))
  (length_X : X -> nat)
  :=
  let atoms := filter (fun x => Nat.eqb (length_X x) 0) subA in
  let complex := filter (fun x => negb (Nat.eqb (length_X x) 0)) subA in
  smleaf
    complex
    atomval.

Definition depfirst
  {X : Type}
  (A : X)
  (goal : nat)
  (atomval : list (pair X nat))
  (max : nat)
  (V : list nat)
  (trules : list (pair (pair nat (list (X -> Target (pair X (list nat))))) bool))
  (arrows : list (pair nat (list nat)))
  (atomicMask dots : list nat)
  (logicst : X -> list (pair X nat) -> list X -> semtree)
  (eqb_X leb_X : X -> X -> bool)
  (length_X : X -> nat)
  (split : X -> list X)
  (logic : list (pair X nat) -> backtree (pair X nat) -> list (pair X nat) -> list nat -> backtree (pair X nat))
  (iscons : pair X nat -> pair X nat -> bool)
  (genSynTree : X -> syntree)
  :=
  let subA := subformulas A eqb_X length_X split in
  rundf
    A
    goal
    V
    (createinit subA atomval length_X)
    arrows
    atomicMask dots
    logicst
    eqb_X
    leb_X
    length_X
    split
    logic
    iscons
    genSynTree
    max max trules.

Fixpoint parsesemt
  {X : Type}
  (t : semtree)
  (i : list (pair X nat))
  (eqb_X : X -> X -> bool)
  : list (list (pair X nat))
  := 
  match t with
  | smstatus b _ => i::nil
  | smleaf lN b => i::nil
  | smun n nT =>
      if isElementInList n i (eqb_pair eqb_X Nat.eqb) then
        parsesemt nT i eqb_X
      else
        parsesemt nT (n::i) eqb_X
  | smbin t1 t2 =>
      parsesemt t1 i eqb_X ++ parsesemt t2 i eqb_X
  end.
