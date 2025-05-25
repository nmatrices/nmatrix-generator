(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val eqb : nat -> nat -> bool **)

let rec eqb n m =
  match n with
  | O -> (match m with
          | O -> true
          | S _ -> false)
  | S n' -> (match m with
             | O -> false
             | S m' -> eqb n' m')

(** val leb : nat -> nat -> bool **)

let rec leb n m =
  match n with
  | O -> true
  | S n' -> (match m with
             | O -> false
             | S m' -> leb n' m')

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

type ('x, 'y) pair =
| Pair of 'x * 'y

(** val proj_l : ('a1, 'a2) pair -> 'a1 **)

let proj_l = function
| Pair (a, _) -> a

(** val proj_r : ('a1, 'a2) pair -> 'a2 **)

let proj_r = function
| Pair (_, b) -> b

(** val filter0 : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter0 test = function
| [] -> []
| h::t -> if test h then h::(filter0 test t) else filter0 test t

(** val insert : 'a1 -> 'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 list **)

let rec insert i l f =
  match l with
  | [] -> i::[]
  | h::t -> if f i h then i::(h::t) else h::(insert i t f)

(** val sort : 'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 list **)

let rec sort l f =
  match l with
  | [] -> []
  | h::t -> insert h (sort t f) f

(** val pop : 'a1 list -> 'a1 -> 'a1 **)

let pop l default =
  match l with
  | [] -> default
  | h::_ -> h

type 'x node =
| Node of nat * 'x

(** val eqb_node : ('a1 -> 'a1 -> bool) -> 'a1 node -> 'a1 node -> bool **)

let eqb_node cmp n1 n2 =
  let Node (nn1, nlf1) = n1 in
  let Node (nn2, nlf2) = n2 in (&&) (eqb nn1 nn2) (cmp nlf1 nlf2)

type 'x btree =
| Leaf of bool
| Alpha of 'x node * 'x btree
| Beta of 'x btree * 'x btree

(** val isLFAlreadyOnList : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec isLFAlreadyOnList cmp l = function
| [] -> false
| h::tl -> (||) (cmp l h) (isLFAlreadyOnList cmp l tl)

(** val removeAmbiguity : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec removeAmbiguity cmp = function
| [] -> []
| h::tl ->
  if isLFAlreadyOnList cmp h tl
  then removeAmbiguity cmp tl
  else h::(removeAmbiguity cmp tl)

(** val decompose :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> 'a1 -> 'a1
    list **)

let decompose eqb_AB leb_AB split l =
  sort (removeAmbiguity eqb_AB (split l)) leb_AB

(** val getAtoms :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 -> 'a1 list)
    -> 'a1 -> 'a1 list **)

let getAtoms eqb_AB leb_AB length_A split a =
  filter0 (fun a0 -> leb (length_A a0) O) (decompose eqb_AB leb_AB split a)

(** val getComposed :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 -> 'a1 list)
    -> 'a1 -> 'a1 list **)

let getComposed eqb_AB leb_AB length_A split a =
  filter0 (fun a0 -> negb (leb (length_A a0) O)) (decompose eqb_AB leb_AB split a)

(** val makeInitialTree_aux : 'a1 -> nat list -> 'a1 btree **)

let rec makeInitialTree_aux a = function
| [] -> Leaf true
| h::tl ->
  if eqb (length tl) O
  then Alpha ((Node (h, a)), (Leaf true))
  else Beta ((Alpha ((Node (h, a)), (Leaf true))), (makeInitialTree_aux a tl))

(** val makeInitialTree_aux0 : 'a1 -> nat list -> 'a1 btree -> 'a1 btree **)

let rec makeInitialTree_aux0 a v = function
| Leaf _ -> makeInitialTree_aux a v
| Alpha (n, nt) -> Alpha (n, (makeInitialTree_aux0 a v nt))
| Beta (nt1, nt2) ->
  Beta ((makeInitialTree_aux0 a v nt1), (makeInitialTree_aux0 a v nt2))

(** val makeInitialTree : 'a1 list -> nat list -> 'a1 btree -> 'a1 btree **)

let rec makeInitialTree ls v t =
  match ls with
  | [] -> t
  | h::tl -> let ntree = makeInitialTree_aux0 h v t in makeInitialTree tl v ntree

(** val make_aux :
    'a1 -> 'a1 btree list -> 'a1 btree -> 'a1 list -> ('a1 -> 'a1 -> 'a1 btree -> nat
    list -> 'a1 btree list -> 'a1 btree) -> nat list -> 'a1 btree **)

let rec make_aux a allVal valT lcomp logic v =
  match lcomp with
  | [] -> valT
  | h::tl -> let ntree = logic a h valT v allVal in make_aux a allVal ntree tl logic v

(** val make :
    'a1 -> 'a1 btree list -> 'a1 btree list -> 'a1 list -> ('a1 -> 'a1 -> 'a1 btree ->
    nat list -> 'a1 btree list -> 'a1 btree) -> nat list -> 'a1 btree list **)

let rec make a allVal allValcp lcomp logic v =
  match allVal with
  | [] -> []
  | h::tl -> (make_aux a allValcp h lcomp logic v)::(make a tl allValcp lcomp logic v)

(** val parse : 'a1 btree -> 'a1 node list -> 'a1 node list list **)

let rec parse t i =
  match t with
  | Leaf b -> if b then i::[] else []
  | Alpha (n, nT) -> parse nT (n::i)
  | Beta (t1, t2) -> app (parse t1 i) (parse t2 i)

(** val parseVal : 'a1 btree list -> 'a1 node list list list **)

let rec parseVal = function
| [] -> []
| h::tl -> (parse h [])::(parseVal tl)

(** val flattenList : 'a1 list list list -> 'a1 list list **)

let rec flattenList = function
| [] -> []
| h::tl -> app h (flattenList tl)

(** val reverseListOrder : 'a1 list -> 'a1 list **)

let rec reverseListOrder = function
| [] -> []
| h::tl -> app (reverseListOrder tl) (h::[])

(** val makeWithoutPrune :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 -> 'a1 list)
    -> ('a1 -> 'a1 -> 'a1 btree -> nat list -> 'a1 btree list -> 'a1 btree) -> 'a1 ->
    'a1 -> nat list -> 'a1 node list list **)

let makeWithoutPrune eqb_AB leb_AB length_A split logic _ a v =
  let init =
    (makeInitialTree (getAtoms eqb_AB leb_AB length_A split a) v (Leaf true))::[]
  in
  let sub_A = getComposed eqb_AB leb_AB length_A split a in
  let forest = make a init init sub_A logic v in flattenList (parseVal forest)

(** val isElementInList : 'a1 -> 'a1 list -> ('a1 -> 'a1 -> bool) -> bool **)

let rec isElementInList n l cmp =
  match l with
  | [] -> false
  | h::tl -> if cmp n h then true else isElementInList n tl cmp

type frame =
| Reflexive
| Transitive

(** val eqb_frame : frame -> frame -> bool **)

let eqb_frame f1 f2 =
  match f1 with
  | Reflexive -> (match f2 with
                  | Reflexive -> true
                  | Transitive -> false)
  | Transitive -> (match f2 with
                   | Reflexive -> false
                   | Transitive -> true)

(** val refl : frame list -> bool **)

let refl constraints =
  isElementInList Reflexive constraints eqb_frame

(** val trans : frame list -> bool **)

let trans constraints =
  isElementInList Transitive constraints eqb_frame

(** val findVal : 'a1 -> 'a1 node list -> ('a1 -> 'a1 -> bool) -> nat -> nat **)

let rec findVal a v eqb_X default =
  match v with
  | [] -> default
  | h::tl ->
    let Node (val1, b) = h in if eqb_X a b then val1 else findVal a tl eqb_X default

(** val isCompatible :
    'a1 node list -> 'a1 node list -> (nat -> bool) -> (nat -> bool) -> bool **)

let rec isCompatible v1 v2 cmp2 cmp3 =
  match v1 with
  | [] -> true
  | h1::tl1 ->
    (match v2 with
     | [] -> true
     | h2::tl2 ->
       let Node (val1, _) = h1 in
       if cmp2 val1
       then let Node (val2, _) = h2 in
            if cmp3 val2 then isCompatible tl1 tl2 cmp2 cmp3 else false
       else isCompatible tl1 tl2 cmp2 cmp3)

(** val restriction_aux2_v2 :
    'a1 -> (nat, 'a1 node list) pair list -> 'a1 node list -> (nat -> bool) -> (nat ->
    bool) -> (nat -> bool) -> ('a1 -> 'a1 -> bool) -> nat -> nat list **)

let rec restriction_aux2_v2 a val1 cval cmp0 cmp1 cmp2 eqb_X default =
  match val1 with
  | [] -> []
  | h::tl ->
    let index = proj_l h in
    let vals = proj_r h in
    let vA = findVal a vals eqb_X default in
    if cmp0 vA
    then let compatible = isCompatible cval vals cmp1 cmp2 in
         if compatible
         then index::(restriction_aux2_v2 a tl cval cmp0 cmp1 cmp2 eqb_X default)
         else restriction_aux2_v2 a tl cval cmp0 cmp1 cmp2 eqb_X default
    else restriction_aux2_v2 a tl cval cmp0 cmp1 cmp2 eqb_X default

(** val restriction_aux1_v2 :
    (nat, 'a1 node list) pair list -> 'a1 node list -> 'a1 node list -> ('a1, nat
    list) pair list -> (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> (nat ->
    bool) -> ('a1 -> 'a1 -> bool) -> nat -> ('a1, nat list) pair list **)

let rec restriction_aux1_v2 val1 cval cpcval allValidators cmp0 cmp1 cmp2 cmp3 eqb_X default =
  match cval with
  | [] -> allValidators
  | h::tl ->
    let Node (v, a) = h in
    if cmp0 v
    then let validators =
           restriction_aux2_v2 a val1 cpcval cmp1 cmp2 cmp3 eqb_X default
         in
         restriction_aux1_v2 val1 tl cpcval ((Pair (a, validators))::allValidators)
           cmp0 cmp1 cmp2 cmp3 eqb_X default
    else restriction_aux1_v2 val1 tl cpcval allValidators cmp0 cmp1 cmp2 cmp3 eqb_X
           default

(** val restriction_aux_v2 :
    (nat, 'a1 node list) pair list -> (nat, 'a1 node list) pair list -> (nat -> bool)
    -> (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> ('a1 -> 'a1 -> bool) -> nat
    -> (nat, ('a1, nat list) pair list) pair list **)

let rec restriction_aux_v2 val1 cpval cmp0 cmp1 cmp2 cmp3 eqb_X default =
  match val1 with
  | [] -> []
  | h::tl ->
    let index = proj_l h in
    let vals = proj_r h in
    let allValidators =
      restriction_aux1_v2 cpval vals vals [] cmp0 cmp1 cmp2 cmp3 eqb_X default
    in
    (Pair (index,
    allValidators))::(restriction_aux_v2 tl cpval cmp0 cmp1 cmp2 cmp3 eqb_X default)

(** val removeAtIndexedList : nat -> (nat, 'a1) pair list -> (nat, 'a1) pair list **)

let rec removeAtIndexedList n = function
| [] -> []
| h::tl ->
  let index = proj_l h in if Nat.eqb index n then tl else h::(removeAtIndexedList n tl)

(** val thereSomeNil : ('a1, nat list) pair list -> bool **)

let rec thereSomeNil = function
| [] -> false
| h::tl ->
  let vals = proj_r h in if Nat.eqb (length vals) O then true else thereSomeNil tl

(** val removeNonValid :
    (nat, 'a1 node list) pair list -> (nat, ('a1, nat list) pair list) pair list ->
    (nat, 'a1 node list) pair list **)

let rec removeNonValid val1 = function
| [] -> val1
| h::tl ->
  let index = proj_l h in
  let validators = proj_r h in
  if thereSomeNil validators
  then removeNonValid (removeAtIndexedList index val1) tl
  else removeNonValid val1 tl

(** val isThereSomethingToRemove :
    (nat, ('a1, nat list) pair list) pair list -> bool **)

let rec isThereSomethingToRemove = function
| [] -> false
| h::tl ->
  let validators = proj_r h in
  if thereSomeNil validators then true else isThereSomethingToRemove tl

(** val restriction_aux0_v2 :
    (nat, 'a1 node list) pair list -> nat -> (nat -> bool) -> (nat -> bool) -> (nat ->
    bool) -> (nat -> bool) -> ('a1 -> 'a1 -> bool) -> nat -> ((nat, 'a1 node list)
    pair list, (nat, ('a1, nat list) pair list) pair list) pair list **)

let rec restriction_aux0_v2 val1 max0 cmp0 cmp1 cmp2 cmp3 eqb_X default =
  match max0 with
  | O -> (Pair (val1, []))::[]
  | S n ->
    let validators = restriction_aux_v2 val1 val1 cmp0 cmp1 cmp2 cmp3 eqb_X default in
    let newMatrix = removeNonValid val1 validators in
    if isThereSomethingToRemove validators
    then (Pair (val1,
           validators))::(restriction_aux0_v2 newMatrix n cmp0 cmp1 cmp2 cmp3 eqb_X
                           default)
    else (Pair (val1, validators))::[]

(** val indexingList : 'a1 list -> nat -> (nat, 'a1) pair list **)

let rec indexingList l i =
  match l with
  | [] -> []
  | h::tl -> (Pair (i, h))::(indexingList tl (add i (S O)))

(** val restriction_v2 :
    'a1 node list list -> (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> (nat ->
    bool) -> ('a1 -> 'a1 -> bool) -> nat -> ((nat, 'a1 node list) pair list, (nat,
    ('a1, nat list) pair list) pair list) pair list **)

let restriction_v2 val1 cmp0 cmp1 cmp2 cmp3 eqb_X =
  let indexedVals = indexingList val1 (S O) in
  restriction_aux0_v2 indexedVals (length indexedVals) cmp0 cmp1 cmp2 cmp3 eqb_X

(** val makeIt :
    'a1 -> nat list -> ('a1 -> 'a1 -> 'a1 btree -> nat list -> 'a1 btree list -> 'a1
    btree) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 ->
    'a1 list) -> 'a1 node list list **)

let makeIt a v logic eqb_X leb_X length_X split =
  makeWithoutPrune eqb_X leb_X length_X split logic a a v

(** val nodeToNatAll_aux2 : 'a1 node list -> nat list **)

let rec nodeToNatAll_aux2 = function
| [] -> []
| h::tl -> let Node (val1, _) = h in val1::(nodeToNatAll_aux2 tl)

(** val nodeToNatAll_aux :
    (nat, 'a1 node list) pair list -> (nat, nat list) pair list **)

let rec nodeToNatAll_aux = function
| [] -> []
| h::tl ->
  let index = proj_l h in
  let vals = proj_r h in
  (Pair (index, (reverseListOrder (nodeToNatAll_aux2 vals))))::(nodeToNatAll_aux tl)

(** val nodeToNatAll :
    ((nat, 'a1 node list) pair list, (nat, ('a1, nat list) pair list) pair list) pair
    list -> ((nat, nat list) pair list, (nat, ('a1, nat list) pair list) pair list)
    pair list **)

let rec nodeToNatAll = function
| [] -> []
| h::tl ->
  let indexedVals = proj_l h in
  let validators = proj_r h in
  (Pair ((nodeToNatAll_aux indexedVals), validators))::(nodeToNatAll tl)

(** val subf :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> 'a1
    list **)

let subf a eqb_X geb_X split =
  reverseListOrder (decompose eqb_X geb_X split a)

(** val restrictionSteps :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1
    -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat -> bool) -> (nat -> bool) -> (nat ->
    bool) -> (nat -> bool) -> nat -> ('a1 list, ((nat, nat list) pair list, (nat,
    ('a1, nat list) pair list) pair list) pair list) pair **)

let restrictionSteps a matrix eqb_X _ geb_X split cmp0 cmp1 cmp2 cmp3 default =
  let res = nodeToNatAll (restriction_v2 matrix cmp0 cmp1 cmp2 cmp3 eqb_X default) in
  let subs = subf a eqb_X geb_X split in Pair (subs, res)

(** val restrictionStepsWithNode :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1
    -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat -> bool) -> (nat -> bool) -> (nat ->
    bool) -> (nat -> bool) -> nat -> ('a1 list, ((nat, 'a1 node list) pair list, (nat,
    ('a1, nat list) pair list) pair list) pair list) pair **)

let restrictionStepsWithNode a matrix eqb_X _ geb_X split cmp0 cmp1 cmp2 cmp3 default =
  let res = restriction_v2 matrix cmp0 cmp1 cmp2 cmp3 eqb_X default in
  let subs = subf a eqb_X geb_X split in Pair (subs, res)

(** val getLast : 'a1 list -> 'a1 list **)

let rec getLast = function
| [] -> []
| h::tl -> if Nat.eqb (length tl) O then h::[] else getLast tl

(** val computeTable :
    ('a1 list, ((nat, nat list) pair list, (nat, ('a1, nat list) pair list) pair list)
    pair list) pair -> ('a1 list, (nat, nat list) pair list) pair **)

let computeTable steps =
  Pair ((proj_l steps), (proj_l (pop (getLast (proj_r steps)) (Pair ([], [])))))

(** val computeTableWithNode :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1
    -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat -> bool) -> (nat -> bool) -> (nat ->
    bool) -> (nat -> bool) -> nat -> ('a1 list, (nat, 'a1 node list) pair list) pair **)

let computeTableWithNode a matrix eqb_X leb_X geb_X split cmp0 cmp1 cmp2 cmp3 default =
  let steps =
    restrictionStepsWithNode a matrix eqb_X leb_X geb_X split cmp0 cmp1 cmp2 cmp3
      default
  in
  Pair ((proj_l steps), (proj_l (pop (getLast (proj_r steps)) (Pair ([], [])))))

(** val computeValidators :
    ('a1 list, ((nat, nat list) pair list, (nat, ('a1, nat list) pair list) pair list)
    pair list) pair -> (nat, ('a1, nat list) pair list) pair list **)

let computeValidators steps =
  proj_r (pop (getLast (proj_r steps)) (Pair ([], [])))

(** val eqb_lX : 'a1 list -> 'a1 list -> ('a1 -> 'a1 -> bool) -> bool **)

let rec eqb_lX l1 l2 cmp =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | h1::tl1 ->
    (match l2 with
     | [] -> false
     | h2::tl2 -> if cmp h1 h2 then eqb_lX tl1 tl2 cmp else false)

(** val isInList : nat -> nat list -> bool **)

let rec isInList n = function
| [] -> false
| h::tl -> if Nat.eqb n h then true else isInList n tl

(** val arrangeKM_aux3 : nat list -> nat list -> nat list **)

let rec arrangeKM_aux3 l ws =
  match l with
  | [] -> ws
  | h::tl -> if isInList h ws then arrangeKM_aux3 tl ws else arrangeKM_aux3 tl (h::ws)

(** val arrangeKM_aux2 : nat -> ('a1, nat list) pair list -> nat list -> nat list **)

let rec arrangeKM_aux2 v l ws =
  match l with
  | [] -> ws
  | h::tl -> let new0 = arrangeKM_aux3 (proj_r h) ws in arrangeKM_aux2 v tl new0

(** val arrangeKM_aux1 :
    (nat, ('a1, nat list) pair list) pair list -> (nat, nat list) pair list **)

let rec arrangeKM_aux1 = function
| [] -> []
| h::tl ->
  let index = proj_l h in
  let valds = proj_r h in
  (Pair (index, (arrangeKM_aux2 index valds [])))::(arrangeKM_aux1 tl)

(** val arrangeKM :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1
    -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat -> bool) -> (nat -> bool) -> (nat ->
    bool) -> (nat -> bool) -> nat -> (nat, nat list) pair list **)

let arrangeKM a matrix eqb_X leb_X geb_X split cmp0 cmp1 cmp2 cmp3 default =
  let steps =
    restrictionSteps a matrix eqb_X leb_X geb_X split cmp0 cmp1 cmp2 cmp3 default
  in
  let validators = computeValidators steps in arrangeKM_aux1 validators

type 'x signedLF =
| Sign of bool * 'x

type 'x node0 =
| Node0 of 'x signedLF * nat
| Rel of bool * nat * nat

(** val eqb_SignedLF : 'a1 signedLF -> 'a1 signedLF -> ('a1 -> 'a1 -> bool) -> bool **)

let eqb_SignedLF s1 s2 cmp =
  let Sign (b1, l1) = s1 in
  let Sign (b2, l2) = s2 in if xorb b1 b2 then false else cmp l1 l2

(** val min : 'a1 node0 -> nat **)

let min = function
| Node0 (_, k) -> k
| Rel (_, k, _) -> k

(** val max : 'a1 node0 -> nat **)

let max = function
| Node0 (_, k) -> k
| Rel (_, _, j) -> j

(** val eqb_node_R : 'a1 node0 -> 'a1 node0 -> bool **)

let eqb_node_R a b =
  match a with
  | Node0 (_, _) -> false
  | Rel (_, k, j) ->
    (match b with
     | Node0 (_, _) -> false
     | Rel (_, k1, j1) -> (&&) (Nat.eqb k k1) (Nat.eqb j j1))

(** val eqb_node0 : ('a1 -> 'a1 -> bool) -> 'a1 node0 -> 'a1 node0 -> bool **)

let eqb_node0 cmp a b =
  match a with
  | Node0 (s1, k1) ->
    (match b with
     | Node0 (s2, k2) -> if Nat.eqb k1 k2 then eqb_SignedLF s1 s2 cmp else false
     | Rel (_, _, _) -> false)
  | Rel (_, _, _) -> eqb_node_R a b

(** val checkIfNodeIsInList :
    'a1 node0 -> 'a1 node0 list -> ('a1 -> 'a1 -> bool) -> bool **)

let rec checkIfNodeIsInList a l cmp =
  match l with
  | [] -> false
  | h::tl -> (||) (eqb_node0 cmp a h) (checkIfNodeIsInList a tl cmp)

(** val closeRToTransitivity :
    'a1 node0 -> 'a1 node0 list -> 'a1 node0 list -> ('a1 -> 'a1 -> bool) -> 'a1 node0
    list **)

let rec closeRToTransitivity n ln cp_ln cmp =
  match ln with
  | [] -> []
  | h::tl ->
    (match h with
     | Node0 (_, _) -> closeRToTransitivity n tl cp_ln cmp
     | Rel (b, k, j) ->
       if Nat.eqb j (min n)
       then if negb (checkIfNodeIsInList (Rel (b, k, (max n))) cp_ln cmp)
            then (Rel (true, k, (max n)))::(closeRToTransitivity n tl cp_ln cmp)
            else closeRToTransitivity n tl cp_ln cmp
       else closeRToTransitivity n tl cp_ln cmp)

(** val removeAmbiguity0 : 'a1 node0 list -> ('a1 -> 'a1 -> bool) -> 'a1 node0 list **)

let rec removeAmbiguity0 ln cmp =
  match ln with
  | [] -> []
  | h::tl ->
    if checkIfNodeIsInList h tl cmp
    then removeAmbiguity0 tl cmp
    else h::(removeAmbiguity0 tl cmp)

(** val transitivity :
    'a1 node0 -> 'a1 node0 list -> ('a1 -> 'a1 -> bool) -> 'a1 node0 list **)

let transitivity n ln cmp =
  removeAmbiguity0 (closeRToTransitivity n ln ln cmp) cmp

(** val closeToTrans_aux :
    'a1 node0 list -> 'a1 node0 list -> ('a1 -> 'a1 -> bool) -> 'a1 node0 list **)

let rec closeToTrans_aux l cl cmp =
  match l with
  | [] -> []
  | h::tl ->
    let closeThis = transitivity h cl cmp in
    if negb (Nat.eqb (length closeThis) O)
    then app (transitivity h cl cmp) (closeToTrans_aux tl cl cmp)
    else closeToTrans_aux tl cl cmp

(** val closeToTrans : 'a1 node0 list -> ('a1 -> 'a1 -> bool) -> 'a1 node0 list **)

let closeToTrans l cmp =
  closeToTrans_aux l l cmp

(** val getOnlyR : 'a1 node0 list -> 'a1 node0 list **)

let rec getOnlyR = function
| [] -> []
| h::tl ->
  (match h with
   | Node0 (_, _) -> getOnlyR tl
   | Rel (b, k, j) -> (Rel (b, k, j))::(getOnlyR tl))

(** val getOnlyNode : 'a1 node0 list -> 'a1 node0 list **)

let rec getOnlyNode = function
| [] -> []
| h::tl ->
  (match h with
   | Node0 (sf, w) -> (Node0 (sf, w))::(getOnlyNode tl)
   | Rel (_, _, _) -> getOnlyNode tl)

(** val rnkripke_aux4 :
    'a1 list -> 'a1 node list -> nat -> ('a1 -> 'a1 -> bool) -> nat -> nat list -> 'a1
    node0 list **)

let rec rnkripke_aux4 atoms row w eqb_X default designated =
  match atoms with
  | [] -> []
  | a::tl ->
    let vA = findVal a row eqb_X default in
    (Node0 ((Sign ((isElementInList vA designated Nat.eqb), a)),
    w))::(rnkripke_aux4 tl row w eqb_X default designated)

(** val rnkripke_aux3 :
    'a1 list -> (nat, 'a1 node list) pair list -> nat -> ('a1 -> 'a1 -> bool) -> nat
    -> nat list -> 'a1 node0 list **)

let rec rnkripke_aux3 atoms matrix w eqb_X default designated =
  match matrix with
  | [] -> []
  | h::tl ->
    let index = proj_l h in
    let row = proj_r h in
    if Nat.eqb index w
    then rnkripke_aux4 atoms row w eqb_X default designated
    else rnkripke_aux3 atoms tl w eqb_X default designated

(** val avoidRepetition :
    'a1 node0 list -> 'a1 node0 list -> ('a1 -> 'a1 -> bool) -> 'a1 node0 list **)

let rec avoidRepetition add0 new0 eqb_X =
  match add0 with
  | [] -> new0
  | h::tl ->
    if isElementInList h new0 (eqb_node0 eqb_X)
    then avoidRepetition tl new0 eqb_X
    else avoidRepetition tl (h::new0) eqb_X

(** val rnkripke_aux2 :
    'a1 list -> (nat, 'a1 node list) pair list -> nat -> nat list -> ('a1 -> 'a1 ->
    bool) -> nat -> nat list -> frame list -> 'a1 node0 list -> 'a1 node0 list **)

let rec rnkripke_aux2 atoms matrix w0 l eqb_X default designated constraints model =
  match l with
  | [] ->
    if refl constraints
    then avoidRepetition ((Rel (true, w0, w0))::[]) model eqb_X
    else model
  | h::tl ->
    let atomVals = rnkripke_aux3 atoms matrix h eqb_X default designated in
    let newModel = avoidRepetition ((Rel (false, w0, h))::atomVals) model eqb_X in
    rnkripke_aux2 atoms matrix w0 tl eqb_X default designated constraints newModel

(** val rnkripke_aux1 :
    'a1 list -> (nat, 'a1 node list) pair list -> (nat, nat list) pair -> ('a1 -> 'a1
    -> bool) -> nat -> nat list -> frame list -> (nat, ('a1 node0 list, nat list)
    pair) pair **)

let rnkripke_aux1 atoms matrix v eqb_X default designated constraints =
  let index = proj_l v in
  let l = proj_r v in
  let atomVals = rnkripke_aux3 atoms matrix index eqb_X default designated in
  let initialModel =
    rnkripke_aux2 atoms matrix index l eqb_X default designated constraints []
  in
  Pair (index, (Pair ((avoidRepetition atomVals initialModel eqb_X), (index::[]))))

(** val closeToReflexivity : 'a1 node0 list -> 'a1 node0 list -> 'a1 node0 list **)

let rec closeToReflexivity l newList =
  match l with
  | [] -> newList
  | h::tl ->
    (match h with
     | Node0 (_, _) -> closeToReflexivity tl newList
     | Rel (t, a, b) ->
       if isElementInList (Rel (t, a, a)) newList eqb_node_R
       then if isElementInList (Rel (t, b, b)) newList eqb_node_R
            then closeToReflexivity tl newList
            else closeToReflexivity tl ((Rel (true, b, b))::newList)
       else if isElementInList (Rel (t, b, b)) newList eqb_node_R
            then closeToReflexivity tl ((Rel (true, a, a))::newList)
            else closeToReflexivity tl ((Rel (true, a, a))::((Rel (true, b,
                   b))::newList)))

(** val closeR_aux1 :
    nat -> 'a1 node0 list -> 'a1 node0 list -> (nat, ('a1 node0 list, nat list) pair)
    pair list -> nat list -> ('a1 -> 'a1 -> bool) -> frame list -> ('a1 node0 list,
    nat list) pair **)

let rec closeR_aux1 index l newR allV visited eqb_X constraints =
  match l with
  | [] ->
    if refl constraints
    then let closedrefl = closeToReflexivity newR newR in
         if trans constraints
         then Pair
                ((avoidRepetition (closeToTrans closedrefl eqb_X) closedrefl eqb_X),
                visited)
         else Pair (closedrefl, visited)
    else if trans constraints
         then Pair ((avoidRepetition (closeToTrans newR eqb_X) newR eqb_X), visited)
         else Pair (newR, visited)
  | h::tl ->
    (match h with
     | Node0 (_, _) -> closeR_aux1 index tl newR allV visited eqb_X constraints
     | Rel (_, _, maxH) ->
       let target =
         pop (filter (fun x -> Nat.eqb (proj_l x) maxH) allV) (Pair (O, (Pair ([],
           []))))
       in
       let target_rels = proj_l (proj_r target) in
       if isElementInList maxH visited Nat.eqb
       then closeR_aux1 index tl newR allV visited eqb_X constraints
       else closeR_aux1 index tl (avoidRepetition target_rels newR eqb_X) allV
              (maxH::visited) eqb_X constraints)

(** val closeR_aux0 :
    (nat, ('a1 node0 list, nat list) pair) pair list -> (nat, ('a1 node0 list, nat
    list) pair) pair -> ('a1 -> 'a1 -> bool) -> frame list -> (nat, ('a1 node0 list,
    nat list) pair) pair **)

let closeR_aux0 allV v eqb_X constraints =
  let index = proj_l v in
  let l = proj_l (proj_r v) in
  let visited = proj_r (proj_r v) in
  let mv = closeR_aux1 index l l allV visited eqb_X constraints in
  let new_visited = proj_r mv in
  let model = app (getOnlyR (proj_l mv)) (getOnlyNode (proj_l mv)) in
  Pair (index, (Pair (model, new_visited)))

(** val closeR :
    (nat, ('a1 node0 list, nat list) pair) pair list -> (nat, ('a1 node0 list, nat
    list) pair) pair list -> ('a1 -> 'a1 -> bool) -> frame list -> (nat, ('a1 node0
    list, nat list) pair) pair list **)

let rec closeR lc l eqb_X constraints =
  match l with
  | [] -> []
  | h::tl -> (closeR_aux0 lc h eqb_X constraints)::(closeR lc tl eqb_X constraints)

(** val rnkripke_aux0 :
    'a1 list -> (nat, 'a1 node list) pair list -> (nat, nat list) pair list -> ('a1 ->
    'a1 -> bool) -> nat -> nat list -> frame list -> (nat, ('a1 node0 list, nat list)
    pair) pair list **)

let rec rnkripke_aux0 atoms matrix l eqb_X default designated constraints =
  match l with
  | [] -> []
  | h::tl ->
    (rnkripke_aux1 atoms matrix h eqb_X default designated constraints)::(rnkripke_aux0
                                                                           atoms
                                                                           matrix tl
                                                                           eqb_X
                                                                           default
                                                                           designated
                                                                           constraints)

(** val closeR_aux00 :
    nat -> (nat, ('a1 node0 list, nat list) pair) pair list -> (nat, ('a1 node0 list,
    nat list) pair) pair list -> ('a1 -> 'a1 -> bool) -> frame list -> ((nat, ('a1
    node0 list, nat list) pair) pair -> bool) -> (nat, ('a1 node0 list, nat list)
    pair) pair list **)

let rec closeR_aux00 max0 rncp rnkripke0 eqb_X constraints select =
  match max0 with
  | O -> rnkripke0
  | S n ->
    let new0 = closeR rncp (filter select rnkripke0) eqb_X constraints in
    closeR_aux00 n rncp new0 eqb_X constraints select

(** val rearrangeModels_aux2 : 'a1 node0 list -> nat -> 'a1 list **)

let rec rearrangeModels_aux2 vals w =
  match vals with
  | [] -> []
  | h::tl ->
    (match h with
     | Node0 (sf, w') ->
       if Nat.eqb w w'
       then let Sign (b, a) = sf in
            if b then a::(rearrangeModels_aux2 tl w) else rearrangeModels_aux2 tl w
       else rearrangeModels_aux2 tl w
     | Rel (_, _, _) -> rearrangeModels_aux2 tl w)

(** val rearrangeModels_aux1 :
    'a1 node0 list -> nat list -> (nat, 'a1 list) pair list **)

let rec rearrangeModels_aux1 vals = function
| [] -> []
| h::tl -> (Pair (h, (rearrangeModels_aux2 vals h)))::(rearrangeModels_aux1 vals tl)

(** val rearrangeModels :
    (nat, ('a1 node0 list, nat list) pair) pair list -> (nat, ((nat, 'a1 list) pair
    list, 'a1 node0 list) pair) pair list **)

let rec rearrangeModels = function
| [] -> []
| h::tl ->
  let index = proj_l h in
  let worlds = proj_r (proj_r h) in
  let rels = proj_l (proj_r h) in
  (Pair (index, (Pair ((rearrangeModels_aux1 (getOnlyNode rels) worlds),
  (getOnlyR rels)))))::(rearrangeModels tl)

(** val rnkripke :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1
    -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 -> 'a1 list) -> (nat -> bool) -> (nat ->
    bool) -> (nat -> bool) -> (nat -> bool) -> nat -> nat list -> frame list -> ((nat,
    ('a1 node0 list, nat list) pair) pair -> bool) -> (nat, ('a1 node0 list, nat list)
    pair) pair list **)

let rnkripke a matrix eqb_X leb_X geb_X length_X split cmp0 cmp1 cmp2 cmp3 default designated constraints select =
  let arrange = arrangeKM a matrix eqb_X leb_X geb_X split cmp0 cmp1 cmp2 cmp3 default
  in
  let table =
    proj_r
      (computeTableWithNode a matrix eqb_X leb_X geb_X split cmp0 cmp1 cmp2 cmp3
        default)
  in
  let atoms = filter (fun x -> Nat.eqb (length_X x) O) (subf a eqb_X geb_X split) in
  let initialR = rnkripke_aux0 atoms table arrange eqb_X default designated constraints
  in
  closeR_aux00 (length initialR) initialR initialR eqb_X constraints select

(** val genTree : 'a1 -> nat list -> 'a1 btree **)

let rec genTree a = function
| [] -> Leaf true
| h::tl ->
  if Nat.eqb (length tl) O
  then Alpha ((Node (h, a)), (Leaf true))
  else Beta ((Alpha ((Node (h, a)), (Leaf true))), (genTree a tl))

(** val unary_op_aux : 'a1 -> nat -> (nat, nat list) pair list -> 'a1 btree **)

let rec unary_op_aux a vB = function
| [] -> Leaf true
| h::tl ->
  let x = proj_l h in
  let vals = proj_r h in if Nat.eqb x vB then genTree a vals else unary_op_aux a vB tl

(** val unary_op :
    'a1 -> 'a1 -> 'a1 btree -> nat -> (nat, nat list) pair list -> ('a1 -> 'a1 ->
    bool) -> 'a1 btree **)

let rec unary_op a b partialV vB table eqb_X =
  match partialV with
  | Leaf _ -> unary_op_aux a vB table
  | Alpha (n, t) ->
    let Node (i, d) = n in
    if eqb_X b d
    then Alpha (n, (unary_op a b t i table eqb_X))
    else Alpha (n, (unary_op a b t vB table eqb_X))
  | Beta (t1, t2) ->
    Beta ((unary_op a b t1 vB table eqb_X), (unary_op a b t2 vB table eqb_X))

(** val bin_op_aux :
    'a1 -> nat -> nat -> ((nat, nat) pair, nat list) pair list -> 'a1 btree **)

let rec bin_op_aux a vB vC = function
| [] -> Leaf true
| h::tl ->
  let xy = proj_l h in
  let vals = proj_r h in
  if (&&) (Nat.eqb (proj_l xy) vB) (Nat.eqb (proj_r xy) vC)
  then genTree a vals
  else bin_op_aux a vB vC tl

(** val bin_op :
    'a1 -> 'a1 -> 'a1 -> 'a1 btree -> nat -> nat -> ((nat, nat) pair, nat list) pair
    list -> ('a1 -> 'a1 -> bool) -> 'a1 btree **)

let rec bin_op a b c partialV vB vC table eqb_X =
  match partialV with
  | Leaf _ -> bin_op_aux a vB vC table
  | Alpha (n, t) ->
    let Node (i, d) = n in
    if eqb_X b d
    then if eqb_X c d
         then Alpha (n, (bin_op a b c t i i table eqb_X))
         else Alpha (n, (bin_op a b c t i vC table eqb_X))
    else if eqb_X c d
         then Alpha (n, (bin_op a b c t vB i table eqb_X))
         else Alpha (n, (bin_op a b c t vB vC table eqb_X))
  | Beta (t1, t2) ->
    Beta ((bin_op a b c t1 vB vC table eqb_X), (bin_op a b c t2 vB vC table eqb_X))

(** val reduceOnTheFly_aux2 :
    'a1 -> 'a1 node list list -> 'a1 node list -> ('a1 -> 'a1 -> bool) -> (nat ->
    bool) -> (nat -> bool) -> (nat -> bool) -> nat -> bool **)

let rec reduceOnTheFly_aux2 a allVs v eqb_X cmp1 cmp2 cmp3 default =
  match allVs with
  | [] -> false
  | h::tl ->
    let wA = findVal a h eqb_X default in
    if cmp1 wA
    then let compatible = isCompatible v h cmp2 cmp3 in
         if compatible
         then true
         else reduceOnTheFly_aux2 a tl v eqb_X cmp1 cmp2 cmp3 default
    else reduceOnTheFly_aux2 a tl v eqb_X cmp1 cmp2 cmp3 default

(** val reduceOnTheFly_aux :
    'a1 node list list -> 'a1 node list -> 'a1 node list -> ('a1 -> 'a1 -> bool) ->
    (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> nat -> bool **)

let rec reduceOnTheFly_aux allVs v vcp eqb_X cmp0 cmp1 cmp2 cmp3 default =
  match v with
  | [] -> true
  | h::tl ->
    let Node (vA, a) = h in
    if cmp0 vA
    then (&&) (reduceOnTheFly_aux2 a allVs vcp eqb_X cmp1 cmp2 cmp3 default)
           (reduceOnTheFly_aux allVs tl vcp eqb_X cmp0 cmp1 cmp2 cmp3 default)
    else reduceOnTheFly_aux allVs tl vcp eqb_X cmp0 cmp1 cmp2 cmp3 default

(** val reduceOnTheFly_aux1 :
    'a1 btree -> 'a1 node list list -> 'a1 node list -> bool -> ('a1 -> 'a1 -> bool)
    -> (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> nat -> 'a1
    btree **)

let rec reduceOnTheFly_aux1 pV allVs v b eqb_X cmp0 cmp1 cmp2 cmp3 default =
  match pV with
  | Leaf b' ->
    if (&&) b b'
    then Leaf (reduceOnTheFly_aux allVs v v eqb_X cmp0 cmp1 cmp2 cmp3 default)
    else Leaf b'
  | Alpha (n, nt) ->
    let Node (vA, _) = n in
    if cmp0 vA
    then Alpha (n,
           (reduceOnTheFly_aux1 nt allVs (n::v) true eqb_X cmp0 cmp1 cmp2 cmp3 default))
    else Alpha (n,
           (reduceOnTheFly_aux1 nt allVs (n::v) b eqb_X cmp0 cmp1 cmp2 cmp3 default))
  | Beta (nt1, nt2) ->
    Beta ((reduceOnTheFly_aux1 nt1 allVs v b eqb_X cmp0 cmp1 cmp2 cmp3 default),
      (reduceOnTheFly_aux1 nt2 allVs v b eqb_X cmp0 cmp1 cmp2 cmp3 default))

(** val reduceOnTheFly_aux0 :
    'a1 btree -> 'a1 node list list -> nat -> ('a1 -> 'a1 -> bool) -> (nat -> bool) ->
    (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> nat -> 'a1 btree **)

let reduceOnTheFly_aux0 pV allVs _ eqb_X cmp0 cmp1 cmp2 cmp3 default =
  reduceOnTheFly_aux1 pV allVs [] false eqb_X cmp0 cmp1 cmp2 cmp3 default

(** val cmp_pVs :
    'a1 node list list -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> bool **)

let rec cmp_pVs l1 l2 eqb_X =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | h1::tl1 ->
    (match l2 with
     | [] -> false
     | h2::tl2 ->
       if eqb_lX h1 h2 (eqb_node eqb_X) then cmp_pVs tl1 tl2 eqb_X else false)

(** val reduceOnTheFly_aux00 :
    'a1 btree -> 'a1 node list list -> nat -> ('a1 -> 'a1 -> bool) -> (nat -> bool) ->
    (nat -> bool) -> (nat -> bool) -> (nat -> bool) -> nat -> 'a1 btree **)

let rec reduceOnTheFly_aux00 pV allVs max0 eqb_X cmp0 cmp1 cmp2 cmp3 default =
  match max0 with
  | O -> pV
  | S n ->
    let reducedtree =
      reduceOnTheFly_aux1 pV allVs [] false eqb_X cmp0 cmp1 cmp2 cmp3 default
    in
    if cmp_pVs (parse reducedtree []) allVs eqb_X
    then reducedtree
    else reduceOnTheFly_aux00 reducedtree (parse reducedtree []) n eqb_X cmp0 cmp1
           cmp2 cmp3 default

(** val reduceOnTheFly :
    'a1 -> 'a1 -> 'a1 btree -> ('a1 -> 'a1 -> bool) -> (nat -> bool) -> (nat -> bool)
    -> (nat -> bool) -> (nat -> bool) -> nat -> 'a1 btree **)

let reduceOnTheFly a b pV eqb_X cmp0 cmp1 cmp2 cmp3 default =
  let allVs = parse pV [] in
  if eqb_X a b
  then reduceOnTheFly_aux00 pV allVs (length allVs) eqb_X cmp0 cmp1 cmp2 cmp3 default
  else reduceOnTheFly_aux0 pV allVs (S O) eqb_X cmp0 cmp1 cmp2 cmp3 default

(** val checkValInW : 'a1 -> nat -> 'a1 node0 list -> ('a1 -> 'a1 -> bool) -> bool **)

let rec checkValInW a w l cmp =
  match l with
  | [] -> false
  | h::tl ->
    (match h with
     | Node0 (sf, k) ->
       if Nat.eqb w k
       then let Sign (b, l0) = sf in if cmp a l0 then b else checkValInW a w tl cmp
       else checkValInW a w tl cmp
     | Rel (_, _, _) -> checkValInW a w tl cmp)

(** val getAllAccessedWorld : 'a1 node0 list -> nat -> nat list **)

let rec getAllAccessedWorld l w =
  match l with
  | [] -> []
  | h::tl ->
    (match h with
     | Node0 (_, _) -> getAllAccessedWorld tl w
     | Rel (_, k, j) ->
       if Nat.eqb w k then j::(getAllAccessedWorld tl w) else getAllAccessedWorld tl w)

(** val forallb : bool list -> bool **)

let rec forallb = function
| [] -> true
| h::tl -> (&&) h (forallb tl)

(** val forallnegb : bool list -> bool **)

let rec forallnegb = function
| [] -> true
| h::tl -> (&&) (negb h) (forallnegb tl)

(** val checkAllModels_aux3 :
    'a1 list -> nat -> 'a1 node0 list -> ('a1 -> 'a1 node0 list -> nat -> bool) ->
    bool list **)

let rec checkAllModels_aux3 subA root model val1 =
  match subA with
  | [] -> []
  | a::tl -> (val1 a model root)::(checkAllModels_aux3 tl root model val1)

(** val checkAllModels_aux :
    'a1 list -> (nat, ('a1 node0 list, nat list) pair) pair list -> ('a1 -> 'a1 node0
    list -> nat -> bool) -> bool list list **)

let rec checkAllModels_aux subA l val1 =
  match l with
  | [] -> []
  | h::tl ->
    let root = proj_l h in
    let model = proj_l (proj_r h) in
    (checkAllModels_aux3 subA root model val1)::(checkAllModels_aux subA tl val1)

(** val checkAllModels_aux2 :
    (nat, nat list) pair list -> bool list list -> (nat, (nat list, bool list) pair)
    pair list **)

let rec checkAllModels_aux2 matrix models_res =
  match matrix with
  | [] -> []
  | h1::tl1 ->
    (match models_res with
     | [] -> []
     | h2::tl2 ->
       let index = proj_l h1 in
       let row = proj_r h1 in
       (Pair (index, (Pair (row, h2))))::(checkAllModels_aux2 tl1 tl2))

(** val checkAllModels :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1
    -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat -> bool) -> (nat -> bool) -> (nat ->
    bool) -> (nat -> bool) -> ('a1 -> 'a1 node0 list -> nat -> bool) -> nat -> (nat,
    ('a1 node0 list, nat list) pair) pair list -> ((nat, ((nat, 'a1 list) pair list,
    'a1 node0 list) pair) pair list, ('a1 list, (nat, (nat list, bool list) pair) pair
    list) pair) pair **)

let checkAllModels a matrix eqb_X leb_X geb_X split cmp0 cmp1 cmp2 cmp3 val1 default models =
  let steps =
    restrictionSteps a matrix eqb_X leb_X geb_X split cmp0 cmp1 cmp2 cmp3 default
  in
  let table = computeTable steps in
  let matrix0 = proj_r table in
  let subA = proj_l table in
  let models_res = checkAllModels_aux subA models val1 in
  Pair ((rearrangeModels models), (Pair (subA,
  (checkAllModels_aux2 matrix0 models_res))))