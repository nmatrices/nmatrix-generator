
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

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

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

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f0 = function
| [] -> []
| a::t -> (f0 a)::(map f0 t)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f0 = function
| [] -> []
| x::l0 -> if f0 x then x::(filter f0 l0) else filter f0 l0

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

let rec insert i l f0 =
  match l with
  | [] -> i::[]
  | h::t -> if f0 i h then i::(h::t) else h::(insert i t f0)

(** val sort : 'a1 list -> ('a1 -> 'a1 -> bool) -> 'a1 list **)

let rec sort l f0 =
  match l with
  | [] -> []
  | h::t -> insert h (sort t f0) f0

(** val pop : 'a1 list -> 'a1 -> 'a1 **)

let pop l default =
  match l with
  | [] -> default
  | h::_ -> h

type 'x node =
| Node of nat * 'x

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
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> 'a1 -> 'a1 list **)

let decompose eqb_AB leb_AB split l =
  sort (removeAmbiguity eqb_AB (split l)) leb_AB

(** val getAtoms :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 -> 'a1 list) ->
    'a1 -> 'a1 list **)

let getAtoms eqb_AB leb_AB length_A split a =
  filter0 (fun a0 -> leb (length_A a0) O) (decompose eqb_AB leb_AB split a)

(** val getComposed :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 -> 'a1 list) ->
    'a1 -> 'a1 list **)

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

let rec makeInitialTree_aux0 a v1 = function
| Leaf _ -> makeInitialTree_aux a v1
| Alpha (n, nt) -> Alpha (n, (makeInitialTree_aux0 a v1 nt))
| Beta (nt1, nt2) ->
  Beta ((makeInitialTree_aux0 a v1 nt1), (makeInitialTree_aux0 a v1 nt2))

(** val makeInitialTree : 'a1 list -> nat list -> 'a1 btree -> 'a1 btree **)

let rec makeInitialTree ls v1 t =
  match ls with
  | [] -> t
  | h::tl -> let ntree = makeInitialTree_aux0 h v1 t in makeInitialTree tl v1 ntree

(** val make_aux :
    'a1 -> 'a1 btree list -> 'a1 btree -> 'a1 list -> ('a1 -> 'a1 -> 'a1 btree -> nat
    list -> 'a1 btree list -> 'a1 btree) -> nat list -> 'a1 btree **)

let rec make_aux a allVal valT lcomp logic v1 =
  match lcomp with
  | [] -> valT
  | h::tl -> let ntree = logic a h valT v1 allVal in make_aux a allVal ntree tl logic v1

(** val make :
    'a1 -> 'a1 btree list -> 'a1 btree list -> 'a1 list -> ('a1 -> 'a1 -> 'a1 btree ->
    nat list -> 'a1 btree list -> 'a1 btree) -> nat list -> 'a1 btree list **)

let rec make a allVal allValcp lcomp logic v1 =
  match allVal with
  | [] -> []
  | h::tl -> (make_aux a allValcp h lcomp logic v1)::(make a tl allValcp lcomp logic v1)

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

(** val nodeToNat_aux : 'a1 node list -> nat list **)

let rec nodeToNat_aux = function
| [] -> []
| h::tl -> let Node (i, _) = h in i::(nodeToNat_aux tl)

(** val nodeToNat : 'a1 node list list -> nat list list **)

let rec nodeToNat = function
| [] -> []
| h::tl -> (nodeToNat_aux h)::(nodeToNat tl)

(** val reverseListOrder : 'a1 list -> 'a1 list **)

let rec reverseListOrder = function
| [] -> []
| h::tl -> app (reverseListOrder tl) (h::[])

(** val reverseThisList : 'a1 list list -> 'a1 list list **)

let rec reverseThisList = function
| [] -> []
| h::tl -> (reverseListOrder h)::(reverseThisList tl)

(** val makeWithoutPrune :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 -> 'a1 list) ->
    ('a1 -> 'a1 -> 'a1 btree -> nat list -> 'a1 btree list -> 'a1 btree) -> 'a1 -> 'a1
    -> nat list -> 'a1 node list list **)

let makeWithoutPrune eqb_AB leb_AB length_A split logic _ a v1 =
  let init =
    (makeInitialTree (getAtoms eqb_AB leb_AB length_A split a) v1 (Leaf true))::[]
  in
  let sub_A = getComposed eqb_AB leb_AB length_A split a in
  let forest = make a init init sub_A logic v1 in flattenList (parseVal forest)

type 'x indexed =
| I of nat * 'x

(** val getValueAtPosition : 'a1 list -> nat -> 'a1 -> 'a1 **)

let rec getValueAtPosition l p default =
  match l with
  | [] -> default
  | h::tl -> if Nat.eqb p O then h else getValueAtPosition tl (sub p (S O)) default

(** val combine : nat -> 'a1 list -> 'a1 list -> nat -> 'a1 -> 'a1 list indexed list **)

let rec combine k v1 l startValue default =
  match k with
  | O -> []
  | S n ->
    (I ((add startValue (S O)),
      (app v1 ((getValueAtPosition l startValue default)::[]))))::(combine n v1 l
                                                                    (add startValue (S
                                                                      O)) default)

(** val getIndex : 'a1 indexed -> nat **)

let getIndex = function
| I (k, _) -> k

(** val getValue : 'a1 indexed -> 'a1 **)

let getValue = function
| I (_, v1) -> v1

(** val break : 'a1 list -> nat -> 'a1 list indexed list **)

let rec break l startIndex =
  match l with
  | [] -> []
  | h::tl -> (I (startIndex, (h::[])))::(break tl (add startIndex (S O)))

(** val combinator :
    'a1 list indexed list -> 'a1 list -> 'a1 -> 'a1 list indexed list **)

let rec combinator li l default =
  match li with
  | [] -> []
  | h::tl ->
    app (combine (sub (length l) (getIndex h)) (getValue h) l (getIndex h) default)
      (combinator tl l default)

(** val select : 'a1 list indexed list -> nat -> 'a1 list indexed list **)

let rec select li size =
  match li with
  | [] -> []
  | h::tl -> if Nat.ltb (getIndex h) size then h::(select tl size) else select tl size

(** val power_r :
    'a1 list indexed list -> 'a1 list -> 'a1 -> nat -> 'a1 list indexed list **)

let rec power_r li l default = function
| O -> []
| S k ->
  let next = combinator (select li (length l)) l default in
  app next (power_r (select next (length l)) l default k)

(** val getAllValuesFromIndexedList : 'a1 list indexed list -> 'a1 list list **)

let rec getAllValuesFromIndexedList = function
| [] -> []
| h::tl -> (getValue h)::(getAllValuesFromIndexedList tl)

(** val power : 'a1 list -> 'a1 -> 'a1 list list **)

let power l default =
  let b = break l (S O) in
  getAllValuesFromIndexedList (app b (power_r b l default (length l)))

type 'x target =
| Some of 'x
| None

(** val applyTo : ('a1, 'a2) pair list -> 'a1 -> 'a2 -> ('a1 -> 'a1 -> bool) -> 'a2 **)

let rec applyTo f0 n undef cmp_x =
  match f0 with
  | [] -> undef
  | p::tl -> let Pair (x, y) = p in if cmp_x n x then y else applyTo tl n undef cmp_x

(** val fold : ('a1 -> 'a2 -> 'a2) -> 'a1 list -> 'a2 -> 'a2 **)

let rec fold f0 l b =
  match l with
  | [] -> b
  | h::tl -> f0 h (fold f0 tl b)

(** val isEmpty : 'a1 list -> bool **)

let isEmpty = function
| [] -> true
| _::_ -> false

(** val isElementInList : 'a1 -> 'a1 list -> ('a1 -> 'a1 -> bool) -> bool **)

let rec isElementInList n l cmp =
  match l with
  | [] -> false
  | h::tl -> if cmp n h then true else isElementInList n tl cmp

(** val validate_aux :
    'a1 -> ('a1 -> ('a1, nat list) pair target) list -> ('a1 -> 'a1 -> bool) -> ('a1,
    nat) pair list -> bool **)

let rec validate_aux a transf eqb_X w =
  match transf with
  | [] -> true
  | f0::tl ->
    let target0 = f0 a in
    (match target0 with
     | Some p ->
       let Pair (b, targets) = p in
       let wB = applyTo w b (S (S (S (S (S (S (S (S O)))))))) eqb_X in
       if (&&) (negb (Nat.eqb wB (S (S (S (S (S (S (S (S O))))))))))
            (negb (isElementInList wB targets Nat.eqb))
       then false
       else validate_aux a tl eqb_X w
     | None -> true)

(** val validate :
    (nat, ('a1 -> ('a1, nat list) pair target) list) pair list -> ('a1 -> 'a1 -> bool)
    -> ('a1, nat) pair list -> ('a1, nat) pair list -> bool **)

let rec validate trules eqb_X v1 w =
  match v1 with
  | [] -> true
  | p::tl ->
    let Pair (a, vA) = p in
    let transf = applyTo trules vA [] Nat.eqb in
    if negb (isEmpty transf)
    then if validate_aux a transf eqb_X w then validate trules eqb_X tl w else false
    else validate trules eqb_X tl w

type frame =
| Reflexive
| Transitive
| Symmetry

(** val eqb_frame : frame -> frame -> bool **)

let eqb_frame f1 f2 =
  match f1 with
  | Reflexive -> (match f2 with
                  | Reflexive -> true
                  | _ -> false)
  | Transitive -> (match f2 with
                   | Transitive -> true
                   | _ -> false)
  | Symmetry -> (match f2 with
                 | Symmetry -> true
                 | _ -> false)

(** val refl : frame list -> bool **)

let refl constraints =
  isElementInList Reflexive constraints eqb_frame

(** val trans : frame list -> bool **)

let trans constraints =
  isElementInList Transitive constraints eqb_frame

(** val sym : frame list -> bool **)

let sym constraints =
  isElementInList Symmetry constraints eqb_frame

(** val findVal : 'a1 -> 'a1 node list -> ('a1 -> 'a1 -> bool) -> nat -> nat **)

let rec findVal a v1 eqb_X default =
  match v1 with
  | [] -> default
  | h::tl ->
    let Node (val1, b) = h in if eqb_X a b then val1 else findVal a tl eqb_X default

(** val nodeToPair : 'a1 node list -> ('a1, nat) pair list **)

let rec nodeToPair = function
| [] -> []
| n::tl -> let Node (v1, a) = n in (Pair (a, v1))::(nodeToPair tl)

(** val restriction_aux2_v2 :
    'a1 -> (nat, 'a1 node list) pair list -> 'a1 node list -> nat -> nat -> ('a1 -> 'a1
    -> bool) -> nat -> ((nat, ('a1 -> ('a1, nat list) pair target) list) pair, bool)
    pair list -> nat list **)

let rec restriction_aux2_v2 a val1 cval root target0 eqb_X default trules =
  match val1 with
  | [] -> []
  | h::tl ->
    let trules' = map proj_l (filter (fun x -> negb (proj_r x)) trules) in
    let index = proj_l h in
    let w = nodeToPair (proj_r h) in
    let wA = applyTo w a default eqb_X in
    if Nat.eqb wA target0
    then let compatible = validate trules' eqb_X (nodeToPair cval) w in
         if compatible
         then index::(restriction_aux2_v2 a tl cval root target0 eqb_X default trules)
         else restriction_aux2_v2 a tl cval root target0 eqb_X default trules
    else restriction_aux2_v2 a tl cval root target0 eqb_X default trules

(** val restriction_aux3_v2 :
    'a1 -> (nat, 'a1 node list) pair list -> 'a1 node list -> nat -> nat list list ->
    ('a1 -> 'a1 -> bool) -> nat -> ((nat, ('a1 -> ('a1, nat list) pair target) list)
    pair, bool) pair list -> (nat, nat list) pair list list **)

let rec restriction_aux3_v2 a val1 cpcval root childs eqb_X default trules =
  match childs with
  | [] -> []
  | targets::tl ->
    let new0 =
      map (fun target0 -> Pair (target0,
        (restriction_aux2_v2 a val1 cpcval root target0 eqb_X default trules))) targets
    in
    new0::(restriction_aux3_v2 a val1 cpcval root tl eqb_X default trules)

(** val isThereAnyEmpty : (nat, nat list) pair list -> bool **)

let rec isThereAnyEmpty = function
| [] -> false
| h::tl -> if isEmpty (proj_r h) then true else isThereAnyEmpty tl

(** val restriction_aux1_v2 :
    (nat, 'a1 node list) pair list -> 'a1 node list -> 'a1 node list -> nat -> nat list
    list -> ('a1 -> 'a1 -> bool) -> nat -> ((nat, ('a1 -> ('a1, nat list) pair target)
    list) pair, bool) pair list -> ('a1, (nat, nat list) pair list) pair list **)

let rec restriction_aux1_v2 val1 cval cpcval root childs eqb_X default trules =
  match cval with
  | [] -> []
  | h::tl ->
    let Node (v1, a) = h in
    if Nat.eqb v1 root
    then let validators =
           restriction_aux3_v2 a val1 cpcval root childs eqb_X default trules
         in
         let cands =
           fold app (filter (fun cands' -> negb (isThereAnyEmpty cands')) validators) []
         in
         if isEmpty cands
         then (Pair (a,
                []))::(restriction_aux1_v2 val1 tl cpcval root childs eqb_X default
                        trules)
         else (Pair (a,
                cands))::(restriction_aux1_v2 val1 tl cpcval root childs eqb_X default
                           trules)
    else restriction_aux1_v2 val1 tl cpcval root childs eqb_X default trules

(** val restriction_aux4_v2 :
    (nat, 'a1 node list) pair list -> 'a1 node list -> (nat, nat list list) pair list ->
    ('a1 -> 'a1 -> bool) -> nat -> ((nat, ('a1 -> ('a1, nat list) pair target) list)
    pair, bool) pair list -> ('a1, (nat, nat list) pair list) pair list **)

let rec restriction_aux4_v2 val1 vals arrows eqb_X default trules =
  match arrows with
  | [] -> []
  | p::tl ->
    let Pair (root, childs) = p in
    app (restriction_aux1_v2 val1 vals vals root childs eqb_X default trules)
      (restriction_aux4_v2 val1 vals tl eqb_X default trules)

(** val checkAutoRule :
    (nat, ('a1 -> ('a1, nat list) pair target) list) pair list -> ('a1 -> 'a1 -> bool)
    -> ('a1, nat) pair list -> ('a1, nat) pair list -> ('a1, (nat, nat list) pair list)
    pair list -> ('a1, (nat, nat list) pair list) pair list **)

let rec checkAutoRule autorules eqb_X v1 cv validators =
  match v1 with
  | [] -> validators
  | p::tl ->
    let Pair (a, vA) = p in
    let transf = applyTo autorules vA [] Nat.eqb in
    if negb (isEmpty transf)
    then if validate_aux a transf eqb_X cv
         then checkAutoRule autorules eqb_X tl cv validators
         else checkAutoRule autorules eqb_X tl cv ((Pair (a, []))::validators)
    else checkAutoRule autorules eqb_X tl cv validators

(** val restriction_aux_v2 :
    (nat, 'a1 node list) pair list -> (nat, 'a1 node list) pair list -> (nat, nat list
    list) pair list -> ('a1 -> 'a1 -> bool) -> nat -> ((nat, ('a1 -> ('a1, nat list)
    pair target) list) pair, bool) pair list -> (nat, ('a1, (nat, nat list) pair list)
    pair list) pair list **)

let rec restriction_aux_v2 val1 cpval arrows eqb_X default trules =
  match val1 with
  | [] -> []
  | h::tl ->
    let autorules = map proj_l (filter proj_r trules) in
    let index = proj_l h in
    let vals = proj_r h in
    let checkAuto = checkAutoRule autorules eqb_X (nodeToPair vals) (nodeToPair vals) []
    in
    if isEmpty checkAuto
    then if validate autorules eqb_X (nodeToPair vals) (nodeToPair vals)
         then let allValidators =
                restriction_aux4_v2 cpval vals arrows eqb_X default trules
              in
              (Pair (index,
              allValidators))::(restriction_aux_v2 tl cpval arrows eqb_X default trules)
         else restriction_aux_v2 tl cpval arrows eqb_X default trules
    else (Pair (index,
           checkAuto))::(restriction_aux_v2 tl cpval arrows eqb_X default trules)

(** val removeAtIndexedList : nat -> (nat, 'a1) pair list -> (nat, 'a1) pair list **)

let rec removeAtIndexedList n = function
| [] -> []
| h::tl ->
  let index = proj_l h in if Nat.eqb index n then tl else h::(removeAtIndexedList n tl)

(** val thereSomeNil : ('a1, (nat, nat list) pair list) pair list -> bool **)

let rec thereSomeNil = function
| [] -> false
| h::tl ->
  let vals = proj_r h in if Nat.eqb (length vals) O then true else thereSomeNil tl

(** val removeNonValid :
    (nat, 'a1 node list) pair list -> (nat, ('a1, (nat, nat list) pair list) pair list)
    pair list -> (nat, 'a1 node list) pair list **)

let rec removeNonValid val1 = function
| [] -> val1
| h::tl ->
  let index = proj_l h in
  let validators = proj_r h in
  if thereSomeNil validators
  then removeNonValid (removeAtIndexedList index val1) tl
  else removeNonValid val1 tl

(** val isThereSomethingToRemove :
    (nat, ('a1, (nat, nat list) pair list) pair list) pair list -> bool **)

let rec isThereSomethingToRemove = function
| [] -> false
| h::tl ->
  let validators = proj_r h in
  if thereSomeNil validators then true else isThereSomethingToRemove tl

(** val restriction_aux0_v2 :
    (nat, 'a1 node list) pair list -> nat -> (nat, nat list list) pair list -> ('a1 ->
    'a1 -> bool) -> nat -> ((nat, ('a1 -> ('a1, nat list) pair target) list) pair, bool)
    pair list -> ((nat, 'a1 node list) pair list, (nat, ('a1, (nat, nat list) pair list)
    pair list) pair list) pair list **)

let rec restriction_aux0_v2 val1 max0 arrows eqb_X default trules =
  match max0 with
  | O -> (Pair (val1, []))::[]
  | S n ->
    let validators = restriction_aux_v2 val1 val1 arrows eqb_X default trules in
    let newMatrix = removeNonValid val1 validators in
    if isThereSomethingToRemove validators
    then (Pair (val1,
           validators))::(restriction_aux0_v2 newMatrix n arrows eqb_X default trules)
    else (Pair (val1, validators))::[]

(** val indexingList : 'a1 list -> nat -> (nat, 'a1) pair list **)

let rec indexingList l i =
  match l with
  | [] -> []
  | h::tl -> (Pair (i, h))::(indexingList tl (add i (S O)))

(** val restriction_v2 :
    'a1 node list list -> (nat, nat list list) pair list -> ('a1 -> 'a1 -> bool) -> nat
    -> ((nat, ('a1 -> ('a1, nat list) pair target) list) pair, bool) pair list -> ((nat,
    'a1 node list) pair list, (nat, ('a1, (nat, nat list) pair list) pair list) pair
    list) pair list **)

let restriction_v2 val1 arrows eqb_X =
  let indexedVals = indexingList val1 (S O) in
  restriction_aux0_v2 indexedVals (length indexedVals) arrows eqb_X

(** val makeIt :
    'a1 -> nat list -> ('a1 -> 'a1 -> 'a1 btree -> nat list -> 'a1 btree list -> 'a1
    btree) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> nat) -> ('a1 ->
    'a1 list) -> 'a1 node list list **)

let makeIt a v1 logic eqb_X leb_X length_X split =
  makeWithoutPrune eqb_X leb_X length_X split logic a a v1

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
    ((nat, 'a1 node list) pair list, (nat, ('a1, (nat, nat list) pair list) pair list)
    pair list) pair list -> ((nat, nat list) pair list, (nat, ('a1, (nat, nat list) pair
    list) pair list) pair list) pair list **)

let rec nodeToNatAll = function
| [] -> []
| h::tl ->
  let indexedVals = proj_l h in
  let validators = proj_r h in
  (Pair ((nodeToNatAll_aux indexedVals), validators))::(nodeToNatAll tl)

(** val subf :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 list) -> 'a1 list **)

let subf a eqb_X geb_X split =
  reverseListOrder (decompose eqb_X geb_X split a)

(** val restrictionSteps :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 ->
    'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat, nat list list) pair list -> nat -> ((nat,
    ('a1 -> ('a1, nat list) pair target) list) pair, bool) pair list -> ('a1 list,
    ((nat, nat list) pair list, (nat, ('a1, (nat, nat list) pair list) pair list) pair
    list) pair list) pair **)

let restrictionSteps a matrix eqb_X _ geb_X split arrows default trules =
  let res = nodeToNatAll (restriction_v2 matrix arrows eqb_X default trules) in
  let subs = subf a eqb_X geb_X split in Pair (subs, res)

(** val restrictionStepsWithNode :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 ->
    'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat, nat list list) pair list -> nat -> ((nat,
    ('a1 -> ('a1, nat list) pair target) list) pair, bool) pair list -> ('a1 list,
    ((nat, 'a1 node list) pair list, (nat, ('a1, (nat, nat list) pair list) pair list)
    pair list) pair list) pair **)

let restrictionStepsWithNode a matrix eqb_X _ geb_X split arrows default trules =
  let res = restriction_v2 matrix arrows eqb_X default trules in
  let subs = subf a eqb_X geb_X split in Pair (subs, res)

(** val getLast : 'a1 list -> 'a1 list **)

let rec getLast = function
| [] -> []
| h::tl -> if Nat.eqb (length tl) O then h::[] else getLast tl

(** val computeTable :
    ('a1 list, ((nat, nat list) pair list, (nat, ('a1, (nat, nat list) pair list) pair
    list) pair list) pair list) pair -> ('a1 list, (nat, nat list) pair list) pair **)

let computeTable steps =
  Pair ((proj_l steps), (proj_l (pop (getLast (proj_r steps)) (Pair ([], [])))))

(** val computeTableWithNode :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 ->
    'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat, nat list list) pair list -> nat -> ((nat,
    ('a1 -> ('a1, nat list) pair target) list) pair, bool) pair list -> ('a1 list, (nat,
    'a1 node list) pair list) pair **)

let computeTableWithNode a matrix eqb_X leb_X geb_X split arrows default trules =
  let steps =
    restrictionStepsWithNode a matrix eqb_X leb_X geb_X split arrows default trules
  in
  Pair ((proj_l steps), (proj_l (pop (getLast (proj_r steps)) (Pair ([], [])))))

(** val computeValidators :
    ('a1 list, ((nat, nat list) pair list, (nat, ('a1, (nat, nat list) pair list) pair
    list) pair list) pair list) pair -> (nat, ('a1, (nat, nat list) pair list) pair
    list) pair list **)

let computeValidators steps =
  proj_r (pop (getLast (proj_r steps)) (Pair ([], [])))

(** val isInList : nat -> nat list -> bool **)

let rec isInList n = function
| [] -> false
| h::tl -> if Nat.eqb n h then true else isInList n tl

(** val convergeArrows : (nat, nat list) pair list -> nat list **)

let rec convergeArrows = function
| [] -> []
| p::tl -> let Pair (_, arrows) = p in app arrows (convergeArrows tl)

(** val arrangeKM_lazymode2 : nat list -> nat list -> nat list **)

let rec arrangeKM_lazymode2 l ws =
  match l with
  | [] -> ws
  | h::tl ->
    if isInList h ws then arrangeKM_lazymode2 tl ws else arrangeKM_lazymode2 tl (h::ws)

(** val arrangeKM_lazymode1 :
    nat -> ('a1, (nat, nat list) pair list) pair list -> nat list -> nat list **)

let rec arrangeKM_lazymode1 v1 l ws =
  match l with
  | [] -> ws
  | h::tl ->
    let new0 = arrangeKM_lazymode2 (convergeArrows (proj_r h)) ws in
    arrangeKM_lazymode1 v1 tl new0

(** val eqb_list : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec eqb_list eqb1 l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | h1::tl1 ->
    (match l2 with
     | [] -> false
     | h2::tl2 -> if eqb1 h1 h2 then eqb_list eqb1 tl1 tl2 else false)

(** val injectList : nat list -> nat list list -> nat list list **)

let rec injectList l1 = function
| [] -> []
| h::tl -> (sort (removeAmbiguity Nat.eqb (app l1 h)) Nat.leb)::(injectList l1 tl)

(** val injectAllLists : nat list list -> nat list list -> nat list list **)

let rec injectAllLists l1 l2 =
  match l1 with
  | [] -> []
  | h::tl -> app (injectList h l2) (injectAllLists tl l2)

(** val arrangeKM_aux3 : nat list list list -> nat list list **)

let rec arrangeKM_aux3 = function
| [] -> []
| h::tl ->
  (match tl with
   | [] -> h
   | _::_ -> removeAmbiguity (eqb_list Nat.eqb) (injectAllLists h (arrangeKM_aux3 tl)))

(** val arrangeKM_aux2 : ('a1, nat list) pair list -> nat list list list **)

let rec arrangeKM_aux2 = function
| [] -> []
| h::tl -> (power (proj_r h) O)::(arrangeKM_aux2 tl)

(** val arrangeKM_aux4 : nat -> nat list list -> (nat, nat list) pair list **)

let rec arrangeKM_aux4 index = function
| [] -> []
| h::tl -> (Pair (index, h))::(arrangeKM_aux4 index tl)

(** val joinPreModels_aux :
    'a1 -> (nat, nat list) pair list -> ('a1, nat list) pair list **)

let rec joinPreModels_aux index = function
| [] -> []
| p::tl ->
  let Pair (_, targets) = p in (Pair (index, targets))::(joinPreModels_aux index tl)

(** val joinPreModels :
    ('a1, (nat, nat list) pair list) pair list -> ('a1, nat list) pair list **)

let rec joinPreModels = function
| [] -> []
| p::tl ->
  let Pair (index, arrows) = p in app (joinPreModels_aux index arrows) (joinPreModels tl)

(** val findBestChoice_aux : ('a1, nat list) pair list -> nat -> nat **)

let rec findBestChoice_aux valds n =
  match valds with
  | [] -> O
  | h::tl ->
    if isElementInList n (proj_r h) Nat.eqb
    then add (S O) (findBestChoice_aux tl n)
    else findBestChoice_aux tl n

(** val findBestChoice : ('a1, nat list) pair list -> nat list -> nat -> nat -> nat **)

let rec findBestChoice valds arrows h_score best_choice =
  match arrows with
  | [] -> best_choice
  | arrow::tl ->
    let score = findBestChoice_aux valds arrow in
    if Nat.leb h_score score
    then findBestChoice valds tl score arrow
    else findBestChoice valds tl h_score best_choice

(** val findSmallestModel :
    ('a1, nat list) pair list -> ('a1, nat list) pair list -> nat list **)

let rec findSmallestModel valds valdscp =
  match valds with
  | [] -> []
  | h::tl -> (findBestChoice valdscp (proj_r h) O O)::(findSmallestModel tl valdscp)

(** val arrangeKM_aux1 :
    bool -> bool -> (nat, ('a1, (nat, nat list) pair list) pair list) pair list -> (nat,
    nat list) pair list **)

let rec arrangeKM_aux1 smallest lazymode = function
| [] -> []
| h::tl ->
  let index = proj_l h in
  let valds = proj_r h in
  if lazymode
  then let accByIndex = arrangeKM_lazymode1 index valds [] in
       app ((Pair (index, accByIndex))::[]) (arrangeKM_aux1 smallest lazymode tl)
  else if Nat.eqb (length (joinPreModels valds)) O
       then app ((Pair (index, []))::[]) (arrangeKM_aux1 smallest lazymode tl)
       else let pm_joined = joinPreModels valds in
            if negb smallest
            then let accByIndex = arrangeKM_aux2 pm_joined in
                 let premodels = arrangeKM_aux3 accByIndex in
                 app (arrangeKM_aux4 index premodels)
                   (arrangeKM_aux1 smallest lazymode tl)
            else app ((Pair (index, (findSmallestModel pm_joined pm_joined)))::[])
                   (arrangeKM_aux1 smallest lazymode tl)

(** val arrangeKM :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 ->
    'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat, nat list list) pair list -> nat -> bool
    -> bool -> ((nat, ('a1 -> ('a1, nat list) pair target) list) pair, bool) pair list
    -> (nat, nat list) pair list **)

let arrangeKM a matrix eqb_X leb_X geb_X split arrows default smallest lazymode trules =
  let steps = restrictionSteps a matrix eqb_X leb_X geb_X split arrows default trules in
  let validators = computeValidators steps in arrangeKM_aux1 smallest lazymode validators

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

(** val eqb_node : ('a1 -> 'a1 -> bool) -> 'a1 node0 -> 'a1 node0 -> bool **)

let eqb_node cmp a b =
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
  | h::tl -> (||) (eqb_node cmp a h) (checkIfNodeIsInList a tl cmp)

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
            then (Rel (false, k, (max n)))::(closeRToTransitivity n tl cp_ln cmp)
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
    'a1 list -> (nat, 'a1 node list) pair list -> nat -> ('a1 -> 'a1 -> bool) -> nat ->
    nat list -> 'a1 node0 list **)

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
    if isElementInList h new0 (eqb_node eqb_X)
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
    'a1 list -> (nat, 'a1 node list) pair list -> (nat, nat list) pair -> ('a1 -> 'a1 ->
    bool) -> nat -> nat list -> frame list -> (nat, ('a1 node0 list, nat list) pair) pair **)

let rnkripke_aux1 atoms matrix v1 eqb_X default designated constraints =
  let index = proj_l v1 in
  let l = proj_r v1 in
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

(** val closeToSym_aux : 'a1 node0 list -> 'a1 node0 list -> 'a1 node0 list **)

let rec closeToSym_aux l nl =
  match l with
  | [] -> nl
  | h::tl ->
    (match h with
     | Node0 (_, _) -> closeToSym_aux tl nl
     | Rel (t, a, b) -> closeToSym_aux tl ((Rel (t, a, b))::((Rel (true, b, a))::nl)))

(** val closeToSym : 'a1 node0 list -> 'a1 node0 list **)

let closeToSym l =
  closeToSym_aux l l

(** val closeR_aux1 :
    nat -> 'a1 node0 list -> 'a1 node0 list -> (nat, ('a1 node0 list, nat list) pair)
    pair list -> nat list -> ('a1 -> 'a1 -> bool) -> frame list -> ('a1 node0 list, nat
    list) pair **)

let rec closeR_aux1 index l newR allV visited eqb_X constraints =
  match l with
  | [] ->
    if refl constraints
    then let closedrefl = closeToReflexivity newR newR in
         if trans constraints
         then let closedtrans =
                avoidRepetition (closeToTrans closedrefl eqb_X) closedrefl eqb_X
              in
              if sym constraints
              then let closedsym =
                     avoidRepetition (closeToSym closedtrans) closedtrans eqb_X
                   in
                   Pair (closedsym, visited)
              else Pair (closedtrans, visited)
         else if sym constraints
              then let closedsym =
                     avoidRepetition (closeToSym closedrefl) closedrefl eqb_X
                   in
                   Pair (closedsym, visited)
              else Pair (closedrefl, visited)
    else if trans constraints
         then let closedtrans = avoidRepetition (closeToTrans newR eqb_X) newR eqb_X in
              if sym constraints
              then let closedsym =
                     avoidRepetition (closeToSym closedtrans) closedtrans eqb_X
                   in
                   Pair (closedsym, visited)
              else Pair (closedtrans, visited)
         else if sym constraints
              then let closedsym = avoidRepetition (closeToSym newR) newR eqb_X in
                   Pair (closedsym, visited)
              else Pair (newR, visited)
  | h::tl ->
    (match h with
     | Node0 (_, _) -> closeR_aux1 index tl newR allV visited eqb_X constraints
     | Rel (_, _, maxH) ->
       let target0 =
         pop (filter (fun x -> Nat.eqb (proj_l x) maxH) allV) (Pair (O, (Pair ([], []))))
       in
       let target_rels = proj_l (proj_r target0) in
       if isElementInList maxH visited Nat.eqb
       then closeR_aux1 index tl newR allV visited eqb_X constraints
       else closeR_aux1 index tl (avoidRepetition target_rels newR eqb_X) allV
              (maxH::visited) eqb_X constraints)

(** val closeR_aux0 :
    (nat, ('a1 node0 list, nat list) pair) pair list -> (nat, ('a1 node0 list, nat list)
    pair) pair -> ('a1 -> 'a1 -> bool) -> frame list -> (nat, ('a1 node0 list, nat list)
    pair) pair **)

let closeR_aux0 allV v1 eqb_X constraints =
  let index = proj_l v1 in
  let l = proj_l (proj_r v1) in
  let visited = proj_r (proj_r v1) in
  let mv = closeR_aux1 index l l allV visited eqb_X constraints in
  let new_visited = proj_r mv in
  let model = app (getOnlyR (proj_l mv)) (getOnlyNode (proj_l mv)) in
  Pair (index, (Pair (model, new_visited)))

(** val closeR :
    (nat, ('a1 node0 list, nat list) pair) pair list -> (nat, ('a1 node0 list, nat list)
    pair) pair list -> ('a1 -> 'a1 -> bool) -> frame list -> (nat, ('a1 node0 list, nat
    list) pair) pair list **)

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
                                                                           atoms matrix
                                                                           tl eqb_X
                                                                           default
                                                                           designated
                                                                           constraints)

(** val closeR_aux00 :
    nat -> (nat, ('a1 node0 list, nat list) pair) pair list -> (nat, ('a1 node0 list,
    nat list) pair) pair list -> ('a1 -> 'a1 -> bool) -> frame list -> (nat, ('a1 node0
    list, nat list) pair) pair list **)

let rec closeR_aux00 max0 rncp rnkripke0 eqb_X constraints =
  match max0 with
  | O -> rnkripke0
  | S n ->
    let new0 = closeR rncp rnkripke0 eqb_X constraints in
    closeR_aux00 n rncp new0 eqb_X constraints

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

(** val filter_smallest :
    (nat, ('a1 node0 list, nat list) pair) pair list -> (nat, ('a1 node0 list, nat list)
    pair) pair list -> nat list -> (nat, ('a1 node0 list, nat list) pair) pair list **)

let rec filter_smallest models modelsc visited =
  match models with
  | [] -> []
  | model::tl ->
    let index = proj_l model in
    if negb (isElementInList index visited Nat.eqb)
    then let select0 = filter (fun m -> Nat.eqb (proj_l m) index) modelsc in
         let m_sorted =
           sort select0 (fun m1 m2 ->
             Nat.leb (length (proj_r (proj_r m1))) (length (proj_r (proj_r m2))))
         in
         let smallest =
           filter (fun m ->
             Nat.eqb (length (proj_r (proj_r m)))
               (length (proj_r (proj_r (pop m_sorted (Pair (O, (Pair ([], [])))))))))
             m_sorted
         in
         app smallest (filter_smallest tl modelsc (index::visited))
    else filter_smallest tl modelsc visited

(** val rnkripke :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 ->
    'a1 -> bool) -> ('a1 -> nat) -> ('a1 -> 'a1 list) -> (nat, nat list list) pair list
    -> nat -> nat list -> frame list -> bool -> bool -> ((nat, ('a1 -> ('a1, nat list)
    pair target) list) pair, bool) pair list -> (nat, ('a1 node0 list, nat list) pair)
    pair list **)

let rnkripke a matrix eqb_X leb_X geb_X length_X split arrows default designated constraints smallest lazymode trules =
  let arrange =
    arrangeKM a matrix eqb_X leb_X geb_X split arrows default smallest lazymode trules
  in
  let table =
    proj_r (computeTableWithNode a matrix eqb_X leb_X geb_X split arrows default trules)
  in
  let atoms = filter (fun x -> Nat.eqb (length_X x) O) (subf a eqb_X geb_X split) in
  let initialR = rnkripke_aux0 atoms table arrange eqb_X default designated constraints
  in
  let relations = closeR_aux00 (length initialR) initialR initialR eqb_X constraints in
  if smallest then filter_smallest relations relations [] else relations

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
    'a1 -> 'a1 -> 'a1 btree -> nat -> (nat, nat list) pair list -> ('a1 -> 'a1 -> bool)
    -> 'a1 btree **)

let rec unary_op a b partialV vB table eqb_X =
  match partialV with
  | Leaf _ -> unary_op_aux a vB table
  | Alpha (n, t) ->
    let Node (v1, d1) = n in
    if eqb_X b d1
    then Alpha (n, (unary_op a b t v1 table eqb_X))
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
    let Node (v1, d1) = n in
    if eqb_X b d1
    then if eqb_X c d1
         then Alpha (n, (bin_op a b c t v1 v1 table eqb_X))
         else Alpha (n, (bin_op a b c t v1 vC table eqb_X))
    else if eqb_X c d1
         then Alpha (n, (bin_op a b c t vB v1 table eqb_X))
         else Alpha (n, (bin_op a b c t vB vC table eqb_X))
  | Beta (t1, t2) ->
    Beta ((bin_op a b c t1 vB vC table eqb_X), (bin_op a b c t2 vB vC table eqb_X))

(** val findRowByIndex : (nat, 'a1 list) pair list -> nat -> 'a1 list **)

let rec findRowByIndex matrix index =
  match matrix with
  | [] -> []
  | h::tl -> if Nat.eqb index (proj_l h) then proj_r h else findRowByIndex tl index

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

(** val existb : bool list -> bool **)

let rec existb = function
| [] -> false
| h::tl -> (||) h (existb tl)

(** val checkAllModels_aux3 :
    'a1 list -> nat -> 'a1 node0 list -> ('a1 -> 'a1 node0 list -> nat -> bool) -> nat
    list -> nat list -> bool list **)

let rec checkAllModels_aux3 subA root model val1 valuation d1 =
  match subA with
  | [] -> []
  | a::tl1 ->
    (match valuation with
     | [] -> []
     | vA::tl2 ->
       let vA0 = val1 a model root in
       if (&&) (isElementInList vA d1 Nat.eqb) vA0
       then true::(checkAllModels_aux3 tl1 root model val1 tl2 d1)
       else ((&&) (negb (isElementInList vA d1 Nat.eqb)) (negb vA0))::(checkAllModels_aux3
                                                                        tl1 root model
                                                                        val1 tl2 d1))

(** val checkAllModels_aux :
    (nat, nat list) pair list -> 'a1 list -> (nat, ('a1 node0 list, nat list) pair) pair
    list -> ('a1 -> 'a1 node0 list -> nat -> bool) -> nat list -> (nat, bool list) pair
    list **)

let rec checkAllModels_aux matrix subA l val1 d1 =
  match l with
  | [] -> []
  | h::tl ->
    let root = proj_l h in
    let model = proj_l (proj_r h) in
    let valuation = findRowByIndex matrix root in
    (Pair (root,
    (checkAllModels_aux3 subA root model val1 valuation d1)))::(checkAllModels_aux
                                                                 matrix subA tl val1 d1)

(** val checkAllModels_aux2 :
    (nat, nat list) pair list -> (nat, bool list) pair list -> (nat, (nat list, bool
    list) pair) pair list **)

let rec checkAllModels_aux2 matrix = function
| [] -> []
| h2::tl2 ->
  let index = proj_l h2 in
  let row = findRowByIndex matrix index in
  (Pair (index, (Pair (row, (proj_r h2)))))::(checkAllModels_aux2 matrix tl2)

(** val checkAllModels :
    'a1 -> 'a1 node list list -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> ('a1 ->
    'a1 -> bool) -> ('a1 -> 'a1 list) -> (nat, nat list list) pair list -> ('a1 -> 'a1
    node0 list -> nat -> bool) -> nat -> (nat, ('a1 node0 list, nat list) pair) pair
    list -> nat list -> ((nat, ('a1 -> ('a1, nat list) pair target) list) pair, bool)
    pair list -> ((nat, ((nat, 'a1 list) pair list, 'a1 node0 list) pair) pair list,
    ('a1 list, (nat, (nat list, bool list) pair) pair list) pair) pair **)

let checkAllModels a m eqb_X leb_X geb_X split arrows val1 default models d1 trules =
  let steps = restrictionSteps a m eqb_X leb_X geb_X split arrows default trules in
  let table = computeTable steps in
  let matrix = proj_r table in
  let subA = proj_l table in
  let models_res = checkAllModels_aux matrix subA models val1 d1 in
  Pair ((rearrangeModels models), (Pair (subA, (checkAllModels_aux2 matrix models_res))))