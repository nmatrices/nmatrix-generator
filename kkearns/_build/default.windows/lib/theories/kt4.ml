open Model

type extendedLF =
| Atom of char list
| Neg of extendedLF
| Box of extendedLF
| Conj of extendedLF * extendedLF
| Disj of extendedLF * extendedLF
| Impl of extendedLF * extendedLF

(** val eqb_elf : extendedLF -> extendedLF -> bool **)

let rec eqb_elf a b =
  match a with
  | Atom p -> (match b with
               | Atom q -> eqb0 p q
               | _ -> false)
  | Neg p -> (match b with
              | Neg q -> eqb_elf p q
              | _ -> false)
  | Box p -> (match b with
              | Box q -> eqb_elf p q
              | _ -> false)
  | Conj (p, q) ->
    (match b with
     | Conj (r, t) -> (&&) (eqb_elf p r) (eqb_elf q t)
     | _ -> false)
  | Disj (p, q) ->
    (match b with
     | Disj (r, t) -> (&&) (eqb_elf p r) (eqb_elf q t)
     | _ -> false)
  | Impl (p, q) ->
    (match b with
     | Impl (r, t) -> (&&) (eqb_elf p r) (eqb_elf q t)
     | _ -> false)

(** val length_elf : extendedLF -> nat **)

let rec length_elf = function
| Atom _ -> O
| Neg p -> add (S O) (length_elf p)
| Box p -> add (S O) (length_elf p)
| Conj (p, q) -> add (add (S O) (length_elf p)) (length_elf q)
| Disj (p, q) -> add (add (S O) (length_elf p)) (length_elf q)
| Impl (p, q) -> add (add (S O) (length_elf p)) (length_elf q)

(** val leb_elf : extendedLF -> extendedLF -> bool **)

let leb_elf a b =
  Nat.leb (length_elf a) (length_elf b)

(** val geb_elf : extendedLF -> extendedLF -> bool **)

let geb_elf a b =
  negb (Nat.leb (length_elf a) (length_elf b))

(** val getAllSubformulas_e : extendedLF -> extendedLF list **)

let rec getAllSubformulas_e = function
| Atom a -> (Atom a)::[]
| Neg a -> (Neg a)::(getAllSubformulas_e a)
| Box a -> (Box a)::(getAllSubformulas_e a)
| Conj (a, b) -> (Conj (a, b))::(app (getAllSubformulas_e a) (getAllSubformulas_e b))
| Disj (a, b) -> (Disj (a, b))::(app (getAllSubformulas_e a) (getAllSubformulas_e b))
| Impl (a, b) -> (Impl (a, b))::(app (getAllSubformulas_e a) (getAllSubformulas_e b))

(** val s4_neg_def : (nat, nat list) pair list **)

let s4_neg_def =
  (Pair (O, ((S O)::((S (S O))::[]))))::((Pair ((S O), (O::[])))::((Pair ((S (S O)),
    (O::[])))::[]))

(** val s4_box_def : (nat, nat list) pair list **)

let s4_box_def =
  (Pair (O, (O::[])))::((Pair ((S O), (O::[])))::((Pair ((S (S O)), ((S (S
    O))::[])))::[]))

(** val s4_impl_def : ((nat, nat) pair, nat list) pair list **)

let s4_impl_def =
  (Pair ((Pair (O, O)), ((S O)::((S (S O))::[]))))::((Pair ((Pair (O, (S O))), ((S
    O)::((S (S O))::[]))))::((Pair ((Pair (O, (S (S O)))), ((S (S O))::[])))::((Pair
    ((Pair ((S O), O)), (O::[])))::((Pair ((Pair ((S O), (S O))), ((S O)::((S (S
    O))::[]))))::((Pair ((Pair ((S O), (S (S O)))), ((S (S O))::[])))::((Pair ((Pair
    ((S (S O)), O)), (O::[])))::((Pair ((Pair ((S (S O)), (S O))), ((S
    O)::[])))::((Pair ((Pair ((S (S O)), (S (S O)))), ((S (S O))::[])))::[]))))))))

(** val s4_disj_def : ((nat, nat) pair, nat list) pair list **)

let s4_disj_def =
  (Pair ((Pair (O, O)), (O::[])))::((Pair ((Pair (O, (S O))), ((S O)::((S (S
    O))::[]))))::((Pair ((Pair (O, (S (S O)))), ((S (S O))::[])))::((Pair ((Pair ((S
    O), O)), ((S O)::((S (S O))::[]))))::((Pair ((Pair ((S O), (S O))), ((S O)::((S (S
    O))::[]))))::((Pair ((Pair ((S O), (S (S O)))), ((S (S O))::[])))::((Pair ((Pair
    ((S (S O)), O)), ((S (S O))::[])))::((Pair ((Pair ((S (S O)), (S O))), ((S (S
    O))::[])))::((Pair ((Pair ((S (S O)), (S (S O)))), ((S (S O))::[])))::[]))))))))

(** val s4_conj_def : ((nat, nat) pair, nat list) pair list **)

let s4_conj_def =
  (Pair ((Pair (O, O)), (O::[])))::((Pair ((Pair (O, (S O))), (O::[])))::((Pair ((Pair
    (O, (S (S O)))), (O::[])))::((Pair ((Pair ((S O), O)), (O::[])))::((Pair ((Pair
    ((S O), (S O))), ((S O)::[])))::((Pair ((Pair ((S O), (S (S O)))), ((S
    O)::[])))::((Pair ((Pair ((S (S O)), O)), (O::[])))::((Pair ((Pair ((S (S O)), (S
    O))), ((S O)::[])))::((Pair ((Pair ((S (S O)), (S (S O)))), ((S (S
    O))::[])))::[]))))))))

(** val s4 :
    extendedLF -> extendedLF -> extendedLF btree -> nat list -> extendedLF btree list
    -> extendedLF btree **)

let s4 _ a partialV _ _ =
  match a with
  | Atom _ -> Leaf true
  | Neg b -> unary_op a b partialV O s4_neg_def eqb_elf
  | Box b -> unary_op a b partialV O s4_box_def eqb_elf
  | Conj (b, c) -> bin_op a b c partialV O O s4_conj_def eqb_elf
  | Disj (b, c) -> bin_op a b c partialV O O s4_disj_def eqb_elf
  | Impl (b, c) -> bin_op a b c partialV O O s4_impl_def eqb_elf

(** val pruning_S4_0 : nat -> bool **)

let pruning_S4_0 a =
  Nat.eqb a (S O)

(** val pruning_S4_1 : nat -> bool **)

let pruning_S4_1 a =
  Nat.eqb a O

(** val pruning_S4_2 : nat -> bool **)

let pruning_S4_2 a =
  Nat.eqb a (S (S O))

(** val pruning_S4_3 : nat -> bool **)

let pruning_S4_3 a =
  Nat.eqb a (S (S O))

(** val s4_otf :
    extendedLF -> extendedLF -> extendedLF btree -> nat list -> extendedLF btree list
    -> extendedLF btree **)

let s4_otf a b partialV _ _ =
  match b with
  | Atom _ -> Leaf true
  | Neg c ->
    let ntree = unary_op b c partialV O s4_neg_def eqb_elf in
    reduceOnTheFly a b ntree eqb_elf pruning_S4_0 pruning_S4_1 pruning_S4_2
      pruning_S4_3 (S (S (S O)))
  | Box c ->
    let ntree = unary_op b c partialV O s4_box_def eqb_elf in
    reduceOnTheFly a b ntree eqb_elf pruning_S4_0 pruning_S4_1 pruning_S4_2
      pruning_S4_3 (S (S (S O)))
  | Conj (c, d) ->
    let ntree = bin_op b c d partialV O O s4_conj_def eqb_elf in
    reduceOnTheFly a b ntree eqb_elf pruning_S4_0 pruning_S4_1 pruning_S4_2
      pruning_S4_3 (S (S (S O)))
  | Disj (c, d) ->
    let ntree = bin_op b c d partialV O O s4_disj_def eqb_elf in
    reduceOnTheFly a b ntree eqb_elf pruning_S4_0 pruning_S4_1 pruning_S4_2
      pruning_S4_3 (S (S (S O)))
  | Impl (c, d) ->
    let ntree = bin_op b c d partialV O O s4_impl_def eqb_elf in
    reduceOnTheFly a b ntree eqb_elf pruning_S4_0 pruning_S4_1 pruning_S4_2
      pruning_S4_3 (S (S (S O)))

(** val makeMakeIt : extendedLF -> extendedLF node list list **)

let makeMakeIt a =
  makeIt a (O::((S O)::((S (S O))::[]))) s4 eqb_elf leb_elf length_elf
    getAllSubformulas_e

(** val makeMakeIt_otf : extendedLF -> extendedLF node list list **)

let makeMakeIt_otf a =
  makeIt a (O::((S O)::((S (S O))::[]))) s4_otf eqb_elf leb_elf length_elf
    getAllSubformulas_e

(** val makeRestrictionSteps :
    (extendedLF -> extendedLF node list list) -> extendedLF -> (extendedLF list,
    ((nat, nat list) pair list, (nat, (extendedLF, nat list) pair list) pair list)
    pair list) pair **)

let makeRestrictionSteps make0 a =
  restrictionSteps a (make0 a) eqb_elf leb_elf geb_elf getAllSubformulas_e
    pruning_S4_0 pruning_S4_1 pruning_S4_2 pruning_S4_3 (S (S (S O)))

(** val makeComputeTable :
    (extendedLF -> extendedLF node list list) -> extendedLF -> (extendedLF list, (nat,
    nat list) pair list) pair **)

let makeComputeTable make0 a =
  let steps = makeRestrictionSteps make0 a in computeTable steps

(** val makeAllRn :
    (extendedLF -> extendedLF node list list) -> extendedLF -> (nat, (extendedLF node0
    list, nat list) pair) pair list **)

let makeAllRn make0 a =
  rnkripke a (make0 a) eqb_elf leb_elf geb_elf length_elf getAllSubformulas_e
    pruning_S4_0 pruning_S4_1 pruning_S4_2 pruning_S4_3 (S (S (S O))) ((S O)::((S (S
    O))::[])) (Transitive::(Reflexive::[])) (fun _ -> true)

(** val makeThisRn :
    nat -> (extendedLF -> extendedLF node list list) -> extendedLF -> (nat,
    (extendedLF node0 list, nat list) pair) pair list **)

let makeThisRn w make0 a =
  rnkripke a (make0 a) eqb_elf leb_elf geb_elf length_elf getAllSubformulas_e
    pruning_S4_0 pruning_S4_1 pruning_S4_2 pruning_S4_3 (S (S (S O))) ((S O)::((S (S
    O))::[])) (Transitive::(Reflexive::[])) (fun x -> Nat.eqb (proj_l x) w)

(** val val0 : extendedLF -> extendedLF node0 list -> nat -> bool **)

let rec val0 a model w =
  let accW = getAllAccessedWorld model w in
  (match a with
   | Atom _ -> checkValInW a w model eqb_elf
   | Neg p -> negb (val0 p model w)
   | Box p -> forallb (map (fun k -> val0 p model k) accW)
   | Conj (p, q) -> (&&) (val0 p model w) (val0 q model w)
   | Disj (p, q) -> (||) (val0 p model w) (val0 q model w)
   | Impl (p, q) -> (||) (val0 q model w) (negb (val0 p model w)))

(** val makeCheckAllModels :
    (extendedLF -> extendedLF node list list) -> extendedLF -> ((nat, ((nat,
    extendedLF list) pair list, extendedLF node0 list) pair) pair list, (extendedLF
    list, (nat, (nat list, bool list) pair) pair list) pair) pair **)

let makeCheckAllModels make0 a =
  checkAllModels a (make0 a) eqb_elf leb_elf geb_elf getAllSubformulas_e pruning_S4_0
    pruning_S4_1 pruning_S4_2 pruning_S4_3 val0 (S (S (S (S O)))) (makeAllRn make0 a)