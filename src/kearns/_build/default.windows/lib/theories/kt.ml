open Model

type lF =
| Atom of char list
| Neg of lF
| Box of lF
| Impl of lF * lF

(** val eqb_lf : lF -> lF -> bool **)

let rec eqb_lf a b =
  match a with
  | Atom p -> (match b with
               | Atom q -> eqb0 p q
               | _ -> false)
  | Neg p -> (match b with
              | Neg q -> eqb_lf p q
              | _ -> false)
  | Box p -> (match b with
              | Box q -> eqb_lf p q
              | _ -> false)
  | Impl (p, q) ->
    (match b with
     | Impl (r, t) -> (&&) (eqb_lf p r) (eqb_lf q t)
     | _ -> false)

(** val length_lf : lF -> nat **)

let rec length_lf = function
| Atom _ -> O
| Neg p -> add (S O) (length_lf p)
| Box p -> add (S O) (length_lf p)
| Impl (p, q) -> add (add (S O) (length_lf p)) (length_lf q)

(** val leb_lf : lF -> lF -> bool **)

let leb_lf a b =
  Nat.leb (length_lf a) (length_lf b)

(** val geb_lf : lF -> lF -> bool **)

let geb_lf a b =
  negb (Nat.leb (length_lf a) (length_lf b))

(** val split_lf : lF -> lF list **)

let rec split_lf = function
| Atom a -> (Atom a)::[]
| Neg a -> (Neg a)::(split_lf a)
| Box a -> (Box a)::(split_lf a)
| Impl (a, b) -> (Impl (a, b))::(app (split_lf a) (split_lf b))

(** val neg_mop : (nat, nat list) pair list **)

let neg_mop =
  (Pair (O, ((S O)::((S (S O))::[]))))::((Pair ((S O), (O::[])))::((Pair ((S (S O)),
    (O::[])))::[]))

(** val box_mop : (nat, nat list) pair list **)

let box_mop =
  (Pair (O, (O::[])))::((Pair ((S O), (O::[])))::((Pair ((S (S O)), ((S O)::((S (S
    O))::[]))))::[]))

(** val impl_mop : ((nat, nat) pair, nat list) pair list **)

let impl_mop =
  (Pair ((Pair (O, O)), ((S O)::((S (S O))::[]))))::((Pair ((Pair (O, (S O))), ((S
    O)::((S (S O))::[]))))::((Pair ((Pair (O, (S (S O)))), ((S O)::((S (S
    O))::[]))))::((Pair ((Pair ((S O), O)), (O::[])))::((Pair ((Pair ((S O), (S O))),
    ((S O)::((S (S O))::[]))))::((Pair ((Pair ((S O), (S (S O)))), ((S O)::((S (S
    O))::[]))))::((Pair ((Pair ((S (S O)), O)), (O::[])))::((Pair ((Pair ((S (S O)),
    (S O))), ((S O)::[])))::((Pair ((Pair ((S (S O)), (S (S O)))), ((S O)::((S (S
    O))::[]))))::[]))))))))

(** val pruning_0 : nat -> bool **)

let pruning_0 a =
  Nat.eqb a (S O)

(** val pruning_1 : nat -> bool **)

let pruning_1 a =
  Nat.eqb a O

(** val pruning_2 : nat -> bool **)

let pruning_2 a =
  Nat.eqb a (S (S O))

(** val pruning_3 : nat -> bool **)

let pruning_3 a =
  (||) (Nat.eqb a (S (S O))) (Nat.eqb a (S O))

(** val kT : lF -> lF -> lF btree -> nat list -> lF btree list -> lF btree **)

let kT _ a partialV _ _ =
  match a with
  | Atom _ -> Leaf true
  | Neg b -> unary_op a b partialV O neg_mop eqb_lf
  | Box b -> unary_op a b partialV O box_mop eqb_lf
  | Impl (b, c) -> bin_op a b c partialV O O impl_mop eqb_lf

(** val kT_otf : lF -> lF -> lF btree -> nat list -> lF btree list -> lF btree **)

let kT_otf a b partialV _ _ =
  match b with
  | Atom _ -> Leaf true
  | Neg c ->
    let ntree = unary_op b c partialV O neg_mop eqb_lf in
    reduceOnTheFly a b ntree eqb_lf pruning_0 pruning_1 pruning_2 pruning_3 (S (S (S
      O)))
  | Box c ->
    let ntree = unary_op b c partialV O box_mop eqb_lf in
    reduceOnTheFly a b ntree eqb_lf pruning_0 pruning_1 pruning_2 pruning_3 (S (S (S
      O)))
  | Impl (c, d) ->
    let ntree = bin_op b c d partialV O O impl_mop eqb_lf in
    reduceOnTheFly a b ntree eqb_lf pruning_0 pruning_1 pruning_2 pruning_3 (S (S (S
      O)))

(** val makeMakeIt : lF -> lF node list list **)

let makeMakeIt a =
  makeIt a (O::((S O)::((S (S O))::[]))) kT eqb_lf leb_lf length_lf split_lf

(** val makeMakeIt_otf : lF -> lF node list list **)

let makeMakeIt_otf a =
  makeIt a (O::((S O)::((S (S O))::[]))) kT_otf eqb_lf leb_lf length_lf split_lf

(** val makeRestrictionSteps :
    (lF -> lF node list list) -> lF -> (lF list, ((nat, nat list) pair list, (nat,
    (lF, nat list) pair list) pair list) pair list) pair **)

let makeRestrictionSteps make0 a =
  restrictionSteps a (make0 a) eqb_lf leb_lf geb_lf split_lf pruning_0 pruning_1
    pruning_2 pruning_3 (S (S (S O)))

(** val makeComputeTable :
    (lF -> lF node list list) -> lF -> (lF list, (nat, nat list) pair list) pair **)

let makeComputeTable make0 a =
  let steps = makeRestrictionSteps make0 a in computeTable steps

(** val makeThisRn :
    nat -> (lF -> lF node list list) -> lF -> (nat, (lF node0 list, nat list) pair)
    pair list **)

let makeThisRn w make0 a =
  rnkripke a (make0 a) eqb_lf leb_lf geb_lf length_lf split_lf pruning_0 pruning_1
    pruning_2 pruning_3 (S (S (S O))) ((S O)::((S (S O))::[])) (Reflexive::[])
    (fun x -> Nat.eqb (proj_l x) w)

(** val makeAllRn :
    (lF -> lF node list list) -> lF -> (nat, (lF node0 list, nat list) pair) pair list **)

let makeAllRn make0 a =
  rnkripke a (make0 a) eqb_lf leb_lf geb_lf length_lf split_lf pruning_0 pruning_1
    pruning_2 pruning_3 (S (S (S O))) ((S O)::((S (S O))::[])) (Reflexive::[])
    (fun _ -> true)

(** val val0 : lF -> lF node0 list -> nat -> bool **)

let rec val0 a model w =
  let accW = getAllAccessedWorld model w in
  (match a with
   | Atom _ -> checkValInW a w model eqb_lf
   | Neg p -> negb (val0 p model w)
   | Box p -> forallb (map (fun k -> val0 p model k) accW)
   | Impl (p, q) -> (||) (val0 q model w) (negb (val0 p model w)))

(** val makeCheckAllModels :
    (lF -> lF node list list) -> lF -> ((nat, ((nat, lF list) pair list, lF node0
    list) pair) pair list, (lF list, (nat, (nat list, bool list) pair) pair list)
    pair) pair **)

let makeCheckAllModels make0 a =
  checkAllModels a (make0 a) eqb_lf leb_lf geb_lf split_lf pruning_0 pruning_1
    pruning_2 pruning_3 val0 (S (S (S O))) (makeAllRn make0 a)