open Model

type iLF =
| IAtom of char list
| INeg of iLF
| IDisj of iLF * iLF
| IConj of iLF * iLF
| IImpl of iLF * iLF

(** val eqb_ilf : iLF -> iLF -> bool **)

let rec eqb_ilf a b =
  match a with
  | IAtom p -> (match b with
                | IAtom q -> eqb0 p q
                | _ -> false)
  | INeg p -> (match b with
               | INeg q -> eqb_ilf p q
               | _ -> false)
  | IDisj (p, q) ->
    (match b with
     | IDisj (r, t) -> (&&) (eqb_ilf p r) (eqb_ilf q t)
     | _ -> false)
  | IConj (p, q) ->
    (match b with
     | IConj (r, t) -> (&&) (eqb_ilf p r) (eqb_ilf q t)
     | _ -> false)
  | IImpl (p, q) ->
    (match b with
     | IImpl (r, t) -> (&&) (eqb_ilf p r) (eqb_ilf q t)
     | _ -> false)

(** val length_ilf : iLF -> nat **)

let rec length_ilf = function
| IAtom _ -> O
| INeg p -> add (S O) (length_ilf p)
| IDisj (p, q) -> add (add (S O) (length_ilf p)) (length_ilf q)
| IConj (p, q) -> add (add (S O) (length_ilf p)) (length_ilf q)
| IImpl (p, q) -> add (add (S O) (length_ilf p)) (length_ilf q)

(** val leb_ilf : iLF -> iLF -> bool **)

let leb_ilf a b =
  Nat.leb (length_ilf a) (length_ilf b)

(** val geb_ilf : iLF -> iLF -> bool **)

let geb_ilf a b =
  negb (Nat.leb (length_ilf a) (length_ilf b))

(** val split_ilf : iLF -> iLF list **)

let rec split_ilf = function
| IAtom a -> (IAtom a)::[]
| INeg a -> (INeg a)::(split_ilf a)
| IDisj (a, b) -> (IDisj (a, b))::(app (split_ilf a) (split_ilf b))
| IConj (a, b) -> (IConj (a, b))::(app (split_ilf a) (split_ilf b))
| IImpl (a, b) -> (IImpl (a, b))::(app (split_ilf a) (split_ilf b))

(** val neg_mop : (nat, nat list) pair list **)

let neg_mop =
  (Pair (O, ((S O)::((S (S O))::[]))))::((Pair ((S O), ((S O)::((S (S
    O))::[]))))::((Pair ((S (S O)), (O::[])))::[]))

(** val impl_mop : ((nat, nat) pair, nat list) pair list **)

let impl_mop =
  (Pair ((Pair (O, O)), ((S O)::((S (S O))::[]))))::((Pair ((Pair (O, (S O))), ((S
    O)::((S (S O))::[]))))::((Pair ((Pair (O, (S (S O)))), ((S (S O))::[])))::((Pair
    ((Pair ((S O), O)), ((S O)::((S (S O))::[]))))::((Pair ((Pair ((S O), (S O))), ((S
    O)::((S (S O))::[]))))::((Pair ((Pair ((S O), (S (S O)))), ((S (S
    O))::[])))::((Pair ((Pair ((S (S O)), O)), (O::[])))::((Pair ((Pair ((S (S O)), (S
    O))), (O::[])))::((Pair ((Pair ((S (S O)), (S (S O)))), ((S (S
    O))::[])))::[]))))))))

(** val disj_mop : ((nat, nat) pair, nat list) pair list **)

let disj_mop =
  (Pair ((Pair (O, O)), (O::[])))::((Pair ((Pair (O, (S O))), (O::[])))::((Pair ((Pair
    (O, (S (S O)))), ((S (S O))::[])))::((Pair ((Pair ((S O), O)), (O::[])))::((Pair
    ((Pair ((S O), (S O))), (O::[])))::((Pair ((Pair ((S O), (S (S O)))), ((S (S
    O))::[])))::((Pair ((Pair ((S (S O)), O)), ((S (S O))::[])))::((Pair ((Pair ((S (S
    O)), (S O))), ((S (S O))::[])))::((Pair ((Pair ((S (S O)), (S (S O)))), ((S (S
    O))::[])))::[]))))))))

(** val conj_mop : ((nat, nat) pair, nat list) pair list **)

let conj_mop =
  (Pair ((Pair (O, O)), (O::[])))::((Pair ((Pair (O, (S O))), (O::[])))::((Pair ((Pair
    (O, (S (S O)))), (O::[])))::((Pair ((Pair ((S O), O)), (O::[])))::((Pair ((Pair
    ((S O), (S O))), (O::[])))::((Pair ((Pair ((S O), (S (S O)))), (O::[])))::((Pair
    ((Pair ((S (S O)), O)), (O::[])))::((Pair ((Pair ((S (S O)), (S O))),
    (O::[])))::((Pair ((Pair ((S (S O)), (S (S O)))), ((S (S O))::[])))::[]))))))))

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
  Nat.eqb a (S (S O))

(** val iPL : iLF -> iLF -> iLF btree -> nat list -> iLF btree list -> iLF btree **)

let iPL _ a partialV _ _ =
  match a with
  | IAtom _ -> Leaf true
  | INeg b -> unary_op a b partialV O neg_mop eqb_ilf
  | IDisj (b, c) -> bin_op a b c partialV O O disj_mop eqb_ilf
  | IConj (b, c) -> bin_op a b c partialV O O conj_mop eqb_ilf
  | IImpl (b, c) -> bin_op a b c partialV O O impl_mop eqb_ilf

(** val iPL_otf :
    iLF -> iLF -> iLF btree -> nat list -> iLF btree list -> iLF btree **)

let iPL_otf a b partialV _ _ =
  match b with
  | IAtom _ -> Leaf true
  | INeg c ->
    let ntree = unary_op b c partialV O neg_mop eqb_ilf in
    reduceOnTheFly a b ntree eqb_ilf pruning_0 pruning_1 pruning_2 pruning_3 (S (S (S
      O)))
  | IDisj (c, d) ->
    let ntree = bin_op b c d partialV O O disj_mop eqb_ilf in
    reduceOnTheFly a b ntree eqb_ilf pruning_0 pruning_1 pruning_2 pruning_3 (S (S (S
      O)))
  | IConj (c, d) ->
    let ntree = bin_op b c d partialV O O conj_mop eqb_ilf in
    reduceOnTheFly a b ntree eqb_ilf pruning_0 pruning_1 pruning_2 pruning_3 (S (S (S
      O)))
  | IImpl (c, d) ->
    let ntree = bin_op b c d partialV O O impl_mop eqb_ilf in
    reduceOnTheFly a b ntree eqb_ilf pruning_0 pruning_1 pruning_2 pruning_3 (S (S (S
      O)))

(** val makeMakeIt : iLF -> iLF node list list **)

let makeMakeIt a =
  makeIt a (O::((S (S O))::[])) iPL eqb_ilf leb_ilf length_ilf split_ilf

(** val makeMakeIt_otf : iLF -> iLF node list list **)

let makeMakeIt_otf a =
  makeIt a (O::((S (S O))::[])) iPL_otf eqb_ilf leb_ilf length_ilf split_ilf

(** val makeAllRn :
    (iLF -> iLF node list list) -> iLF -> (nat, (iLF node0 list, nat list) pair) pair
    list **)

let makeAllRn make0 a =
  rnkripke a (make0 a) eqb_ilf leb_ilf geb_ilf length_ilf split_ilf pruning_0
    pruning_1 pruning_2 pruning_3 (S (S (S (S O)))) ((S (S O))::[])
    (Transitive::(Reflexive::[])) (fun _ -> true)

(** val makeThisRn :
    nat -> (iLF -> iLF node list list) -> iLF -> (nat, (iLF node0 list, nat list)
    pair) pair list **)

let makeThisRn w make0 a =
  rnkripke a (make0 a) eqb_ilf leb_ilf geb_ilf length_ilf split_ilf pruning_0
    pruning_1 pruning_2 pruning_3 (S (S (S (S O)))) ((S (S O))::[])
    (Transitive::(Reflexive::[])) (fun x -> Nat.eqb (proj_l x) w)

(** val val0 : iLF -> iLF node0 list -> nat -> bool **)

let rec val0 a model w =
  let accW = getAllAccessedWorld model w in
  (match a with
   | IAtom _ -> checkValInW a w model eqb_ilf
   | INeg p -> forallnegb (map (val0 p model) accW)
   | IDisj (p, q) -> (||) (val0 p model w) (val0 q model w)
   | IConj (p, q) -> (&&) (val0 p model w) (val0 q model w)
   | IImpl (p, q) ->
     forallb (map (fun k -> if val0 p model k then val0 q model k else true) accW))

(** val makeCheckAllModels :
    (iLF -> iLF node list list) -> iLF -> ((nat, ((nat, iLF list) pair list, iLF node0
    list) pair) pair list, (iLF list, (nat, (nat list, bool list) pair) pair list)
    pair) pair **)

let makeCheckAllModels make0 a =
  checkAllModels a (make0 a) eqb_ilf leb_ilf geb_ilf split_ilf pruning_0 pruning_1
    pruning_2 pruning_3 val0 (S (S (S O))) (makeAllRn make0 a)

(** val makeRestrictionSteps :
    (iLF -> iLF node list list) -> iLF -> (iLF list, ((nat, nat list) pair list, (nat,
    (iLF, nat list) pair list) pair list) pair list) pair **)

let makeRestrictionSteps make0 a =
  restrictionSteps a (make0 a) eqb_ilf leb_ilf geb_ilf split_ilf pruning_0 pruning_1
    pruning_2 pruning_3 (S (S (S O)))

(** val makeComputeTable :
    (iLF -> iLF node list list) -> iLF -> (iLF list, (nat, nat list) pair list) pair **)

let makeComputeTable make0 a =
  let steps = makeRestrictionSteps make0 a in computeTable steps