open Model
open Language
open Relcond

(** val v0 : nat list **)

let v0 =
  vF::(vf::(vt::(vT::[])))

(** val d0 : nat list **)

let d0 =
  vt::(vT::[])

(** val neg_def : (nat, nat list) pair list **)

let neg_def =
  (Pair (vF, (vT::[])))::((Pair (vf, (vt::[])))::((Pair (vt, (vf::[])))::((Pair (vT,
    (vF::[])))::[])))

(** val box_def : (nat, nat list) pair list **)

let box_def =
  (Pair (vF, (vF::[])))::((Pair (vf, (vF::(vf::[]))))::((Pair (vt,
    (vF::(vf::[]))))::((Pair (vT, (vT::[])))::[])))

(** val dia_def : (nat, nat list) pair list **)

let dia_def =
  (Pair (vF, (vF::[])))::((Pair (vf, (vT::(vt::[]))))::((Pair (vt,
    (vT::(vt::[]))))::((Pair (vT, (vT::[])))::[])))

(** val impl_def : ((nat, nat) pair, nat list) pair list **)

let impl_def =
  (Pair ((Pair (vF, vF)), (vT::[])))::((Pair ((Pair (vF, vf)), (vT::[])))::((Pair ((Pair
    (vF, vt)), (vT::[])))::((Pair ((Pair (vF, vT)), (vT::[])))::((Pair ((Pair (vf, vF)),
    (vt::[])))::((Pair ((Pair (vf, vf)), (vT::(vt::[]))))::((Pair ((Pair (vf, vt)),
    (vT::(vt::[]))))::((Pair ((Pair (vf, vT)), (vT::[])))::((Pair ((Pair (vt, vF)),
    (vf::[])))::((Pair ((Pair (vt, vf)), (vf::[])))::((Pair ((Pair (vt, vt)),
    (vT::(vt::[]))))::((Pair ((Pair (vt, vT)), (vT::[])))::((Pair ((Pair (vT, vF)),
    (vF::[])))::((Pair ((Pair (vT, vf)), (vf::[])))::((Pair ((Pair (vT, vt)),
    (vt::[])))::((Pair ((Pair (vT, vT)), (vT::[])))::[])))))))))))))))

(** val conj_def : ((nat, nat) pair, nat list) pair list **)

let conj_def =
  (Pair ((Pair (vF, vF)), (vF::[])))::((Pair ((Pair (vF, vf)), (vF::[])))::((Pair ((Pair
    (vF, vt)), (vF::[])))::((Pair ((Pair (vF, vT)), (vF::[])))::((Pair ((Pair (vf, vF)),
    (vF::[])))::((Pair ((Pair (vf, vf)), (vF::(vf::[]))))::((Pair ((Pair (vf, vt)),
    (vF::[])))::((Pair ((Pair (vf, vT)), (vf::[])))::((Pair ((Pair (vt, vF)),
    (vF::[])))::((Pair ((Pair (vt, vf)), (vF::[])))::((Pair ((Pair (vt, vt)),
    (vt::[])))::((Pair ((Pair (vt, vT)), (vt::[])))::((Pair ((Pair (vT, vF)),
    (vF::[])))::((Pair ((Pair (vT, vf)), (vf::[])))::((Pair ((Pair (vT, vt)),
    (vt::[])))::((Pair ((Pair (vT, vT)), (vT::[])))::[])))))))))))))))

(** val disj_def : ((nat, nat) pair, nat list) pair list **)

let disj_def =
  (Pair ((Pair (vF, vF)), (vF::[])))::((Pair ((Pair (vF, vf)), (vf::[])))::((Pair ((Pair
    (vF, vt)), (vt::[])))::((Pair ((Pair (vF, vT)), (vT::[])))::((Pair ((Pair (vf, vF)),
    (vf::[])))::((Pair ((Pair (vf, vf)), (vf::[])))::((Pair ((Pair (vf, vt)),
    (vT::(vt::[]))))::((Pair ((Pair (vf, vT)), (vT::[])))::((Pair ((Pair (vt, vF)),
    (vt::[])))::((Pair ((Pair (vt, vf)), (vT::(vt::[]))))::((Pair ((Pair (vt, vt)),
    (vT::(vt::[]))))::((Pair ((Pair (vt, vT)), (vT::[])))::((Pair ((Pair (vT, vF)),
    (vT::[])))::((Pair ((Pair (vT, vf)), (vT::[])))::((Pair ((Pair (vT, vt)),
    (vT::[])))::((Pair ((Pair (vT, vT)), (vT::[])))::[])))))))))))))))

(** val nmatrix : lF -> lF -> lF btree -> nat list -> lF btree list -> lF btree **)

let nmatrix _ a partialV _ _ =
  match a with
  | Atom _ -> Leaf true
  | Neg b -> unary_op a b partialV O neg_def eqb_lf
  | Box b -> unary_op a b partialV O box_def eqb_lf
  | Dia b -> unary_op a b partialV O dia_def eqb_lf
  | Impl (b, c) -> bin_op a b c partialV O O impl_def eqb_lf
  | Conj (b, c) -> bin_op a b c partialV O O conj_def eqb_lf
  | Disj (b, c) -> bin_op a b c partialV O O disj_def eqb_lf

(** val makeMatrix : lF -> lF node list list **)

let makeMatrix a =
  makeIt a v0 nmatrix eqb_lf leb_lf length_lf split_lf

(** val makeRestrictionSteps :
    lF -> (lF list, ((nat, nat list) pair list, (nat, (lF, (nat, nat list) pair list)
    pair list) pair list) pair list) pair **)

let makeRestrictionSteps a =
  restrictionSteps a (makeMatrix a) eqb_lf leb_lf geb_lf split_lf arrowsKT4 (S (S (S (S
    (S (S (S (S O)))))))) truleKT4

(** val makeComputeTable : lF -> (lF list, (nat, nat list) pair list) pair **)

let makeComputeTable a =
  let steps = makeRestrictionSteps a in computeTable steps

(** val makeThisRn :
    nat -> lF -> bool -> bool -> (nat, (lF node0 list, nat list) pair) pair list **)

let makeThisRn _ a smallest lazymode =
  rnkripke a (makeMatrix a) eqb_lf leb_lf geb_lf length_lf split_lf arrowsKT4 (S (S (S
    (S (S (S (S (S O)))))))) d0 (Reflexive::(Transitive::[])) smallest lazymode truleKT4

(** val makeAllRn :
    lF -> bool -> bool -> (nat, (lF node0 list, nat list) pair) pair list **)

let makeAllRn a smallest lazymode =
  rnkripke a (makeMatrix a) eqb_lf leb_lf geb_lf length_lf split_lf arrowsKT4 (S (S (S
    (S (S (S (S (S O)))))))) d0 (Reflexive::(Transitive::[])) smallest lazymode truleKT4

(** val val0 : lF -> lF node0 list -> nat -> bool **)

let rec val0 a model w =
  let accW = getAllAccessedWorld model w in
  (match a with
   | Atom _ -> checkValInW a w model eqb_lf
   | Neg p -> negb (val0 p model w)
   | Box p -> forallb (map (fun k -> val0 p model k) accW)
   | Dia p -> existb (map (fun k -> val0 p model k) accW)
   | Impl (p, q) -> (||) (val0 q model w) (negb (val0 p model w))
   | Conj (p, q) -> (&&) (val0 q model w) (val0 p model w)
   | Disj (p, q) -> (||) (val0 q model w) (val0 p model w))

(** val makeCheckAllModels :
    lF -> bool -> bool -> ((nat, ((nat, lF list) pair list, lF node0 list) pair) pair
    list, (lF list, (nat, (nat list, bool list) pair) pair list) pair) pair **)

let makeCheckAllModels a smallest lazymode =
  checkAllModels a (makeMatrix a) eqb_lf leb_lf geb_lf split_lf arrowsKT4 val0 (S (S (S
    (S (S (S (S (S O)))))))) (makeAllRn a smallest lazymode) d0 truleKT4


(** val makeLevel0_aux1 : lF node list -> lF list **)

let rec makeLevel0_aux1 = function
| [] -> []
| n::tl -> let Node (_, a) = n in a::(makeLevel0_aux1 tl)

(** val makeLevel0_aux : nat -> nat list list -> (nat, nat list) pair list **)

let rec makeLevel0_aux initLabel = function
| [] -> []
| row::tl -> (Pair (initLabel, row))::(makeLevel0_aux (add initLabel (S O)) tl)

(** val makeLevel0 : lF -> (lF list, (nat, nat list) pair list) pair **)

let makeLevel0 a =
  let table = reverseThisList (makeMatrix a) in
  let subA = makeLevel0_aux1 (pop table []) in
  let level0 = nodeToNat table in Pair (subA, (makeLevel0_aux (S O) level0))