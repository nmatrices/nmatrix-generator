open Model
open Language

(** val joinRules_aux :
    nat -> (nat, (lF -> (lF, nat list) pair target) list) pair list list -> (lF -> (lF,
    nat list) pair target) list **)

let rec joinRules_aux tVal = function
| [] -> []
| frule::tl ->
  let rule = applyTo frule tVal [] Nat.eqb in app rule (joinRules_aux tVal tl)

(** val joinRules :
    (nat, (lF -> (lF, nat list) pair target) list) pair list list -> bool -> nat list ->
    ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)

let rec joinRules l auto = function
| [] -> []
| tVal::tl ->
  let rulesJoined = joinRules_aux tVal l in
  if negb (isEmpty rulesJoined)
  then (Pair ((Pair (tVal, rulesJoined)), auto))::(joinRules l auto tl)
  else joinRules l auto tl

(** val vF : nat **)

let vF =
  O

(** val vf : nat **)

let vf =
  S O

(** val vf1 : nat **)

let vf1 =
  S (S O)

(** val vf2 : nat **)

let vf2 =
  S (S (S O))

(** val vt2 : nat **)

let vt2 =
  S (S (S (S O)))

(** val vt1 : nat **)

let vt1 =
  S (S (S (S (S O))))

(** val vt : nat **)

let vt =
  S (S (S (S (S (S O)))))

(** val vT : nat **)

let vT =
  S (S (S (S (S (S (S O))))))

(** val v : nat list **)

let v =
  vF::(vf::(vf1::(vf2::(vt2::(vt1::(vt::(vT::[])))))))

(** val d : nat list **)

let d =
  vt::(vt1::(vt2::(vT::[])))

(** val f : nat list **)

let f =
  vf::(vf1::(vf2::(vF::[])))

(** val arrowsK : (nat, nat list list) pair list **)

let arrowsK =
  (Pair (vT, ((vT::[])::((vt1::[])::((vt::[])::((vt2::[])::[]))))))::((Pair (vt,
    ((vF::(vT::[]))::((vf1::(vT::[]))::((vf::(vT::[]))::((vf2::(vT::[]))::((vF::(vt1::[]))::((vf1::(vt1::[]))::((vf::(vt1::[]))::((vf2::(vt1::[]))::((vF::(vt::[]))::((vf1::(vt::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::((vF::(vt2::[]))::((vf1::(vt2::[]))::((vf::(vt2::[]))::((vf2::(vt2::[]))::[]))))))))))))))))))::((Pair
    (vt2, ((vF::[])::((vf1::[])::((vf::[])::((vf2::[])::[]))))))::((Pair (vf,
    ((vF::(vT::[]))::((vf1::(vT::[]))::((vf::(vT::[]))::((vf2::(vT::[]))::((vF::(vt1::[]))::((vf1::(vt1::[]))::((vf::(vt1::[]))::((vf2::(vt1::[]))::((vF::(vt::[]))::((vf1::(vt::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::((vF::(vt2::[]))::((vf1::(vt2::[]))::((vf::(vt2::[]))::((vf2::(vt2::[]))::[]))))))))))))))))))::((Pair
    (vf2, ((vT::[])::((vt1::[])::((vt::[])::((vt2::[])::[]))))))::((Pair (vF,
    ((vF::[])::((vf1::[])::((vf::[])::((vf2::[])::[]))))))::[])))))

(** val arrowsKB : (nat, nat list list) pair list **)

let arrowsKB =
  (Pair (vT, ((vT::[])::((vt::[])::[]))))::((Pair (vt,
    ((vf::(vT::[]))::((vf2::(vT::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::[]))))))::((Pair
    (vt2, ((vf::[])::((vf2::[])::[]))))::((Pair (vf,
    ((vF::(vt::[]))::((vf::(vt::[]))::((vF::(vt2::[]))::((vf::(vt2::[]))::[]))))))::((Pair
    (vf2, ((vt::[])::((vt2::[])::[]))))::((Pair (vF,
    ((vF::[])::((vf::[])::[]))))::[])))))

(** val arrowsK4 : (nat, nat list list) pair list **)

let arrowsK4 =
  (Pair (vT, ((vT::[])::((vt1::[])::[]))))::((Pair (vt,
    ((vF::(vT::[]))::((vf1::(vT::[]))::((vf::(vT::[]))::((vf2::(vT::[]))::((vF::(vt1::[]))::((vf1::(vt1::[]))::((vf::(vt1::[]))::((vf2::(vt1::[]))::((vF::(vt::[]))::((vf1::(vt::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::((vF::(vt2::[]))::((vf1::(vt2::[]))::((vf::(vt2::[]))::((vf2::(vt2::[]))::[]))))))))))))))))))::((Pair
    (vt2, ((vF::[])::((vf1::[])::[]))))::((Pair (vf,
    ((vF::(vT::[]))::((vf1::(vT::[]))::((vf::(vT::[]))::((vf2::(vT::[]))::((vF::(vt1::[]))::((vf1::(vt1::[]))::((vf::(vt1::[]))::((vf2::(vt1::[]))::((vF::(vt::[]))::((vf1::(vt::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::((vF::(vt2::[]))::((vf1::(vt2::[]))::((vf::(vt2::[]))::((vf2::(vt2::[]))::[]))))))))))))))))))::((Pair
    (vf2, ((vT::[])::((vt1::[])::[]))))::((Pair (vF,
    ((vF::[])::((vf1::[])::[]))))::[])))))

(** val arrowsK5 : (nat, nat list list) pair list **)

let arrowsK5 =
  (Pair (vT, ((vT::[])::((vt::[])::[]))))::((Pair (vt, ((vf::(vt::[]))::[])))::((Pair
    (vt2, ((vF::[])::((vf::[])::[]))))::((Pair (vf, ((vf::(vt::[]))::[])))::((Pair (vf2,
    ((vT::[])::((vt::[])::[]))))::((Pair (vF, ((vF::[])::((vf::[])::[]))))::[])))))

(** val arrowsK45 : (nat, nat list list) pair list **)

let arrowsK45 =
  (Pair (vT, ((vT::[])::[])))::((Pair (vt, ((vf::(vt::[]))::[])))::((Pair (vt2,
    ((vF::[])::[])))::((Pair (vf, ((vf::(vt::[]))::[])))::((Pair (vf2,
    ((vT::[])::[])))::((Pair (vF, ((vF::[])::[])))::[])))))

(** val arrowsKB45 : (nat, nat list list) pair list **)

let arrowsKB45 =
  (Pair (vT, ((vT::[])::[])))::((Pair (vt, ((vf::(vt::[]))::[])))::((Pair (vf,
    ((vf::(vt::[]))::[])))::((Pair (vF, ((vF::[])::[])))::[])))

(** val arrowsKD : (nat, nat list list) pair list **)

let arrowsKD =
  (Pair (vT, ((vT::[])::((vt::[])::((vt2::[])::[])))))::((Pair (vt,
    ((vF::(vT::[]))::((vf::(vT::[]))::((vf2::(vT::[]))::((vF::(vt::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::((vF::(vt2::[]))::((vf::(vt2::[]))::((vf2::(vt2::[]))::[])))))))))))::((Pair
    (vt2, ((vF::[])::((vf::[])::((vf2::[])::[])))))::((Pair (vf,
    ((vF::(vT::[]))::((vf::(vT::[]))::((vf2::(vT::[]))::((vF::(vt::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::((vF::(vt2::[]))::((vf::(vt2::[]))::((vf2::(vt2::[]))::[])))))))))))::((Pair
    (vf2, ((vT::[])::((vt::[])::((vt2::[])::[])))))::((Pair (vF,
    ((vF::[])::((vf::[])::((vf2::[])::[])))))::[])))))

(** val arrowsKDB : (nat, nat list list) pair list **)

let arrowsKDB =
  arrowsKB

(** val arrowsKD4 : (nat, nat list list) pair list **)

let arrowsKD4 =
  (Pair (vT, ((vT::[])::[])))::((Pair (vt,
    ((vF::(vT::[]))::((vf::(vT::[]))::((vf2::(vT::[]))::((vF::(vt::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::((vF::(vt2::[]))::((vf::(vt2::[]))::((vf2::(vt2::[]))::[])))))))))))::((Pair
    (vt2, ((vF::[])::[])))::((Pair (vf,
    ((vF::(vT::[]))::((vf::(vT::[]))::((vf2::(vT::[]))::((vF::(vt::[]))::((vf::(vt::[]))::((vf2::(vt::[]))::((vF::(vt2::[]))::((vf::(vt2::[]))::((vf2::(vt2::[]))::[])))))))))))::((Pair
    (vf2, ((vT::[])::[])))::((Pair (vF, ((vF::[])::[])))::[])))))

(** val arrowsKD5 : (nat, nat list list) pair list **)

let arrowsKD5 =
  arrowsK5

(** val arrowsKD45 : (nat, nat list list) pair list **)

let arrowsKD45 =
  arrowsK45

(** val arrowsKT : (nat, nat list list) pair list **)

let arrowsKT =
  (Pair (vt, ((vF::[])::((vf::[])::[]))))::((Pair (vf, ((vT::[])::((vt::[])::[]))))::[])

(** val arrowsKT4 : (nat, nat list list) pair list **)

let arrowsKT4 =
  arrowsKT

(** val arrowsKTB : (nat, nat list list) pair list **)

let arrowsKTB =
  (Pair (vt, ((vf::[])::[])))::((Pair (vf, ((vt::[])::[])))::[])

(** val arrowsKT45 : (nat, nat list list) pair list **)

let arrowsKT45 =
  arrowsKTB
    
    (** val n : nat list **)
    
    let n =
      vT::(vt1::(vf2::(vf1::[])))
    
    (** val i : nat list **)
    
    let i =
      vF::(vf1::(vt2::(vt1::[])))
    
    (** val pA : nat list **)
    
    let pA =
      vT::(vt::(vf2::(vf::[])))
    
    (** val pNA : nat list **)
    
    let pNA =
      vF::(vf::(vt::(vt2::[])))
    
    (** val toD : lF -> (lF, nat list) pair target **)
    
    let toD a =
      Some (Pair (a, d))
    
    (** val toND : lF -> (lF, nat list) pair target **)
    
    let toND a =
      Some (Pair (a, f))
    
    (** val posNA : lF -> (lF, nat list) pair target **)
    
    let posNA a =
      Some (Pair (a, pNA))
    
    (** val posA : lF -> (lF, nat list) pair target **)
    
    let posA a =
      Some (Pair (a, pA))
    
    (** val necN : lF -> (lF, nat list) pair target **)
    
    let necN a =
      Some (Pair (a, n))
    
    (** val necI : lF -> (lF, nat list) pair target **)
    
    let necI a =
      Some (Pair (a, i))
    
    (** val axD : (nat, (lF -> (lF, nat list) pair target) list) pair list **)
    
    let axD =
      (Pair (vT, (posA::[])))::((Pair (vt1, (posA::(posNA::[]))))::((Pair (vt2,
        (posNA::[])))::((Pair (vf1, (posA::(posNA::[]))))::((Pair (vf2, (posA::[])))::((Pair
        (vF, (posNA::[])))::[])))))
    
    (** val axT : (nat, (lF -> (lF, nat list) pair target) list) pair list **)
    
    let axT =
      (Pair (vT, (toD::[])))::((Pair (vt1, (toD::(toND::[]))))::((Pair (vt2,
        (toND::[])))::((Pair (vf1, (toND::(toD::[]))))::((Pair (vf2, (toD::[])))::((Pair
        (vF, (toND::[])))::[])))))
    
    (** val boxRule : (nat, (lF -> (lF, nat list) pair target) list) pair list **)
    
    let boxRule =
      (Pair (vT, (toD::[])))::((Pair (vt1, (toD::(toND::[]))))::((Pair (vt2,
        (toND::[])))::((Pair (vf1, (toD::(toND::[]))))::((Pair (vf2, (toD::[])))::((Pair
        (vF, (toND::[])))::[])))))
    
    (** val ax4 : (nat, (lF -> (lF, nat list) pair target) list) pair list **)
    
    let ax4 =
      (Pair (vT, (necN::[])))::((Pair (vt1, (necN::(necI::[]))))::((Pair (vt2,
        (necI::[])))::((Pair (vf1, (necN::(necI::[]))))::((Pair (vf2, (necN::[])))::((Pair
        (vF, (necI::[])))::[])))))
    
    (** val axB : (nat, (lF -> (lF, nat list) pair target) list) pair list **)
    
    let axB =
      (Pair (vT, (posA::[])))::((Pair (vt1, (posA::[])))::((Pair (vt, (posA::[])))::((Pair
        (vt2, (posA::[])))::((Pair (vf1, (posNA::[])))::((Pair (vf, (posNA::[])))::((Pair
        (vf2, (posNA::[])))::((Pair (vF, (posNA::[])))::[])))))))
    
    (** val ax5 : (nat, (lF -> (lF, nat list) pair target) list) pair list **)
    
    let ax5 =
      (Pair (vT, (posA::[])))::((Pair (vt, (posA::(posNA::[]))))::((Pair (vt2,
        (posNA::[])))::((Pair (vf, (posA::(posNA::[]))))::((Pair (vf2, (posA::[])))::((Pair
        (vF, (posNA::[])))::[])))))
    
    (** val truleK :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleK : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      joinRules (boxRule::[]) false v
    
    (** val truleKB :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKB : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      joinRules (boxRule::(axB::[])) false v
    
    (** val truleK4 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleK4 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      joinRules (boxRule::(ax4::[])) false v
    
    (** val truleK5 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleK5 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      joinRules (boxRule::(ax5::[])) false v
    
    (** val truleK45 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleK45 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::(ax4::(ax5::[]))) false v) (joinRules (axD::[]) true v)
    
    (** val truleKB45 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKB45 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      joinRules (boxRule::(axB::(ax4::(ax5::[])))) false v
    
    (** val truleKD :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKD : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::[]) false v) (joinRules (axD::[]) true v)
    
    (** val truleKDB :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKDB : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::(axB::[])) false v) (joinRules (axD::[]) true v)
    
    (** val truleKD4 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKD4 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::(ax4::[])) false v) (joinRules (axD::[]) true v)
    
    (** val truleKD5 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKD5 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::(ax5::[])) false v) (joinRules (axD::[]) true v)
    
    (** val truleKD45 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKD45 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::(ax4::(ax5::[]))) false v) (joinRules (axD::[]) true v)
    
    (** val truleKT :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKT : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::[]) false v) (joinRules (axT::[]) true v)
    
    (** val truleKTB :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKTB : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::(axB::[])) false v) (joinRules (axT::[]) true v)
    
    (** val truleKT4 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKT4 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::(ax4::[])) false v) (joinRules (axT::[]) true v)
    
    (** val truleKT45 :
        ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list **)
    
    let truleKT45 : ((nat, (lF -> (lF, nat list) pair target) list) pair, bool) pair list =
      app (joinRules (boxRule::(ax4::(ax5::[]))) false v) (joinRules (axT::[]) true v)
    
    