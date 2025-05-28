open Model

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true


(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

type lF =
| Atom of char list
| Neg of lF
| Box of lF
| Dia of lF
| Impl of lF * lF
| Conj of lF * lF
| Disj of lF * lF

(** val eqb_lf : lF -> lF -> bool **)

let rec eqb_lf a b =
  match a with
  | Atom p -> (match b with
               | Atom q -> eqb p q
               | _ -> false)
  | Neg p -> (match b with
              | Neg q -> eqb_lf p q
              | _ -> false)
  | Box p -> (match b with
              | Box q -> eqb_lf p q
              | _ -> false)
  | Dia p -> (match b with
              | Dia q -> eqb_lf p q
              | _ -> false)
  | Impl (p, q) ->
    (match b with
     | Impl (r, t) -> (&&) (eqb_lf p r) (eqb_lf q t)
     | _ -> false)
  | Conj (p, q) ->
    (match b with
     | Conj (r, t) -> (&&) (eqb_lf p r) (eqb_lf q t)
     | _ -> false)
  | Disj (p, q) ->
    (match b with
     | Disj (r, t) -> (&&) (eqb_lf p r) (eqb_lf q t)
     | _ -> false)

(** val length_lf : lF -> nat **)

let rec length_lf = function
| Atom _ -> O
| Neg p -> add (S O) (length_lf p)
| Box p -> add (S O) (length_lf p)
| Dia p -> add (S O) (length_lf p)
| Impl (p, q) -> add (add (S O) (length_lf p)) (length_lf q)
| Conj (p, q) -> add (add (S O) (length_lf p)) (length_lf q)
| Disj (p, q) -> add (add (S O) (length_lf p)) (length_lf q)

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
| Dia a -> (Dia a)::(split_lf a)
| Impl (a, b) -> (Impl (a, b))::(app (split_lf a) (split_lf b))
| Conj (a, b) -> (Conj (a, b))::(app (split_lf a) (split_lf b))
| Disj (a, b) -> (Disj (a, b))::(app (split_lf a) (split_lf b))

