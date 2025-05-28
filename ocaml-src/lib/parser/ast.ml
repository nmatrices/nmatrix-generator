type expr =
| Atom of string
| Neg of expr
| Box of expr
| Dia of expr
| Disj of expr * expr
| Conj of expr * expr
| Impl of expr * expr