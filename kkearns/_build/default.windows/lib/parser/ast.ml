type expr_kt4 =
| Atom_kt4 of string
| Neg_kt4 of expr_kt4
| Box_kt4 of expr_kt4
| Disj_kt4 of expr_kt4 * expr_kt4
| Conj_kt4 of expr_kt4 * expr_kt4
| Impl_kt4 of expr_kt4 * expr_kt4

type expr_kt =
| Atom_kt of string
| Neg_kt of expr_kt
| Box_kt of expr_kt
| Impl_kt of expr_kt * expr_kt

type expr_ipl =
| Atom_ipl of string
| Neg_ipl of expr_ipl
| Disj_ipl of expr_ipl * expr_ipl
| Conj_ipl of expr_ipl * expr_ipl
| Impl_ipl of expr_ipl * expr_ipl
