
(* The type of tokens. *)

type token = 
  | RPAREN
  | NEG
  | LPAREN
  | IMPL
  | EOF
  | DISJ
  | CONJ
  | BOX
  | ATOM of (string)

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog_kt4: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr_kt4)

val prog_kt: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr_kt)

val prog_ipl: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr_ipl)
