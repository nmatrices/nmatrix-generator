
(* The type of tokens. *)

type token = 
  | RPAREN
  | NEG
  | LPAREN
  | IMPL
  | EOF
  | DISJ
  | DIA
  | CONJ
  | BOX
  | ATOM of (string)

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr)
