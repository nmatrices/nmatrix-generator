%{
open Ast
%}

%token <string> ATOM
%token NEG
%token BOX
%token DIA
%token CONJ
%token DISJ
%token IMPL
%token LPAREN
%token RPAREN
%token EOF

%left CONJ DISJ IMPL NEG
%nonassoc BOX DIA

%start <Ast.expr> prog

%%

prog:
  | e = expr; EOF { e }
  ;

expr:
  | x = ATOM { Atom x }
  | BOX; e = expr { Box e }
  | DIA; e = expr { Dia e }
  | NEG; e = expr { Neg e }
  | e1 = expr; CONJ; e2 = expr { Conj (e1, e2) }
  | e1 = expr; DISJ; e2 = expr { Disj (e1, e2) }
  | e1 = expr; IMPL; e2 = expr { Impl (e1, e2) }
  | LPAREN; e=expr; RPAREN {e}
  ;