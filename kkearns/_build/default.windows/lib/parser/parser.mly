%{
open Ast
%}

%token <string> ATOM
%token NEG
%token BOX
%token CONJ
%token DISJ
%token IMPL
%token LPAREN
%token RPAREN
%token EOF

%left CONJ DISJ IMPL NEG
%nonassoc BOX

%start <Ast.expr_kt4> prog_kt4
%start <Ast.expr_kt> prog_kt
%start <Ast.expr_ipl> prog_ipl

%%

prog_kt:
  | e = expr_kt; EOF { e }
  ;

prog_kt4:
  | e = expr_kt4; EOF { e }
  ;

prog_ipl:
  | e = expr_ipl; EOF { e }
  ;

expr_kt4:
  | x = ATOM { Atom_kt4 x }
  | BOX; e = expr_kt4 { Box_kt4 e }
  | NEG; e = expr_kt4 { Neg_kt4 e }
  | e1 = expr_kt4; CONJ; e2 = expr_kt4 { Conj_kt4 (e1, e2) }
  | e1 = expr_kt4; DISJ; e2 = expr_kt4 { Disj_kt4 (e1, e2) }
  | e1 = expr_kt4; IMPL; e2 = expr_kt4 { Impl_kt4 (e1, e2) }
  | LPAREN; e=expr_kt4; RPAREN {e}
  ;

expr_kt:
  | x = ATOM { Atom_kt x }
  | BOX; e = expr_kt { Box_kt e }
  | NEG; e = expr_kt { Neg_kt e }
  | e1 = expr_kt; IMPL; e2 = expr_kt { Impl_kt (e1, e2) }
  | LPAREN; e=expr_kt; RPAREN {e}
  ;

expr_ipl:
  | x = ATOM { Atom_ipl x }
  | NEG; e = expr_ipl { Neg_ipl e }
  | e1 = expr_ipl; CONJ; e2 = expr_ipl { Conj_ipl (e1, e2) }
  | e1 = expr_ipl; DISJ; e2 = expr_ipl { Disj_ipl (e1, e2) }
  | e1 = expr_ipl; IMPL; e2 = expr_ipl { Impl_ipl (e1, e2) }
  | LPAREN; e=expr_ipl; RPAREN {e}
  ;