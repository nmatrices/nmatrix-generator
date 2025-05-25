{
open Parser
}

let white = [' ' '\t']+
let letter = ['a'-'z' 'A'-'Z' '0'-'9']
let digit = ['0'-'9']
let colchete = '[' | ']'
let id = letter+

rule read =
  parse
  | white { read lexbuf }
  | "[]" { BOX }
  | "~" { NEG }
  | "/\\" { CONJ }
  | "\\/" { DISJ }
  | "->" { IMPL }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | id { ATOM (Lexing.lexeme lexbuf) }
  | eof { EOF }