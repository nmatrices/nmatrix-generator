open Language
open Ast
open Model

(* General tools *)

let rec nat_to_int (n : nat) = match n with
  | O -> 0
  | S n' -> 1 + nat_to_int n';;
  
let rec int_to_nat (n : int) = match n with
  | 0 -> O
  | _ -> S (int_to_nat (n - 1));;

let node_to_string = function
  | Node0 (_, _) -> ""
  | Rel (b, w, w') -> 
    let complement = if b then " [style=dotted]" else "" in
    (string_of_int (nat_to_int w)) ^ " -> " ^ (string_of_int (nat_to_int w')) ^ complement;;

let rec list_char_to_string l =
  match l with
  | [] -> ""
  | h::t -> (Char.escaped h) ^ (list_char_to_string t);;

let rec str_to_list_char s =
  match s with
  | "" -> []
  | _ -> (String.get s 0)::(str_to_list_char (String.sub s 1 ((String.length s) - 1)));;

  let rec list_node_to_string l drawreflexive = match l with
  | [] -> ""
  | h::t -> 
    match h with
    | Rel (_, w, w') -> 
      if (w = w') && drawreflexive then (string_of_int (nat_to_int w)) ^ "; " ^ (list_node_to_string t drawreflexive)
      else
      (node_to_string h) ^ "; " ^ (list_node_to_string t drawreflexive)
    | _ -> (list_node_to_string t drawreflexive);;

let rec list_lF_to_string l lF_to_string = match l with
  | [] -> ""
  | h::t -> 
    if t = [] then (lF_to_string h) else
    (lF_to_string h) ^ ", " ^ (list_lF_to_string t lF_to_string);;

let bool_to_string b = match b with
  | true -> "\\textbf{1}"
  | false -> "\\textbf{0}";;

let nat_to_string n = string_of_int (nat_to_int n);;

(* Modal language *)

let rec lF_to_string (prop : lF) = 
  match prop with
| Atom a -> list_char_to_string a
| Conj (p, q) -> "(" ^ (lF_to_string p) ^ " /\\ " ^ (lF_to_string q) ^ ")"
| Disj (p, q) -> "(" ^ (lF_to_string p) ^ " \\/ " ^ (lF_to_string q) ^ ")"
| Box p -> "[]" ^ (lF_to_string p)
| Dia p -> "<>" ^ (lF_to_string p)
| Impl (p, q) -> "(" ^ (lF_to_string p) ^ " -> " ^ (lF_to_string q) ^ ")"
| Neg p -> "~ " ^ (lF_to_string p);;

let rec lF_to_tex (prop : lF) = 
  match prop with
| Atom a -> "$" ^ list_char_to_string a ^ "$"
| Conj (p, q) -> "(" ^ (lF_to_tex p) ^ "$\\land$" ^ (lF_to_tex q) ^ ")"
| Disj (p, q) -> "(" ^ (lF_to_tex p) ^ "$\\lor$" ^ (lF_to_tex q) ^ ")"
| Box p -> "$\\Box$" ^ (lF_to_tex p)
| Dia p -> "$\\Diamond$" ^ (lF_to_tex p)
| Impl (p, q) -> "(" ^ (lF_to_tex p) ^ "$\\to$" ^ (lF_to_tex q) ^ ")"
| Neg p -> "$\\neg$" ^ (lF_to_tex p);;

let rec expr_to_lF (prop : expr) : lF = 
  match prop with
  | Atom a -> Atom (str_to_list_char a)
  | Neg e -> Neg (expr_to_lF e)
  | Box e -> Box (expr_to_lF e)
  | Dia e -> Dia (expr_to_lF e)
  | Conj (e, e') -> Conj (expr_to_lF e, expr_to_lF e')
  | Disj (e, e') -> Disj (expr_to_lF e, expr_to_lF e')
  | Impl (e, e') -> Impl (expr_to_lF e, expr_to_lF e');;