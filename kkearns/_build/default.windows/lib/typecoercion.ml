open Kt4
open Kt
open Ipl
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

let rec list_lf_to_string l lf_to_string = match l with
  | [] -> ""
  | h::t -> 
    if t = [] then (lf_to_string h) else
    (lf_to_string h) ^ ", " ^ (list_lf_to_string t lf_to_string);;

let bool_to_string b = match b with
  | true -> "\\textbf{1}"
  | false -> "\\textbf{0}";;

let nat_to_string n = string_of_int (nat_to_int n);;

(***)
(* Translations between wffs *)
(***)
(*
let rec expr_to_string (e : expr_kt4) = 
  match e with
  | Atom_kt4 a -> a
  | Neg_kt4 e -> "~" ^ (expr_to_string e)
  | Box_kt4 e -> "[]" ^ (expr_to_string e)
  | Conj_kt4 (e, e') -> (expr_to_string e) ^ " \\/ " ^ (expr_to_string e')
  | Disj_kt4 (e, e') -> (expr_to_string e) ^ " /\\ " ^ (expr_to_string e')
  | Impl_kt4 (e, e') -> (expr_to_string e) ^ " -> " ^ (expr_to_string e');;
*)
(* KT4 language *)

let rec extendedLF_to_string (prop : extendedLF) = 
  match prop with
| Atom a -> list_char_to_string a
| Conj (p, q) -> "(" ^ (extendedLF_to_string p) ^ " /\\ " ^ (extendedLF_to_string q) ^ ")"
| Disj (p, q) -> "(" ^ (extendedLF_to_string p) ^ " \\/ " ^ (extendedLF_to_string q) ^ ")"
| Box p -> "[]" ^ (extendedLF_to_string p)
| Impl (p, q) -> "(" ^ (extendedLF_to_string p) ^ " -> " ^ (extendedLF_to_string q) ^ ")"
| Neg p -> "~ " ^ (extendedLF_to_string p);;

let rec extendedLF_to_tex (prop : extendedLF) = 
  match prop with
| Atom a -> "$" ^ list_char_to_string a ^ "$"
| Conj (p, q) -> "(" ^ (extendedLF_to_tex p) ^ "$\\land$" ^ (extendedLF_to_tex q) ^ ")"
| Disj (p, q) -> "(" ^ (extendedLF_to_tex p) ^ "$\\lor$" ^ (extendedLF_to_tex q) ^ ")"
| Box p -> "$\\Box$" ^ (extendedLF_to_tex p)
| Impl (p, q) -> "(" ^ (extendedLF_to_tex p) ^ "$\\to$" ^ (extendedLF_to_tex q) ^ ")"
| Neg p -> "$\\neg$" ^ (extendedLF_to_tex p);;

let rec expr_to_extendedLF (prop : expr_kt4) : extendedLF = 
  match prop with
  | Atom_kt4 a -> Atom (str_to_list_char a)
  | Neg_kt4 e -> Neg (expr_to_extendedLF e)
  | Box_kt4 e -> Box (expr_to_extendedLF e)
  | Conj_kt4 (e, e') -> Conj (expr_to_extendedLF e, expr_to_extendedLF e')
  | Disj_kt4 (e, e') -> Disj (expr_to_extendedLF e, expr_to_extendedLF e')
  | Impl_kt4 (e, e') -> Impl (expr_to_extendedLF e, expr_to_extendedLF e');;

(* KT language *)

let rec lf_to_string (prop : lF) = 
  match prop with
| Atom n -> list_char_to_string n
| Box p -> "[]" ^ (lf_to_string p)
| Impl (p, q) -> "(" ^ (lf_to_string p) ^ " -> " ^ (lf_to_string q) ^ ")"
| Neg p -> "~ " ^ (lf_to_string p);;

let rec lf_to_tex (prop : lF) = 
  match prop with
| Atom a -> "$" ^ list_char_to_string a ^ "$"
| Box p -> "$\\Box$" ^ (lf_to_tex p)
| Impl (p, q) -> "(" ^ (lf_to_tex p) ^ "$\\to$" ^ (lf_to_tex q) ^ ")"
| Neg p -> "$\\neg$" ^ (lf_to_tex p);;

let rec expr_to_lf (prop : expr_kt) : lF = 
  match prop with
  | Atom_kt a -> Atom (str_to_list_char a)
  | Neg_kt e -> Neg (expr_to_lf e)
  | Box_kt e -> Box (expr_to_lf e)
  | Impl_kt (e, e') -> Impl (expr_to_lf e, expr_to_lf e');;

(* IPL language *)

let nat_to_ipl_truth_val = function
| O -> "\\textbf{F}"
| S (S _) -> "\\textbf{T}"
| _ -> "\\textbf{U}";;

let rec ilf_to_string (prop : iLF) = 
  match prop with
| IAtom n -> list_char_to_string n
| IConj (p, q) -> "(" ^ (ilf_to_string p) ^ " /\\ " ^ (ilf_to_string q) ^ ")"
| IDisj (p, q) -> "(" ^ (ilf_to_string p) ^ " \\/ " ^ (ilf_to_string q) ^ ")"
| IImpl (p, q) -> "(" ^ (ilf_to_string p) ^ " -> " ^ (ilf_to_string q) ^ ")"
| INeg p -> "~ " ^ (ilf_to_string p);;

let rec ilf_to_tex (prop : iLF) = 
  match prop with
  | IAtom a -> "$" ^ list_char_to_string a ^ "$"
  | IConj (p, q) -> "(" ^ (ilf_to_tex p) ^ "$\\land$" ^ (ilf_to_tex q) ^ ")"
  | IDisj (p, q) -> "(" ^ (ilf_to_tex p) ^ "$\\lor$" ^ (ilf_to_tex q) ^ ")"
  | IImpl (p, q) -> "(" ^ (ilf_to_tex p) ^ "$\\to$" ^ (ilf_to_tex q) ^ ")"
  | INeg p -> "$\\neg$" ^ (ilf_to_tex p);;

let rec expr_to_ilf (prop : expr_ipl) : iLF = 
  match prop with
  | Atom_ipl a -> IAtom (str_to_list_char a)
  | Neg_ipl e -> INeg (expr_to_ilf e)
  | Impl_ipl (e, e') -> IImpl (expr_to_ilf e, expr_to_ilf e')
  | Conj_ipl (e, e') -> IConj (expr_to_ilf e, expr_to_ilf e')
  | Disj_ipl (e, e') -> IDisj (expr_to_ilf e, expr_to_ilf e');;