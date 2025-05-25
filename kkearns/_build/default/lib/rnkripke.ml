(*open Model
open Kt4
open Kt
open Ipl
open Negecp*)
open Model
open Typecoercion

let time f x =
  let t = Unix.gettimeofday () in
  let fx = f x in
  Printf.printf "> Elapsed time: %fs\n" (Unix.gettimeofday () -. t);
  fx;;

let parse s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast;;

let makeLabel p l lf_to_string =
  let w = string_of_int (nat_to_int p) in
  if l = [] then " " else
    w ^ " [label=< " ^ w ^ ":<B>" ^ (list_lF_to_string l lf_to_string) ^ "</B> >];\n";;

let rec makeLabels l lf_to_string = match l with
  | [] -> ""
  | h::t -> (makeLabel (proj_l h) (proj_r h) lf_to_string) ^ (makeLabels t lf_to_string);;

let rec output_to_graphiz l lf_to_string drawreflexive = 
  match l with
  | [] -> []
  | h::t -> 
    (Pair (nat_to_int (proj_l h), ((makeLabels (proj_l (proj_r h)) lf_to_string)^(list_node_to_string (proj_r (proj_r h)) drawreflexive))))
      ::(output_to_graphiz t lf_to_string drawreflexive);;

let rec save_each_to_file l layout (count : int) = match l with
  | [] -> ()
  | h::t ->
    Printf.printf "Make model with root in (%d). File models/model%d.svg.\n" (proj_l h) (proj_l h);
    let graphvizcmd = 
      "echo \"digraph { graph [root="^(string_of_int ((proj_l h)))^", label=\\\"Root in world ("^string_of_int(proj_l h)^
      ")\\\"]; edge [arrowhead=vee]; node [color=darkred fillcolor=ghostwhite style=filled shape=box3d]; "
      ^ (string_of_int ((proj_l h))) ^ "[color=darkgreen]"
      ^ " outputorder=edgesfirst; layout=circo;  "
      ^layout^ " "
      ^ (proj_r h) ^ " }\" | dot -Tsvg > models/model" 
      ^ (string_of_int (proj_l h)) ^ "[fileId=" ^ (string_of_int count) ^"].svg" in
    (*let _ = Printf.printf "\nGraphviz command: %s\n\n" graphvizcmd in*)
    let _ = 
      Sys.command graphvizcmd
    in
    save_each_to_file t layout (count + 1);;

(*
(**** CLI *****)
*)

(*type propo =
| KT_l of Kt.lF
| KT45_l of Kt45.lF
| KT4_l of extendedLF
| IPL_l of iLF
| NEGECP_l of eLF*)

type logic =
| KT45
| KT4
| KTB
| KT
| KD
| KDB
| KD4
| KD5
| KD45

let string_to_logic = function
  | ("KT45" | "S5" | "KTB45" | "KT5" | "T5") -> KT45
  | ("KT4" | "S4" | "T4" ) -> KT4
  | ("KTB" | "TB") -> KTB
  | ("KT" | "T") -> KT
  | ("KD" | "D") -> KD
  | ("KDB" | "DB") -> KDB
  | ("KD4" | "D4") -> KD4
  | ("KD5" | "D5") -> KD5
  | ("KD45" | "D45") -> KD45
  | _ -> invalid_arg "Invalid logic"

let rec list_wff_to_list_md l wff_to_string counter = match l with
  | [] -> ""
  | h::t -> 
    "* " ^ "($\\varphi_{"^(string_of_int counter)^"}$) " 
    ^ (wff_to_string h) ^ "\n" 
    ^ (list_wff_to_list_md t wff_to_string (counter+1))

let rec list_wff_to_list_string l counter = match l with
  | [] -> "|"
  | _::t -> "| " ^ "$\\varphi_{"^(string_of_int counter)^"}$ "  ^ " " ^ (list_wff_to_list_string t (counter+1))

let rec make_header (size : int) = match size with
  | 0 -> "|"
  | n -> "| :-: " ^ (make_header (n-1)) 

let rec list_nat_to_string l to_string = match l with
  | [] -> " |\n"
  | h::t -> " | " ^ (to_string h)  ^ (list_nat_to_string t to_string);;

let rec print_rnmatrix l to_string =
  match l with
  | [] -> ""
  | h::t -> 
    let row = ("| (\\emph{" ^ (string_of_int (nat_to_int (proj_l h))) ^ "})" ^ (list_nat_to_string (proj_l (proj_r h)) to_string)) in
    row ^ print_rnmatrix t to_string;;

let rec print_truthtable l to_string =
  match l with
  | [] -> ""
  | h::t -> 
    let row = ("| (\\emph{" ^ (string_of_int (nat_to_int (proj_l h))) ^ "})" ^ (list_nat_to_string (proj_r h) to_string)) in
    row ^ print_truthtable t to_string;;

let rec list_bool_to_string l = match l with
  | [] -> " |\n"
  | h::t -> " | " ^ (bool_to_string h)  ^ (list_bool_to_string t);;

let rec print_semantic_matrix l =
  match l with
  | [] -> ""
  | h::t -> 
    let row = ("| (\\emph{" ^ (string_of_int (nat_to_int (proj_l h))) ^ "})" ^ (list_bool_to_string (proj_r (proj_r h)))) in
    row ^ print_semantic_matrix t;;

(* 

= ([! "p0"; [] ! "p0"; [] ([] ! "p0"); [] ! "p0" ~> [] ([] ! "p0")];
       [(2; ([0; 0; 0; 2]; [false; false; false; true]));
        (4; ([1; 0; 0; 2]; [true; false; false; true]));
        (5; ([2; 2; 2; 2]; [true; true; true; true]))])
     : pair (list extendedLF) (list (pair nat (pair (list nat) (list bool))))

*)

let print_string_to_file s = 
  let oc = open_out "matrices/matrices.md" in
  Printf.fprintf oc "%s" s;
  Printf.printf "\n\nMatrices saved in matrices/matrices.md\n";
  let _ = close_out oc in
  Sys.command ("((pandoc -f markdown -t latex --standalone matrices/matrices.md > matrices/matrices.tex " 
  ^ "&& pdflatex -interaction=\"batchmode\" -output-directory=\"matrices/\" matrices/matrices.tex > /dev/null 2>&1)" 
  ^ " && xdg-open matrices/matrices.pdf &)");;
  (*Sys.command ("(pandoc -f markdown -t latex --standalone matrices\\matrices.md > matrices\\matrices.tex && pdflatex -interaction=batchmode -output-directory=matrices\ matrices\\matrices.tex > NUL 2>&1) && start matrices\\matrices.pdf");;*)

let modelCli logic prop layout drawreflexive onlytable w lazy_mode smallest level0 = 
let l = string_to_logic logic in
let des = match l with
  | (KT45 | KT4 | KTB | KT) -> "{6, 7}" 
  | (KD | KDB | KD4 | KD5 | KD45) -> "{4,6,7}" 
in
let title = 
  if level0 then
    "\n# Nmatrix (level 0) in "
  else  
    "\n# Restricted Nmatrix in "
in
let header = "---\ndocumentclass: extarticle\nfontsize: 14pt\n---\n\n" in
let truthtable rnmatrix wfs wf_to_tex nat_to_string = 
  header^title^logic^"\n\n" 
  ^ "* $\\mathcal{D}$ = "^des^"\n\n"
  ^ "## Subformulas\n\n"
  ^ (list_wff_to_list_md (proj_l rnmatrix) wf_to_tex 0) ^ "\n"
  ^"| Id "^wfs^"\n"^(make_header ((List.length (proj_l rnmatrix)+1))) ^"\n" 
  ^ (print_truthtable (proj_r rnmatrix) nat_to_string) in
let matrices_str rnmatrix wfs wf_to_tex nat_to_string = 
  header^"\n# Matrices in "^logic^"\n\n" 
  ^ "## Subformulas\n\n"
  ^ (list_wff_to_list_md (proj_l rnmatrix) wf_to_tex 0) ^ "\n"
  ^ "## Restricted Nmatrix\n\n* $\\mathcal{D}$ = "^des^"\n\n"
  ^"| Id "^wfs^"\n"^(make_header ((List.length (proj_l rnmatrix)+1))) ^"\n" 
  ^ (print_rnmatrix (proj_r rnmatrix) nat_to_string) ^ "\n\\pagebreak\n## Model checking \n"
  ^ "\n| World "^wfs^"\n"^(make_header ((List.length (proj_l rnmatrix)+1)))^"\n" 
  ^ (print_semantic_matrix (proj_r rnmatrix)) in
let genFile table rnk checkAll =
    if w > -1 then
      let wfs = list_wff_to_list_string (proj_l table) 0 in
      let _ = print_string_to_file (truthtable table wfs lF_to_tex nat_to_string) in 
      let models = rearrangeModels ((rnk w) lazy_mode smallest ) in
      let models_to_string = output_to_graphiz models lF_to_tex drawreflexive in
      if models_to_string = [] then
        Printf.printf "\n> ERROR: No model found with root in world (%d).\n" w
      else
        let _ = save_each_to_file models_to_string layout 0 in
        let _ = Sys.command "eog models/ &" in
        ()
    else
    if onlytable then
      let wfs = list_wff_to_list_string (proj_l table) 0 in
      let _ = print_string_to_file (truthtable table wfs lF_to_tex nat_to_string) in
      ()
    else
      if level0 then
        let wfs = list_wff_to_list_string (proj_l table) 0 in
        let _ = print_string_to_file (truthtable table wfs lF_to_tex nat_to_string) in
        ()
    else
      let rnmatrix = proj_r (checkAll lazy_mode smallest ) in
      let models = proj_l (checkAll lazy_mode smallest ) in
      let wfs = list_wff_to_list_string (proj_l rnmatrix) 0 in
      let models_to_string = output_to_graphiz models lF_to_string drawreflexive in
      let _ = save_each_to_file models_to_string layout 0 in
      let _ = print_string_to_file (matrices_str rnmatrix wfs lF_to_tex nat_to_string) in
      let _ = Sys.command "eog models/ &" in ()
    in
let tableKT45 = 
  if level0 then Kt45.makeLevel0 (expr_to_lF (parse prop)) 
  else
    Kt45.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKT45 w = Kt45.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKT45 = Kt45.makeCheckAllModels (expr_to_lF (parse prop)) in
let tableKT4 = 
  if level0 then Kt4.makeLevel0 (expr_to_lF (parse prop)) 
else  
  Kt4.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKT4 w = Kt4.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKT4 = Kt4.makeCheckAllModels (expr_to_lF (parse prop)) in
let tableKTB = 
  if level0 then Ktb.makeLevel0 (expr_to_lF (parse prop)) 
  else  
      Ktb.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKTB w = Ktb.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKTB = Ktb.makeCheckAllModels (expr_to_lF (parse prop)) in
let tableKT = 
  if level0 then Kt.makeLevel0 (expr_to_lF (parse prop)) 
  else 
    Kt.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKT w = Kt.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKT = Kt.makeCheckAllModels (expr_to_lF (parse prop)) in
let tableKD = 
  if level0 then Kd.makeLevel0 (expr_to_lF (parse prop)) 
  else 
    Kd.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKD w = Kd.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKD = Kd.makeCheckAllModels (expr_to_lF (parse prop)) in
let tableKDB = 
  if level0 then Kdb.makeLevel0 (expr_to_lF (parse prop))
  else Kdb.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKDB w = Kdb.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKDB = Kdb.makeCheckAllModels (expr_to_lF (parse prop)) in
let tableKD4 = 
  if level0 then Kd4.makeLevel0 (expr_to_lF (parse prop)) 
  else Kd4.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKD4 w = Kd4.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKD4 = Kd4.makeCheckAllModels (expr_to_lF (parse prop)) in
let tableKD5 = 
  if level0 then Kd5.makeLevel0 (expr_to_lF (parse prop)) 
  else Kd5.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKD5 w = Kd5.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKD5 = Kd5.makeCheckAllModels (expr_to_lF (parse prop)) in
let tableKD45 = 
  if level0 then Kd45.makeLevel0 (expr_to_lF (parse prop)) 
  else Kd45.makeComputeTable (expr_to_lF (parse prop)) 
in
let rnkKD45 w = Kd45.makeThisRn (int_to_nat w) (expr_to_lF (parse prop)) in
let checkAllKD45 = Kd45.makeCheckAllModels (expr_to_lF (parse prop)) in
match l with
| KT45 -> genFile tableKT45 rnkKT45 checkAllKT45
| KT4 -> genFile tableKT4 rnkKT4 checkAllKT4
| KTB -> genFile tableKTB rnkKTB checkAllKTB 
| KT -> genFile tableKT rnkKT checkAllKT
| KD -> genFile tableKD rnkKD checkAllKD 
| KDB -> genFile tableKDB rnkKDB checkAllKDB
| KD4 -> genFile tableKD4 rnkKD4 checkAllKD4
| KD5 -> genFile tableKD5 rnkKD5 checkAllKD5 
| KD45 -> genFile tableKD45 rnkKD45 checkAllKD45 ;;