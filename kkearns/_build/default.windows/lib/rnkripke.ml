open Model
open Kt4
open Kt
open Ipl
open Typecoercion

let parse_kt4 s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog_kt4 Lexer.read lexbuf in
  ast;;

let parse_kt s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog_kt Lexer.read lexbuf in
  ast;;

let parse_ipl s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog_ipl Lexer.read lexbuf in
  ast;;

let makeLabel p l lf_to_string =
  let w = string_of_int (nat_to_int p) in
  if l = [] then " " else
    w ^ " [label=< " ^ w ^ ":<B>" ^ (list_lf_to_string l lf_to_string) ^ "</B> >];\n";;

let rec makeLabels l lf_to_string = match l with
  | [] -> ""
  | h::t -> (makeLabel (proj_l h) (proj_r h) lf_to_string) ^ (makeLabels t lf_to_string);;

let rec output_to_graphiz l lf_to_string drawreflexive = match l with
| [] -> []
| h::t -> 
    (Pair (nat_to_int (proj_l h), ((makeLabels (proj_l (proj_r h)) lf_to_string)^(list_node_to_string (proj_r (proj_r h)) drawreflexive))))
      ::(output_to_graphiz t lf_to_string drawreflexive);;

let rec save_each_to_file l layout = match l with
  | [] -> ()
  | h::t ->
    Printf.printf "Make model with root in (%d). File models/model%d.svg.\n" (proj_l h) (proj_l h);
    let graphvizcmd = 
      "echo \"digraph { graph [root="^(string_of_int ((proj_l h)))^", label=\\\"Root in world ("^string_of_int(proj_l h)^
      ")\\\"]; edge [arrowhead=vee]; node [color=darkred fillcolor=ghostwhite style=filled shape=box3d]; "
      ^ (string_of_int ((proj_l h))) ^ "[color=darkgreen]"
      ^ " outputorder=edgesfirst; layout=circo;  "
      ^layout^ " "
      ^ (proj_r h) ^ " }\" | dot -Tsvg > models\\model" 
      ^ (string_of_int (proj_l h)) ^ ".svg" in
    (*let _ = Printf.printf "\nGraphviz command: %s\n\n" graphvizcmd in*)
    let _ = 
      Sys.command graphvizcmd
    in
    save_each_to_file t layout;;

(*
(**** CLI *****)
*)

type propo =
| KT_l of lF
| KT4_l of extendedLF
| IPL_l of iLF

type logic =
| KT
| KT4
| IPL

let string_to_logic = function
  | "KT4" -> KT4
  | "KT" -> KT
  | "T" -> KT
  | "IPL" -> IPL
  | "S4" -> KT4
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
  let oc = open_out "matrices\\matrices.md" in
  Printf.fprintf oc "%s" s;
  Printf.printf "\n\nMatrices saved in matrices/matrices.md\n";
  let _ = close_out oc in
  (*Sys.command ("((pandoc -f markdown -t latex --standalone matrices/matrices.md > matrices/matrices.tex " 
  ^ "&& pdflatex -interaction=\"batchmode\" -output-directory=\"matrices/\" matrices/matrices.tex > /dev/null 2>&1)" 
  ^ " && start matrices/matrices.pdf)");;*)
  Sys.command ("(pandoc -f markdown -t latex --standalone matrices\\matrices.md > matrices\\matrices.tex && pdflatex -interaction=batchmode -output-directory=matrices\ matrices\\matrices.tex > NUL 2>&1) && start matrices\\matrices.pdf");;
let modelCli logic prop layout drawreflexive otf onlytable w = 
  let l = string_to_logic logic in
  let des = match l with
    | KT4 -> "{1,2}"
    | KT -> "{1,2}"
    | IPL -> "{$\\textbf{T}$}" in
  let _ = if otf then Printf.printf "\n> Using reduction on the fly. \n" in
  let header = "---\ndocumentclass: extarticle\nfontsize: 14pt\n---\n\n" in
  let truthtable rnmatrix wfs wf_to_tex nat_to_string = 
    header^"\n# Restricted Nmatrix in "^logic^"\n\n" 
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
    ^ (print_rnmatrix (proj_r rnmatrix) nat_to_string) ^ "\n\\pagebreak\n## Semantic matrix (Kripke models)\n"
    ^ "\n| World "^wfs^"\n"^(make_header ((List.length (proj_l rnmatrix)+1)))^"\n" 
    ^ (print_semantic_matrix (proj_r rnmatrix)) in
  match l with
  | KT4 ->
    if w > -1 then
      let table = 
        if otf then
          Kt4.makeComputeTable Kt4.makeMakeIt_otf (expr_to_extendedLF (parse_kt4 prop))
        else
          Kt4.makeComputeTable Kt4.makeMakeIt (expr_to_extendedLF (parse_kt4 prop)) in
      let wfs = list_wff_to_list_string (proj_l table) 0 in
      let _ = print_string_to_file (truthtable table wfs extendedLF_to_tex nat_to_string) in 
      let rnk = 
        if otf then
          Kt4.makeThisRn (int_to_nat w) Kt4.makeMakeIt_otf (expr_to_extendedLF (parse_kt4 prop))
        else
          Kt4.makeThisRn (int_to_nat w) Kt4.makeMakeIt (expr_to_extendedLF (parse_kt4 prop)) in
      let models = rearrangeModels rnk in
      let models_to_string = output_to_graphiz models extendedLF_to_string drawreflexive in
      if models_to_string = [] then
        Printf.printf "\n> ERROR: No model found with root in world (%d).\n" w
      else
        let _ = save_each_to_file models_to_string layout in
        let _ = Sys.command "start models\\ " in
        ()
    else
    if onlytable then
      let table = 
        if otf then
          Kt4.makeComputeTable Kt4.makeMakeIt_otf (expr_to_extendedLF (parse_kt4 prop))
        else
          Kt4.makeComputeTable Kt4.makeMakeIt (expr_to_extendedLF (parse_kt4 prop)) in
      let wfs = list_wff_to_list_string (proj_l table) 0 in
      let _ = print_string_to_file (truthtable table wfs extendedLF_to_tex nat_to_string) in
      ()
    else
    let rnk = 
      if otf then
        Kt4.makeCheckAllModels Kt4.makeMakeIt_otf (expr_to_extendedLF (parse_kt4 prop))
      else
        Kt4.makeCheckAllModels Kt4.makeMakeIt (expr_to_extendedLF (parse_kt4 prop)) in
    let rnmatrix = proj_r rnk in
    let models = proj_l rnk in
    let wfs = list_wff_to_list_string (proj_l rnmatrix) 0 in
    let models_to_string = output_to_graphiz models extendedLF_to_string drawreflexive in
    let _ = save_each_to_file models_to_string layout in
    let _ = print_string_to_file (matrices_str rnmatrix wfs extendedLF_to_tex nat_to_string) in
    let _ = Sys.command "start models\\ " in
    ()
  | KT ->
    if w > -1 then
      let table = 
        if otf then
          Kt.makeComputeTable Kt.makeMakeIt_otf (expr_to_lf (parse_kt prop))
        else
          Kt.makeComputeTable Kt.makeMakeIt (expr_to_lf (parse_kt prop)) in
      let wfs = list_wff_to_list_string (proj_l table) 0 in
      let _ = print_string_to_file (truthtable table wfs lf_to_tex nat_to_string) in 
      let rnk = 
        if otf then
          Kt.makeThisRn (int_to_nat w) Kt.makeMakeIt_otf (expr_to_lf (parse_kt prop))
        else
          Kt.makeThisRn (int_to_nat w) Kt.makeMakeIt (expr_to_lf (parse_kt prop)) in
      let models = rearrangeModels rnk in
      let models_to_string = output_to_graphiz models lf_to_string drawreflexive in
      if models_to_string = [] then
        Printf.printf "\n> ERROR: No model found with root in world (%d).\n" w
      else
        let _ = save_each_to_file models_to_string layout in
        let _ = Sys.command "start models\\ " in
        ()
    else
    if onlytable then
      let table = 
        if otf then
          Kt.makeComputeTable Kt.makeMakeIt_otf (expr_to_lf (parse_kt prop))
        else
          Kt.makeComputeTable Kt.makeMakeIt (expr_to_lf (parse_kt prop)) in
      let wfs = list_wff_to_list_string (proj_l table) 0 in
      let _ = print_string_to_file (truthtable table wfs lf_to_tex nat_to_string) in 
      ()
    else
    let rnk = 
      if otf then 
        Kt.makeCheckAllModels (Kt.makeMakeIt_otf) (expr_to_lf (parse_kt prop))
      else
        Kt.makeCheckAllModels (Kt.makeMakeIt_otf) (expr_to_lf (parse_kt prop)) in
    let rnmatrix = proj_r rnk in
    let models = proj_l rnk in
    let models_to_string = output_to_graphiz models lf_to_string drawreflexive in
    let wfs = list_wff_to_list_string (proj_l rnmatrix) 0 in
    let _ = save_each_to_file models_to_string layout in
    let _ = print_string_to_file (matrices_str rnmatrix wfs lf_to_tex nat_to_string) in
    let _ = Sys.command "start models\\ " in 
    ()
  | IPL -> 
    if w > -1 then
      let table = 
        if otf then
          Ipl.makeComputeTable Ipl.makeMakeIt_otf (expr_to_ilf (parse_ipl prop))
        else
          Ipl.makeComputeTable Ipl.makeMakeIt (expr_to_ilf (parse_ipl prop)) in
      let wfs = list_wff_to_list_string (proj_l table) 0 in
      let _ = print_string_to_file (truthtable table wfs ilf_to_tex nat_to_string) in 
      let rnk = 
        if otf then
          Ipl.makeThisRn (int_to_nat w) Ipl.makeMakeIt_otf (expr_to_ilf (parse_ipl prop))
        else
          Ipl.makeThisRn (int_to_nat w) Ipl.makeMakeIt (expr_to_ilf (parse_ipl prop)) in
      let models = rearrangeModels rnk in
      let models_to_string = output_to_graphiz models ilf_to_string drawreflexive in
      if models_to_string = [] then
        Printf.printf "\n> ERROR: No model found with root in world (%d).\n" w
      else
        let _ = save_each_to_file models_to_string layout in
        let _ = Sys.command "start models\\ " in
        ()
    else
    if onlytable then
      let table = 
        if otf then
          Ipl.makeComputeTable Ipl.makeMakeIt_otf (expr_to_ilf (parse_ipl prop))
        else
          Ipl.makeComputeTable Ipl.makeMakeIt (expr_to_ilf (parse_ipl prop)) in
      let wfs = list_wff_to_list_string (proj_l table) 0 in
      let _ = print_string_to_file (truthtable table wfs ilf_to_tex nat_to_ipl_truth_val) in 
      ()
    else
    let rnk = 
      if otf then 
        Ipl.makeCheckAllModels Ipl.makeMakeIt_otf (expr_to_ilf (parse_ipl prop))
      else
        Ipl.makeCheckAllModels Ipl.makeMakeIt (expr_to_ilf (parse_ipl prop)) in
    let rnmatrix = proj_r rnk in
    let models = proj_l rnk in
    let models_to_string = output_to_graphiz models ilf_to_string drawreflexive in
    let wfs = list_wff_to_list_string (proj_l rnmatrix) 0 in
    let _ = save_each_to_file models_to_string layout in
    let _ = print_string_to_file (matrices_str rnmatrix wfs ilf_to_tex nat_to_ipl_truth_val) in 
    let _ = Sys.command "start models\\ " in 
    ();;
