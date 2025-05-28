open Rnkripke;;

let () = print_endline "\n> Welcome to kearns 1.2.\n";;

Sys.command "rm -fr models && mkdir -p models";;
Sys.command "rm -fr matrices && mkdir -p matrices";;

(*
Sys.command "(if exist models rmdir /s /q models) && mkdir models";;
Sys.command "(if exist matrices rmdir /s /q matrices) && mkdir matrices";;
*)
module Cmd = struct
  type t = { 
    level0 : bool;
    l : string; 
    g : string;
    silent : bool;
    m : bool; 
    prop : string;
  }

let usage = "
Usage:
 kearns [-l <string>] [-g <string>] [-level0 | -m | -s] <prop : string>

1) Description

  kearns is a matrix generator. It can be used to decide the validity of formulas in normal modal logics extending K with axioms D, T, B, 4 and 5, as well as to produce counter-models for invalid formulas in each logic. The semantics is based on the extension presented in [1] of J. Kearns' non-determinitic truth tables with level valuations. Graphs are rendered using Graphviz and the pdf files are created with LaTeX (via pandoc).

  [1] Leme, R., Olarte, C., Pimentel, E., & Coniglio, M. E. (2025). The Modal Cube Revisited: Semantics without Worlds. arXiv preprint arXiv:2505.12824.

"
let parse () =
  let level0 = ref false in
  let m = ref false in
  let l = ref "S5" in
  let g = ref "" in
  let silent = ref false in
  let prop = ref None in
  let specs = [
    "-level0", Arg.Set level0, "Compute only the level 0 (no restrictions)";
    "-l", Arg.Set_string l, "Logic.";
    "-silent", Arg.Set silent, "Silent mode (do not open files).";
    "-g", Arg.Set_string g, "Graphviz optional arguments.";
    "-m", Arg.Set m, "Generate Kripke models.";
    "--logic", Arg.Set_string l, "Logic.";
    "--graphviz", Arg.Set_string g, "Graphviz optional arguments."
  ] in
  let anon str = prop := Some str in
  Arg.parse specs anon usage;
  {
    level0 = !level0;
    l = !l;
    g = !g;
    m = !m;
    silent = !silent;
    prop = match !prop with
      | Some m ->
        m
      | None ->
        Arg.usage specs usage;
        invalid_arg "<prop> is required";
  }
end

let () =
  let { Cmd.level0; Cmd.l; Cmd.g; prop; Cmd.m; Cmd.silent } = Cmd.parse () in
  let _ = modelCli l prop g true (not m) (-1) false true level0 silent in
  Printf.printf "\n> Thank you for using kearns. See you back soon! \n" ;;