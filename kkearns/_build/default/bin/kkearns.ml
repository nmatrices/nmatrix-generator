open Rnkripke;;

let () = print_endline "\n> Welcome to kkearns 1.1.\n";;

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
    m : bool; 
    prop : string;
  }

let usage = "
Usage:
 kkearns [-l <string>] [-g <string>] [-level0 | -m] <prop : string>

1) Description

  kkearns (Kripke-Kearns) build truth-tables and Kripke Models using the Restricted Non-Deterministic Matrices theory based on Kearns' level valuations. Graphs are rendered using Graphviz and the pdf files are created with LaTeX (via pandoc).

"
let parse () =
  let level0 = ref false in
  let m = ref false in
  let l = ref "S5" in
  let g = ref "" in
  let prop = ref None in
  let specs = [
    "-level0", Arg.Set level0, "Compute only the level 0 (no restrictions)";
    "-l", Arg.Set_string l, "Logic.";
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
    prop = match !prop with
      | Some m ->
        m
      | None ->
        Arg.usage specs usage;
        invalid_arg "<prop> is required";
  }
end

let () =
  let { Cmd.level0; Cmd.l; Cmd.g; prop; Cmd.m } = Cmd.parse () in
  let _ = modelCli l prop g true (not m) (-1) false true level0 in
  Printf.printf "\n> Thank you for using kkearns. See you back soon! \n" ;;