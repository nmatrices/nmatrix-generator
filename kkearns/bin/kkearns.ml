open Rnkripke;;

let () = print_endline "\n> Welcome to RNKripke 1.0.\n";;

Sys.command "rm -fr models && mkdir -p models";;
Sys.command "rm -fr matrices && mkdir -p matrices";;

(*
Sys.command "(if exist models rmdir /s /q models) && mkdir models";;
Sys.command "(if exist matrices rmdir /s /q matrices) && mkdir matrices";;
*)
module Cmd = struct
  type t = { 
    smallest : bool;
    lazy_mode : bool;
    level0 : bool;
    l : string; 
    g : string; 
    r : bool; 
    t : bool; 
    w : int; 
    prop : string;
  }

let usage = "
Usage:
 rnk [-l <string>] [-g <string>] <prop>

1) Description

  rnk (from RNKripke) build Kripke Models from Restricted Non-Deterministic Matrices. To generate the graphs, the software use Graphviz tool.

"
let parse () =
  let w = ref (-1) in
  let lazy_mode = ref true in
  let smallest = ref false in
  let level0 = ref false in
  let t = ref false in
  let r = ref false in
  let l = ref "S5" in
  let g = ref "" in
  let prop = ref None in
  let specs = [
    "-lazy_mode", Arg.Set lazy_mode, "Model construction lazy mode (construct the biggest model).";
    "-smallest", Arg.Set smallest, "Present only the smallest models for each row.";
    "-level0", Arg.Set level0, "Compute only the level 0 (no restrictions)";
    "-l", Arg.Set_string l, "Logic.";
    "-g", Arg.Set_string g, "Graphviz optional arguments.";
    "-r", Arg.Set r, "Draw reflexive edges.";
    "-t", Arg.Set t, "Generate only the RNmatrix.";
    "-w", Arg.Set_int w, "Construct an specific model (with root in w).";
    "--logic", Arg.Set_string l, "Logic.";
    "--graphviz", Arg.Set_string g, "Graphviz optional arguments."
  ] in
  let anon str = prop := Some str in
  Arg.parse specs anon usage;
  {
    smallest = !smallest;
    lazy_mode = !lazy_mode;
    level0 = !level0;
    l = !l;
    g = !g;
    r = !r;
    t = !t;
    w = !w;
    prop = match !prop with
      | Some m ->
        m
      | None ->
        Arg.usage specs usage;
        invalid_arg "<prop> is required";
  }
end

let () =
  let { Cmd.smallest; Cmd.lazy_mode; Cmd.level0; Cmd.l; Cmd.g; Cmd.r; prop; Cmd.t; Cmd.w } = Cmd.parse () in
  let _ = time (modelCli l prop g (not r) t w smallest) lazy_mode level0 in
  Printf.printf "\n> Thank you for using RNKripke. See you back soon! \n" ;;