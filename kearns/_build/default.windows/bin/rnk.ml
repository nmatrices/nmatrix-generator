open Rnkripke;;

let () = print_endline "\n> Welcome to RNKripke 1.0.\n";;
(*
Sys.command "rm -fr models && mkdir -p models";;
Sys.command "rm -fr matrices && mkdir -p matrices";;
*)

Sys.command "(if exist models rmdir /s /q models) && mkdir models";;
Sys.command "(if exist matrices rmdir /s /q matrices) && mkdir matrices";;

module Cmd = struct
  type t = { l : string; g : string; r : bool; f : bool; t : bool; w : int; prop : string }

let usage = "
Usage:
 rnk [-l <string>] [-g <string>] <prop>

1) Description

  rnk (from RNKripke) build Kripke Models from Restricted Non-Deterministic Matrices. To generate the graphs, we use the Graphviz library.

"
let parse () =
  let w = ref (-1) in
  let t = ref false in
  let f = ref false in
  let r = ref false in
  let l = ref "IPL" in
  let g = ref "" in
  let prop = ref None in
  let specs = [
    "-w", Arg.Set_int w, "Construct an specific model (with root in w).";
    "-t", Arg.Set t, "Generate only the RNmatrix.";
    "-f", Arg.Set f, "Reduction on the fly.";
    "-r", Arg.Set r, "Draw reflexive edges.";
    "-l", Arg.Set_string l, "Logic.";
    "--logic", Arg.Set_string l, "Logic.";
    "-g", Arg.Set_string g, "Graphviz optional arguments.";
    "--graphviz", Arg.Set_string g, "Graphviz optional arguments."
  ] in
  let anon str = prop := Some str in
  Arg.parse specs anon usage;
  {
    w = !w;
    t = !t;
    f = !f;
    r = !r;
    l = !l;
    g = !g;
    prop = match !prop with
      | Some m ->
        m
      | None ->
        Arg.usage specs usage;
        invalid_arg "<prop> is required";
  }
end

let () =
  let { Cmd.g; Cmd.l; Cmd.r; prop; Cmd.f; Cmd.t; Cmd.w } = Cmd.parse () in
  let _ = modelCli l prop g (not r) f t w in 
  Printf.printf "\n\nGoodbye ............. \n";;