
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | RPAREN
    | NEG
    | LPAREN
    | IMPL
    | EOF
    | DISJ
    | CONJ
    | BOX
    | ATOM of (
# 5 "lib/parser/parser.mly"
       (string)
# 23 "lib/parser/parser.ml"
  )
  
end

include MenhirBasics

# 1 "lib/parser/parser.mly"
  
open Ast

# 34 "lib/parser/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_prog_ipl) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: prog_ipl. *)

  | MenhirState01 : (('s, _menhir_box_prog_ipl) _menhir_cell1_NEG, _menhir_box_prog_ipl) _menhir_state
    (** State 01.
        Stack shape : NEG.
        Start symbol: prog_ipl. *)

  | MenhirState02 : (('s, _menhir_box_prog_ipl) _menhir_cell1_LPAREN, _menhir_box_prog_ipl) _menhir_state
    (** State 02.
        Stack shape : LPAREN.
        Start symbol: prog_ipl. *)

  | MenhirState06 : (('s, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl, _menhir_box_prog_ipl) _menhir_state
    (** State 06.
        Stack shape : expr_ipl.
        Start symbol: prog_ipl. *)

  | MenhirState08 : (('s, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl, _menhir_box_prog_ipl) _menhir_state
    (** State 08.
        Stack shape : expr_ipl.
        Start symbol: prog_ipl. *)

  | MenhirState10 : (('s, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl, _menhir_box_prog_ipl) _menhir_state
    (** State 10.
        Stack shape : expr_ipl.
        Start symbol: prog_ipl. *)

  | MenhirState16 : ('s, _menhir_box_prog_kt) _menhir_state
    (** State 16.
        Stack shape : .
        Start symbol: prog_kt. *)

  | MenhirState17 : (('s, _menhir_box_prog_kt) _menhir_cell1_NEG, _menhir_box_prog_kt) _menhir_state
    (** State 17.
        Stack shape : NEG.
        Start symbol: prog_kt. *)

  | MenhirState18 : (('s, _menhir_box_prog_kt) _menhir_cell1_LPAREN, _menhir_box_prog_kt) _menhir_state
    (** State 18.
        Stack shape : LPAREN.
        Start symbol: prog_kt. *)

  | MenhirState19 : (('s, _menhir_box_prog_kt) _menhir_cell1_BOX, _menhir_box_prog_kt) _menhir_state
    (** State 19.
        Stack shape : BOX.
        Start symbol: prog_kt. *)

  | MenhirState24 : (('s, _menhir_box_prog_kt) _menhir_cell1_expr_kt, _menhir_box_prog_kt) _menhir_state
    (** State 24.
        Stack shape : expr_kt.
        Start symbol: prog_kt. *)

  | MenhirState30 : ('s, _menhir_box_prog_kt4) _menhir_state
    (** State 30.
        Stack shape : .
        Start symbol: prog_kt4. *)

  | MenhirState31 : (('s, _menhir_box_prog_kt4) _menhir_cell1_NEG, _menhir_box_prog_kt4) _menhir_state
    (** State 31.
        Stack shape : NEG.
        Start symbol: prog_kt4. *)

  | MenhirState32 : (('s, _menhir_box_prog_kt4) _menhir_cell1_LPAREN, _menhir_box_prog_kt4) _menhir_state
    (** State 32.
        Stack shape : LPAREN.
        Start symbol: prog_kt4. *)

  | MenhirState33 : (('s, _menhir_box_prog_kt4) _menhir_cell1_BOX, _menhir_box_prog_kt4) _menhir_state
    (** State 33.
        Stack shape : BOX.
        Start symbol: prog_kt4. *)

  | MenhirState38 : (('s, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4, _menhir_box_prog_kt4) _menhir_state
    (** State 38.
        Stack shape : expr_kt4.
        Start symbol: prog_kt4. *)

  | MenhirState40 : (('s, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4, _menhir_box_prog_kt4) _menhir_state
    (** State 40.
        Stack shape : expr_kt4.
        Start symbol: prog_kt4. *)

  | MenhirState42 : (('s, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4, _menhir_box_prog_kt4) _menhir_state
    (** State 42.
        Stack shape : expr_kt4.
        Start symbol: prog_kt4. *)


and ('s, 'r) _menhir_cell1_expr_ipl = 
  | MenhirCell1_expr_ipl of 's * ('s, 'r) _menhir_state * (Ast.expr_ipl)

and ('s, 'r) _menhir_cell1_expr_kt = 
  | MenhirCell1_expr_kt of 's * ('s, 'r) _menhir_state * (Ast.expr_kt)

and ('s, 'r) _menhir_cell1_expr_kt4 = 
  | MenhirCell1_expr_kt4 of 's * ('s, 'r) _menhir_state * (Ast.expr_kt4)

and ('s, 'r) _menhir_cell1_BOX = 
  | MenhirCell1_BOX of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_NEG = 
  | MenhirCell1_NEG of 's * ('s, 'r) _menhir_state

and _menhir_box_prog_kt4 = 
  | MenhirBox_prog_kt4 of (Ast.expr_kt4) [@@unboxed]

and _menhir_box_prog_kt = 
  | MenhirBox_prog_kt of (Ast.expr_kt) [@@unboxed]

and _menhir_box_prog_ipl = 
  | MenhirBox_prog_ipl of (Ast.expr_ipl) [@@unboxed]

let _menhir_action_03 =
  fun x ->
    (
# 55 "lib/parser/parser.mly"
             ( Atom_ipl x )
# 160 "lib/parser/parser.ml"
     : (Ast.expr_ipl))

let _menhir_action_04 =
  fun e ->
    (
# 56 "lib/parser/parser.mly"
                      ( Neg_ipl e )
# 168 "lib/parser/parser.ml"
     : (Ast.expr_ipl))

let _menhir_action_05 =
  fun e1 e2 ->
    (
# 57 "lib/parser/parser.mly"
                                       ( Conj_ipl (e1, e2) )
# 176 "lib/parser/parser.ml"
     : (Ast.expr_ipl))

let _menhir_action_06 =
  fun e1 e2 ->
    (
# 58 "lib/parser/parser.mly"
                                       ( Disj_ipl (e1, e2) )
# 184 "lib/parser/parser.ml"
     : (Ast.expr_ipl))

let _menhir_action_07 =
  fun e1 e2 ->
    (
# 59 "lib/parser/parser.mly"
                                       ( Impl_ipl (e1, e2) )
# 192 "lib/parser/parser.ml"
     : (Ast.expr_ipl))

let _menhir_action_08 =
  fun e ->
    (
# 60 "lib/parser/parser.mly"
                               (e)
# 200 "lib/parser/parser.ml"
     : (Ast.expr_ipl))

let _menhir_action_09 =
  fun x ->
    (
# 47 "lib/parser/parser.mly"
             ( Atom_kt x )
# 208 "lib/parser/parser.ml"
     : (Ast.expr_kt))

let _menhir_action_10 =
  fun e ->
    (
# 48 "lib/parser/parser.mly"
                     ( Box_kt e )
# 216 "lib/parser/parser.ml"
     : (Ast.expr_kt))

let _menhir_action_11 =
  fun e ->
    (
# 49 "lib/parser/parser.mly"
                     ( Neg_kt e )
# 224 "lib/parser/parser.ml"
     : (Ast.expr_kt))

let _menhir_action_12 =
  fun e1 e2 ->
    (
# 50 "lib/parser/parser.mly"
                                     ( Impl_kt (e1, e2) )
# 232 "lib/parser/parser.ml"
     : (Ast.expr_kt))

let _menhir_action_13 =
  fun e ->
    (
# 51 "lib/parser/parser.mly"
                              (e)
# 240 "lib/parser/parser.ml"
     : (Ast.expr_kt))

let _menhir_action_14 =
  fun x ->
    (
# 37 "lib/parser/parser.mly"
             ( Atom_kt4 x )
# 248 "lib/parser/parser.ml"
     : (Ast.expr_kt4))

let _menhir_action_15 =
  fun e ->
    (
# 38 "lib/parser/parser.mly"
                      ( Box_kt4 e )
# 256 "lib/parser/parser.ml"
     : (Ast.expr_kt4))

let _menhir_action_16 =
  fun e ->
    (
# 39 "lib/parser/parser.mly"
                      ( Neg_kt4 e )
# 264 "lib/parser/parser.ml"
     : (Ast.expr_kt4))

let _menhir_action_17 =
  fun e1 e2 ->
    (
# 40 "lib/parser/parser.mly"
                                       ( Conj_kt4 (e1, e2) )
# 272 "lib/parser/parser.ml"
     : (Ast.expr_kt4))

let _menhir_action_18 =
  fun e1 e2 ->
    (
# 41 "lib/parser/parser.mly"
                                       ( Disj_kt4 (e1, e2) )
# 280 "lib/parser/parser.ml"
     : (Ast.expr_kt4))

let _menhir_action_19 =
  fun e1 e2 ->
    (
# 42 "lib/parser/parser.mly"
                                       ( Impl_kt4 (e1, e2) )
# 288 "lib/parser/parser.ml"
     : (Ast.expr_kt4))

let _menhir_action_20 =
  fun e ->
    (
# 43 "lib/parser/parser.mly"
                               (e)
# 296 "lib/parser/parser.ml"
     : (Ast.expr_kt4))

let _menhir_action_21 =
  fun e ->
    (
# 33 "lib/parser/parser.mly"
                      ( e )
# 304 "lib/parser/parser.ml"
     : (Ast.expr_ipl))

let _menhir_action_22 =
  fun e ->
    (
# 25 "lib/parser/parser.mly"
                     ( e )
# 312 "lib/parser/parser.ml"
     : (Ast.expr_kt))

let _menhir_action_23 =
  fun e ->
    (
# 29 "lib/parser/parser.mly"
                      ( e )
# 320 "lib/parser/parser.ml"
     : (Ast.expr_kt4))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ATOM _ ->
        "ATOM"
    | BOX ->
        "BOX"
    | CONJ ->
        "CONJ"
    | DISJ ->
        "DISJ"
    | EOF ->
        "EOF"
    | IMPL ->
        "IMPL"
    | LPAREN ->
        "LPAREN"
    | NEG ->
        "NEG"
    | RPAREN ->
        "RPAREN"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog_ipl) _menhir_state -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NEG (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState01 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_02 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog_ipl) _menhir_state -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState02 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_ipl) _menhir_state -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let x = _v in
      let _v = _menhir_action_03 x in
      _menhir_goto_expr_ipl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr_ipl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_ipl) _menhir_state -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState01 ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState10 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState08 ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState06 ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState02 ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_14 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_ipl) _menhir_state -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | IMPL ->
          let _menhir_stack = MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF ->
          let e = _v in
          let _v = _menhir_action_21 e in
          MenhirBox_prog_ipl _v
      | DISJ ->
          let _menhir_stack = MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | CONJ ->
          let _menhir_stack = MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack. (ttv_stack, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl -> _ -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState06 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_08 : type  ttv_stack. (ttv_stack, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl -> _ -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState08 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack. (ttv_stack, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl -> _ -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState10 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_12 : type  ttv_stack. (ttv_stack, _menhir_box_prog_ipl) _menhir_cell1_NEG -> _ -> _ -> _ -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NEG (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_04 e in
      _menhir_goto_expr_ipl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_11 : type  ttv_stack. (ttv_stack, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl -> _ -> _ -> _ -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_05 e1 e2 in
      _menhir_goto_expr_ipl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_09 : type  ttv_stack. (ttv_stack, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl -> _ -> _ -> _ -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_06 e1 e2 in
      _menhir_goto_expr_ipl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_07 : type  ttv_stack. (ttv_stack, _menhir_box_prog_ipl) _menhir_cell1_expr_ipl -> _ -> _ -> _ -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_07 e1 e2 in
      _menhir_goto_expr_ipl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_04 : type  ttv_stack. ((ttv_stack, _menhir_box_prog_ipl) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog_ipl) _menhir_state -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_08 e in
          _menhir_goto_expr_ipl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | IMPL ->
          let _menhir_stack = MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DISJ ->
          let _menhir_stack = MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer
      | CONJ ->
          let _menhir_stack = MenhirCell1_expr_ipl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  let _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog_ipl =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState00 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  let rec _menhir_run_17 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt) _menhir_state -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NEG (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState17 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_18 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt) _menhir_state -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState18 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_19 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt) _menhir_state -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_BOX (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState19 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_20 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt) _menhir_state -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let x = _v in
      let _v = _menhir_action_09 x in
      _menhir_goto_expr_kt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr_kt : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt) _menhir_state -> _ -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState16 ->
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState24 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState18 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState19 ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_28 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt) _menhir_state -> _ -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | IMPL ->
          let _menhir_stack = MenhirCell1_expr_kt (_menhir_stack, _menhir_s, _v) in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF ->
          let e = _v in
          let _v = _menhir_action_22 e in
          MenhirBox_prog_kt _v
      | _ ->
          _eRR ()
  
  and _menhir_run_24 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt) _menhir_cell1_expr_kt -> _ -> _ -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState24 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_26 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt) _menhir_cell1_NEG -> _ -> _ -> _ -> _ -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NEG (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_11 e in
      _menhir_goto_expr_kt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_25 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt) _menhir_cell1_expr_kt -> _ -> _ -> _ -> _ -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_kt (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_12 e1 e2 in
      _menhir_goto_expr_kt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_22 : type  ttv_stack. ((ttv_stack, _menhir_box_prog_kt) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog_kt) _menhir_state -> _ -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_13 e in
          _menhir_goto_expr_kt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | IMPL ->
          let _menhir_stack = MenhirCell1_expr_kt (_menhir_stack, _menhir_s, _v) in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_21 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt) _menhir_cell1_BOX -> _ -> _ -> _ -> _ -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_BOX (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_10 e in
      _menhir_goto_expr_kt _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  let _menhir_run_16 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog_kt =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState16 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  let rec _menhir_run_31 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt4) _menhir_state -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NEG (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState31 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_32 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt4) _menhir_state -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState32 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_33 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt4) _menhir_state -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_BOX (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState33 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_34 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt4) _menhir_state -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let x = _v in
      let _v = _menhir_action_14 x in
      _menhir_goto_expr_kt4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr_kt4 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt4) _menhir_state -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState30 ->
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState31 ->
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState42 ->
          _menhir_run_43 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState40 ->
          _menhir_run_41 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState38 ->
          _menhir_run_39 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState32 ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState33 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_46 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog_kt4) _menhir_state -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | IMPL ->
          let _menhir_stack = MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF ->
          let e = _v in
          let _v = _menhir_action_23 e in
          MenhirBox_prog_kt4 _v
      | DISJ ->
          let _menhir_stack = MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | CONJ ->
          let _menhir_stack = MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_38 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4 -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState38 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_40 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4 -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState40 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_42 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4 -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState42 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_44 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_NEG -> _ -> _ -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_NEG (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_16 e in
      _menhir_goto_expr_kt4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_43 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4 -> _ -> _ -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_17 e1 e2 in
      _menhir_goto_expr_kt4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_41 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4 -> _ -> _ -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_18 e1 e2 in
      _menhir_goto_expr_kt4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_39 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_expr_kt4 -> _ -> _ -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let e2 = _v in
      let _v = _menhir_action_19 e1 e2 in
      _menhir_goto_expr_kt4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_36 : type  ttv_stack. ((ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog_kt4) _menhir_state -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_20 e in
          _menhir_goto_expr_kt4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | IMPL ->
          let _menhir_stack = MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DISJ ->
          let _menhir_stack = MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | CONJ ->
          let _menhir_stack = MenhirCell1_expr_kt4 (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_35 : type  ttv_stack. (ttv_stack, _menhir_box_prog_kt4) _menhir_cell1_BOX -> _ -> _ -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_BOX (_menhir_stack, _menhir_s) = _menhir_stack in
      let e = _v in
      let _v = _menhir_action_15 e in
      _menhir_goto_expr_kt4 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  let _menhir_run_30 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog_kt4 =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState30 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NEG ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOX ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ATOM _v ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
end

let prog_kt4 =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog_kt4 v = _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v

let prog_kt =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog_kt v = _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v

let prog_ipl =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog_ipl v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
