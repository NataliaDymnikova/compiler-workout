open GT       
open Syntax

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval (st, (s, i, o)) prg =
    match prg with
    | []            -> (st, (s, i, o))
    | BINOP op :: p ->
        let y :: x :: st1 = st in
        let res = Expr.eval s (Binop (op, Const x, Const y))
        in eval (res :: st1, (s, i, o)) p
    | CONST c  :: p -> eval (c :: st, (s, i, o)) p
    | READ     :: p -> eval ((List.hd i) :: st, (s, List.tl i, o)) p
    | WRITE    :: p -> eval (List.tl st, (s, i, o @ [List.hd st])) p
    | LD x     :: p -> eval (s x :: st, (s, i, o)) p
    | ST x     :: p -> eval (List.tl st, (Expr.update x (List.hd st) s, i, o)) p

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile stmt =
    match stmt with
    | Syntax.Stmt.Read    v       -> [READ; ST v]
    | Syntax.Stmt.Write   e       -> (compileExpr e) @ [WRITE]
    | Syntax.Stmt.Assign (v, e)   -> (compileExpr e) @ [ST v]
    | Syntax.Stmt.Seq    (e1, e2) -> (compile e1) @ (compile e2)

    and compileExpr e =
        match e with
        | Syntax.Expr.Const  c         -> [CONST c]
        | Syntax.Expr.Var    v         -> [LD v]
        | Syntax.Expr.Binop (op, l, r) -> (compileExpr l) @ (compileExpr r) @ [BINOP op]
