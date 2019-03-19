open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env (st, (s, i, o)) prg =
    match prg with
    | []            -> (st, (s, i, o))
    | BINOP op :: p ->
        let y :: x :: st1 = st in
        let res = Expr.eval s (Binop (op, Const x, Const y))
        in eval env (res :: st1, (s, i, o)) p
    | CONST c  :: p -> eval env (c :: st, (s, i, o)) p
    | READ     :: p -> eval env ((List.hd i) :: st, (s, List.tl i, o)) p
    | WRITE    :: p -> eval env (List.tl st, (s, i, o @ [List.hd st])) p
    | LD x     :: p -> eval env (s x :: st, (s, i, o)) p
    | ST x     :: p -> eval env (List.tl st, (Expr.update x (List.hd st) s, i, o)) p
    | LABEL l  :: p -> eval env (st, (s, i, o)) p
    | JMP l    :: _ -> eval env (st, (s, i, o)) (env#labeled l)
    | CJMP (z, l) :: p ->
        let b = if z = "z" then (List.hd st) == 0 else (List.hd st) != 0 in
        if b then eval env (List.tl st, (s, i, o)) (env#labeled l) else eval env (List.tl st, (s, i, o)) p

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
  | Stmt.While (e, s)  ->
    let r = string_of_int (Random.int 10000) in
    [JMP ("l_check"^r); LABEL ("l_loop"^r)] @ compile s @ [LABEL ("l_check"^r)] @ expr e @ [CJMP ("nz", ("l_loop"^r))]
  | Stmt.If (e, s1, s2)  ->
    let r = string_of_int (Random.int 10000) in
    expr e @ [CJMP ("z", ("l_else"^r))] @ compile s1 @ [JMP ("l_end"^r); LABEL ("l_else"^r)] @ compile s2 @ [LABEL ("l_end"^r)]
  | Stmt.Skip          -> []
  | Stmt.Repeat (s, e) ->
      let r = string_of_int (Random.int 10000) in
      [LABEL ("l_repeat"^r)] @ compile s @ expr e @ [CJMP ("z", ("l_repeat"^r))]
