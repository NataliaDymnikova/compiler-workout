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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env ((cst, st, ((s, i, o) as c)) as conf) prg =
    match prg with
    | []            -> (cst, st, (s, i, o))
    | BINOP op :: p ->
        let y :: x :: st = st in
        eval env (cst, Expr.to_func op x y :: st, (s, i, o)) p
    | CONST c  :: p -> eval env (cst, c :: st, (s, i, o)) p
    | READ     :: p -> eval env (cst, (List.hd i) :: st, (s, List.tl i, o)) p
    | WRITE    :: p -> eval env (cst, List.tl st, (s, i, o @ [List.hd st])) p
    | LD x     :: p -> eval env (cst, State.eval s x :: st, (s, i, o)) p
    | ST x     :: p -> eval env (cst, List.tl st, (Language.State.update x (List.hd st) s, i, o)) p
    | LABEL l  :: p -> eval env (cst, st, (s, i, o)) p
    | JMP l    :: _ -> eval env (cst, st, (s, i, o)) (env#labeled l)
    | CJMP (z, l) :: p ->
        let b = if z = "z" then (List.hd st) == 0 else (List.hd st) != 0 in
        if b then eval env (cst, List.tl st, (s, i, o)) (env#labeled l) else eval env (cst, List.tl st, (s, i, o)) p
    | BEGIN (_, a, l) :: p ->
        let state = Language.State.enter s (a @ l) in
        let s, st = List.fold_left (fun (s, x::stack) name -> (State.update name x s, stack)) (state, st) a in
        eval env (cst, st, (s, i, o)) p
    | CALL (f, _, _)   :: p -> eval env ((p, s)::cst, st, (s, i, o)) (env#labeled f)
    | (RET _  | END)   :: _ -> (match cst with
        | (p, old_s)::cst -> eval env (cst, st, (Language.State.leave s old_s, i, o)) p
        | _ -> (cst, st, c))

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let label = object
    val mutable n = 0
    method get s = n <- n + 1; s ^ string_of_int n
end

let rec compile_labeled p last_label =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, args)   ->
    let compile_args = List.concat (List.map (expr) (List.rev args)) in
    compile_args @ [CALL (f, List.length args, true)]
  in match p with
  | Stmt.Seq (s1, s2)  ->
    let new_label = label#get "l_seq" in
    let (compiled1, used1) = compile_labeled s1 new_label in
    let (compiled2, used2) = compile_labeled s2 last_label in
    compiled1 @ (if used1 then [LABEL new_label] else []) @ compiled2, used2
  | Stmt.Read x        -> [READ; ST x], false
  | Stmt.Write e       -> expr e @ [WRITE], false
  | Stmt.Assign (x, e) -> expr e @ [ST x], false
  | Stmt.While (e, s)  ->
    let check = label#get "l_check" in
    let loop = label#get "l_loop" in
    let (compiled, _) = compile_labeled s check in
    [JMP check; LABEL loop] @ compiled @ [LABEL check] @ expr e @ [CJMP ("nz", loop)], false
  | Stmt.If (e, s1, s2) ->
    let l_else = label#get "l_else" in
    let (if_body, used1) = compile_labeled s1 last_label in
    let (else_body, used2) = compile_labeled s2 last_label in
    expr e @ [CJMP ("z", l_else)] @ if_body @ (if used1 then [] else [JMP last_label]) @ [LABEL l_else] @ else_body @ (if used2 then [] else [JMP last_label]), true
  | Stmt.Skip          -> [], false
  | Stmt.Repeat (s, e) ->
    let l_repeat = label#get "l_repeat" in
    let (compiled, _) = compile_labeled s last_label in
    [LABEL l_repeat] @ compiled @ expr e @ [CJMP ("z", l_repeat)], false
  | Stmt.Call (f, args) ->
    List.concat (List.map (expr) (List.rev args)) @ [CALL (f, List.length args, false)], false
  | Stmt.Return e       -> (match e with
                            | Some x -> (expr x) @ [RET true]
                            | _ -> [RET false]), false

let rec compile_main p =
    let l = label#get "l_main" in
    let compiled, used = compile_labeled p l in
    compiled @ (if used then [LABEL l] else [])

let rec compile_defs defs =
    List.fold_left (fun (p) (name, (args, locals, body)) ->
        let body = compile_main body in
        p @ [LABEL name] @ [BEGIN (name, args, locals)] @ body @ [END]) ([]) defs

let rec compile (defs, p) =
    let p = compile_main p in
    let defs = compile_defs defs in
    p @ [END] @ defs