open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
(* drop values from stack and jmp  *) | ZJMPDROP of string * int
with show

(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((cst, st, ((s, i, o) as c)) as conf) prg =
    let instr_eval = function
        | BINOP op    ->
            let y :: x :: st = st in
            (Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)) :: st, c)
        | CONST x         -> ((Value.of_int x) :: st, c)
        | STRING x        -> ((Value.of_string (Bytes.of_string x)) :: st, c)
        | LD x            -> (State.eval s x :: st, (s, i, o))
        | ST x            -> (List.tl st, (Language.State.update x (List.hd st) s, i, o))
        | STA (x, n)      ->
            let (v::ids, tail) = split (n + 1) st in
            let s = Stmt.update s x v (List.rev ids) in
            (tail, (s, i, o))
        | LABEL l         -> (st, c)
        | BEGIN (_, a, l) ->
            let state = Language.State.enter s (a @ l) in
            let vs, st = split (List.length a) st in
            let s = List.fold_left (fun s (x, v) -> State.update x v s) state (List.combine a @@ List.rev vs) in
            (st, (s, i, o))
        | SEXP (t, n)     ->
            let vs, st = split n st in
            ((Value.sexp t @@ (List.rev vs))::st, c)
        | DROP            -> (List.tl st, c)
        | DUP             -> (List.hd st :: st, c)
        | SWAP            -> let x::y::st = st in (y::x::st, c)
        | TAG t           ->
            let x::st = st in
            let res = match x with
                | Value.Sexp (t', _) -> if (t = t') then 1 else 0
                | _                  -> 0 in
            ((Value.of_int res)::st, c)
        | ENTER xs        ->
            let vs, st = split (List.length xs) st in
            (st, (State.push s (List.fold_left (fun s (x, v) -> State.bind x v s) State.undefined (List.combine xs vs)) xs, i, o))
        | LEAVE           -> (st, (State.drop s, i, o))
    in
    match prg with
        | []           -> conf
        | JMP l       :: _ -> eval env conf (env#labeled l)
        | CJMP (z, l) :: p ->
            let v = Value.to_int (List.hd st) in
            let b = if z = "z" then v == 0 else v != 0 in
            if b then eval env (cst, List.tl st, c) (env#labeled l) else eval env (cst, List.tl st, c) p
        | CALL (f, n, fl)   :: p ->
            if env#is_label f then eval env ((p, s)::cst, st, c) (env#labeled f)
            else eval env (env#builtin (cst, st, c) f n fl) p
        | (RET _  | END)   :: _ -> (match cst with
            | (p, old_s)::cst -> eval env (cst, st, (Language.State.leave s old_s, i, o)) p
            | _ -> (cst, st, c))
        | ZJMPDROP (l, d) :: p ->
            let z::st = st in
            if Value.to_int z = 0
            then let (_,  st) = split d st in eval env (cst, st, c) (env#labeled l)
            else eval env (cst, st, c) p
        | x :: p ->
            let (st, c) = instr_eval x in
            eval env (cst, st, c) p

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (*Printf.printf "Builtin:\n";*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let label = object
    val mutable n = 0
    method get s = n <- n + 1; s ^ string_of_int n
end

(* Assume that on the top of the stack there is already a duplicated version of element *)
let rec match_pattern lFalse depth = function
  | Stmt.Pattern.Wildcard | Stmt.Pattern.Ident _ -> false, [DROP]
  | Stmt.Pattern.Sexp (t, ps) -> true, [TAG t] @ [ZJMPDROP (lFalse, depth)] @
    (List.flatten @@ List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @
        (match p with
        | Stmt.Pattern.Sexp (_, ps') ->
            if List.length ps' > 0 then [DUP] @ snd (match_pattern lFalse (depth + 1) p) @ [DROP]
            else snd (match_pattern lFalse depth p)
        | _ -> snd (match_pattern lFalse depth p))
      ) ps)

let rec make_bindings p =
  let rec inner p' = match p' with
    | Stmt.Pattern.Wildcard -> []
    | Stmt.Pattern.Ident var -> [[]]
    | Stmt.Pattern.Sexp (_, xs) ->
       let next i x = List.map (fun arr -> i::arr) (inner x) in
       List.flatten (List.mapi next xs) in
  let topElem i = [CONST i; CALL (".elem", 2, false)] in
  let extractBindValue path = [DUP] @ (List.flatten (List.map topElem path)) @ [SWAP] in
  List.flatten (List.map extractBindValue (List.rev (inner p)))

let rec compile_labeled p last_label =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String n         -> [STRING n]
  | Expr.Array a          ->
    let compiled = List.flatten (List.map expr a) in
    compiled @ [CALL (".array", (List.length compiled), false)]
  | Expr.Elem (a, i)      -> expr a @ expr i @ [CALL (".elem", 2, false)]
  | Expr.Length n         -> expr n @ [CALL (".length", 1, false)]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, args) ->
    let compile_args = List.flatten @@ List.map expr args in
    compile_args @ [CALL (f, List.length args, false)]
  | Expr.Sexp (t, xs)     ->
    let compiled = List.flatten (List.map expr xs) in
    compiled @ [SEXP (t, List.length xs)]
  in match p with
  | Stmt.Seq (s1, s2)  ->
    let new_label = label#get "l_seq" in
    let (compiled1, used1) = compile_labeled s1 new_label in
    let (compiled2, used2) = compile_labeled s2 last_label in
    compiled1 @ (if used1 then [LABEL new_label] else []) @ compiled2, used2
  | Stmt.Assign (x, [], e) -> (expr e @ [ST x]), false
  | Stmt.Assign (x, is, e) -> List.flatten (List.map expr (is @ [e])) @ [STA (x, List.length is)], false
  | Stmt.While (e, s)  ->
    let check = label#get "l_check" in
    let loop = label#get "l_loop" in
    let (compiled, _) = compile_labeled s check in
    [JMP check; LABEL loop] @ compiled @ [LABEL check] @ expr e @ [CJMP ("nz", loop)], false
  | Stmt.If (e, s1, s2) ->
    let l_else = label#get "l_else" in
    let (if_body, used1) = compile_labeled s1 last_label in
    let (else_body, used2) = compile_labeled s2 last_label in
    expr e @ [CJMP ("z", l_else)]
        @ if_body @ (if used1 then [] else [JMP last_label]) @ [LABEL l_else]
        @ else_body @ (if used2 then [] else [JMP last_label]), true
  | Stmt.Skip          -> [], false
  | Stmt.Repeat (s, e) ->
    let l_repeat = label#get "l_repeat" in
    let (compiled, _) = compile_labeled s last_label in
    [LABEL l_repeat] @ compiled @ expr e @ [CJMP ("z", l_repeat)], false
  | Stmt.Call (f, args) ->
    let compile_args = List.flatten @@ List.map expr args in
    compile_args @ [CALL (f, List.length args, true)], false
  | Stmt.Return e       -> (match e with
                            | Some x -> (expr x) @ [RET true]
                            | _ -> [RET false]), false
  | Stmt.Leave            -> [LEAVE], false
  | Stmt.Case (e, [p, s]) -> (* TODO: Reverse match_pattern return tuple *)
    let pUsed, pCode = match_pattern last_label 0 p in
    let sBody, sUsed = compile_labeled (Stmt.Seq (s, Stmt.Leave)) last_label in
    expr e @ [DUP] @ pCode @ make_bindings p @ [DROP; ENTER (List.rev (Stmt.Pattern.vars p))] @ sBody, pUsed || sUsed
  | Stmt.Case (e, bs)      ->
    let n = List.length bs - 1 in
    let _, _, code = List.fold_left
        (fun (l, i, code) (p, s) ->
            let lFalse, jmp = if i = n then last_label, []
                else label#get "l_case", [JMP last_label] in
             let _, pCode = match_pattern lFalse 0 p in
             let sBody, _ = compile_labeled (Stmt.Seq (s, Stmt.Leave)) last_label in
             let amLabel = match l with Some x -> [LABEL x; DUP] | None -> [] in
             (Some lFalse, i + 1, (amLabel @ pCode @ make_bindings p @ [DROP; ENTER (List.rev (Stmt.Pattern.vars p))] @ sBody @ jmp) :: code)
                ) (None, 0, []) bs in
        expr e @ [DUP] @ List.flatten @@ List.rev code, true

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