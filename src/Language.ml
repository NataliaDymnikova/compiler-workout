(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)

    let rec eval st expr =
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
      parse:
	  !(Ostap.Util.expr
             (fun x -> x)
	     (Array.map (fun (a, s) -> a,
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        )
              [|
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |]
	     )
	     primary);

      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env (s, i, o) t =
        match t with
        | Read    v       -> (State.update v (List.hd i) s, List.tl i, o)
        | Write   e       -> (s, i, o @ [Expr.eval s e])
        | Assign (v, e)   -> (State.update v (Expr.eval s e) s, i, o)
        | Seq    (e1, e2) ->
            let stmt = eval env (s, i, o) e1
            in eval env stmt e2
        | Skip            -> (s, i, o)
        | If (e1, e2, e3) ->
            if (Expr.eval s e1) != 0 then eval env (s, i, o) e2 else eval env (s, i, o) e3
        | While (e1, e2)  ->
            let r = Expr.eval s e1 in
            if r != 0 then eval env (eval env (s, i, o) e2) (While (e1, e2)) else (s, i, o)
        | Repeat (e1, e2)  ->
            let (s, i, o) = eval env (s, i, o) e1 in
            let r = Expr.eval s e2 in
            if r != 0 then (s, i ,o) else eval env (s, i, o) t
        | Call (name, args) ->
            let (arg_names, locals, body) = env#definition name in
            let args = List.combine arg_names (List.map (Expr.eval s) args) in
            let state = State.push_scope s (arg_names @ locals) in
            let fun_env_w_args = List.fold_left (fun s (name, value) -> State.update name value s) state args in
            let (new_s, i, o) = eval env (fun_env_w_args, i, o) body in
            (State.drop_scope new_s s, i, o)

    (* Statement parser *)
    ostap (
      line:
          "read" "(" x:IDENT ")"         {Read x}
        | "write" "(" e:!(Expr.parse) ")" {Write e}
        | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
        | "if" e1:!(Expr.parse) "then" e2:parse "else" e3:parse "fi" {If (e1, e2, e3)}
        | "if" e1:!(Expr.parse) "then" e2:parse "fi" {If (e1, e2, Skip)}
        | "if" e1:!(Expr.parse) "then" e2:parse e3:elif {If (e1, e2, e3)}
        | "skip" {Skip}
        | "while" e1:!(Expr.parse) "do" e2:parse "od" {While (e1, e2)}
        | "repeat" e1:parse "until" e2:!(Expr.parse) {Repeat (e1, e2)}
        | "for" e1:parse "," e2:!(Expr.parse) "," e3:parse "do" s:parse "od" {Seq (e1, While (e2, Seq(s, e3)))}
        | name:IDENT "(" args:(!(Expr.parse))* ")" {Call (name, args)};

      parse:
          l:line ";" rest:parse {Seq (l, rest)} | line;

      elif:
          "elif" e1:!(Expr.parse) "then" e2:parse "else" e3:parse "fi" {If (e1, e2, e3)}
        | "elif" e1:!(Expr.parse) "then" e2:parse "fi" {If (e1, e2, Skip)}
        | "elif" e1:!(Expr.parse) "then" e2:parse e3:elif {If (e1, e2, e3)}
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: "fun" name:IDENT "(" args:(IDENT)* ")" local:(%"local" (IDENT)*)? "{" body:!(Stmt.parse) "}"
        {
            let local = match local with
            | Some x -> x
            | _ -> [] in
            name, (args, local, body)
        }
    )

  end
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
