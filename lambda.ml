(*
 * (c) 2014 Andreas Rossberg
 *)

(*
 * Modified by Shon Feder in 2018
 *)

(* Syntax *)

type var = string
type lab = string

module Env = Map.Make(String)
type env = value Env.t

and exp =
  | VarE of var
  | PrimE of Prim.const
  | IfE of exp * exp * exp
  | LamE of var * exp
  | AppE of exp * exp
  | TupE of exp list
  | DotE of exp * int
  | RecE of var * exp
  | LetE of exp * var * exp

and value =
  | PrimV of Prim.const
  | TupV of value list
  | FunV of env * var * exp
  | RecV of value option ref

let rec string_of_exp = function
  | VarE var       -> var
  | PrimE prim     -> Prim.string_of_const prim
  | IfE(c, t, f)   -> Printf.sprintf "(if %s then %s else %s)" (string_of_exp c) (string_of_exp t) (string_of_exp f)
  | LamE(v, e)     -> Printf.sprintf "\%s.(%s)" v (string_of_exp e)
  | AppE(e, e')    -> Printf.sprintf "(%s %s)" (string_of_exp e) (string_of_exp e')
  | TupE es        -> Printf.sprintf "(%s)" (String.concat " * " @@ List.map string_of_exp es)
  | DotE(e, i)     -> Printf.sprintf "(DotE?? %s %s)" (string_of_exp e) (string_of_int i)
  | RecE(v, e)     -> Printf.sprintf "rec %s %s" v (string_of_exp e)
  | LetE(e, v, e') -> Printf.sprintf "let %s = %s in %s" (string_of_exp e) v (string_of_exp e')

(* String conversion *)

let rec string_of_value = function
  | PrimV(c) -> Prim.string_of_const c
  | TupV(vs) -> "[" ^ String.concat ", " (List.map string_of_value vs) ^ "]"
  | FunV(env, x, e) -> Printf.sprintf "(\\ %s %s)" x (string_of_exp e)
  | RecV(r) ->
    match !r with
    | Some v -> string_of_value v
    | None -> "_"


(* Evaluation *)

exception Error of string

let rec consts_of_value = function
  | PrimV(c) -> [c]
  | TupV(vs) -> List.map (fun v -> List.hd (consts_of_value v)) vs
  | v -> raise (Error ("AppE2: " ^ string_of_value v))

let value_of_consts = function
  | [c] -> PrimV(c)
  | cs -> TupV(List.map (fun c -> PrimV(c)) cs)

let rec unroll = function
  | RecV(r) ->
    (match !r with
    | Some v -> unroll v
    | None -> raise (Error "RecE: _")
    )
  | v -> v

let rec eval env e = unroll (eval' env e)

and eval' env = function
  | VarE(x) ->
    (try Env.find x env with Not_found -> raise (Error ("VarE: " ^ x)))
  | PrimE(c) -> PrimV(c)
  | IfE(e1, e2, e3) ->
    (match eval env e1 with
    | PrimV(Prim.BoolV(b)) -> eval env (if b then e2 else e3)
    | v -> raise (Error ("IfE: " ^ string_of_value v))
    )
  | LamE(x, e) -> FunV(env, x, e)
  | AppE(e1, e2) ->
    (match eval env e1, eval env e2 with
    | FunV(env', x, e), v2 -> eval (Env.add x v2 env') e
    | PrimV(Prim.FunV f), v2 -> value_of_consts (f.Prim.fn (consts_of_value v2))
    | v1, _ -> raise (Error ("AppE1: " ^ string_of_value v1))
    )
  | TupE(es) -> TupV(List.map (eval env) es)
  | DotE(e, i) ->
    (match eval env e with
    | TupV(vs) -> List.nth vs i
    | v -> raise (Error ("DotE: " ^ string_of_value v))
    )
  | RecE(x, e) ->
    let r = ref None in
    let v = eval (Env.add x (RecV(r)) env) e in
    r := Some v;
    v
  | LetE(e1, x, e2) -> let v1 = eval env e1 in eval (Env.add x v1 env) e2
