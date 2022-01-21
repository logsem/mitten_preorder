open Sexplib
open Mode_theory
type uni_level = int

type t =
  | Var of int (* DeBruijn indices for variables *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Pi of m * t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of m * t * t
  | Sig of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Uni of uni_level
  | TyMod of m * t
  | Mod of m * t
  | Letmod of m * m * (* BINDS *) t * (* BINDS *) t * t
  | Axiom of string * t

type envhead =
  | Ty of t
  | Mo of m

type env = envhead list

exception Illformed

let rec nth lst id =
  match lst with
  | [] -> failwith "syntax shift mistake, context too short?"
  | x :: xs -> if Int.equal id 0 then x else nth xs (id - 1)

let rec env_length lst =
  match lst with
  | [] -> 0
  | Ty _ :: xs -> (env_length xs) + 1
  | Mo _ :: xs -> (env_length xs)

let find_idx ~equal key xs =
  let rec go i = function
    | [] -> None
    | x :: xs ->
      if equal key x then Some i else go (i + 1) xs in
  go 0 xs

let to_sexp env t =
  let counter = ref 0 in
  let rec int_of_syn = function
    | Zero -> Some 0
    | Suc t ->
      begin
        match int_of_syn t with
        | Some i -> Some (i + 1)
        | None -> None
      end
    | _ -> None in
  let rec go env = function
    (* need pp for cells to pretty print variables also for non trivial cells *)
    | Var i -> if i >= List.length env
      then Sexp.Atom ("free" ^ string_of_int i)
      else List.nth env i
    | Nat -> Sexp.Atom "Nat"
    | Let (def, body) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List
        [Sexp.Atom "let";
         Sexp.List [var; go env def];
         go (var :: env) body]
    | Check (term, tp) -> Sexp.List [Sexp.Atom "check"; go env term; go env tp]
    | Zero -> Sexp.Atom "zero"
    | Suc t ->
      begin
        match int_of_syn t with
        | Some i -> Sexp.Atom (string_of_int (i + 1))
        | None -> Sexp.List [Sexp.Atom "suc"; go env t]
      end
    | NRec (motive, zero, suc, n) ->
      incr counter;
      let mvar = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let suc_var1 = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let suc_var2 = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List
        [Sexp.Atom "nrec";
         Sexp.List [mvar; go (mvar :: env) motive];
         go env zero;
         Sexp.List [suc_var1; suc_var2; go (suc_var2 :: suc_var1 :: env) suc];
         go env n]
    | Pi (mu, src, dest) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Pi"; mod_to_sexp mu; go env src; Sexp.List [var; Sexp.Atom "->"; go (var :: env) dest]]
    | Lam t ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "lam"; Sexp.List [var; go (var :: env) t]]
    | Ap (mu, t1, t2) ->
      Sexp.List [Sexp.Atom "ap"; mod_to_sexp mu; go env t1; go env t2]
    | Sig (fst, snd) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Sig"; go env fst; Sexp.List [var; go (var :: env) snd]]
    | Pair (t1, t2) ->
      Sexp.List [Sexp.Atom "pair"; go env t1; go env t2]
    | Fst t -> Sexp.List [Sexp.Atom "fst"; go env t]
    | Snd t -> Sexp.List [Sexp.Atom "snd"; go env t]
    | Uni i -> Sexp.List [Sexp.Atom "U"; Sexp.Atom (string_of_int i)]
    | TyMod (mu, tp) -> Sexp.List [Sexp.Atom "<"; mod_to_sexp mu; Sexp.Atom "|"; go env tp; Sexp.Atom ">"]
    | Mod (mu, tm) -> Sexp.List [Sexp.Atom "mod"; mod_to_sexp mu; go env tm]
    | Letmod (mu, nu, tymot, deptm, tm) ->
      incr counter;
      let mvar = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let tm_var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "let"; mod_to_sexp mu; Sexp.Atom "mod"; mod_to_sexp nu; Sexp.Atom "<-"; go env tm ; Sexp.Atom "in"; Sexp.List [go (tm_var :: env) deptm]; Sexp.Atom "at"; go (mvar :: env) tymot]
    | Id (ty, le, ri) -> Sexp.List [Sexp.Atom "Id"; go env ty; go env le; go env ri]
    | Refl term -> Sexp.List [Sexp.Atom "Refl"; go env term]
    | J (mot, refltm, eq) ->
      incr counter;
      let rivar = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let levar = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let prfvar = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "J"; go (prfvar :: levar :: rivar :: env) mot; go (levar :: env) refltm; go env eq]
    | Axiom (str, _) -> Sexp.Atom str in
  go env t

let pp t = to_sexp [] t |> Sexp.to_string_hum
