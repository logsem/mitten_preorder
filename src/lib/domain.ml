open Mode_theory

type envhead =
  | Val of t
  | M of m
and env = envhead list
and clos = Clos of {term : Syntax.t; env : env}
and clos2 = Clos2 of {term : Syntax.t; env : env}
and clos3 = Clos3 of {term : Syntax.t; env : env}
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of m * t * clos
  | Sig of t * clos
  | Pair of t * t
  | Refl of t
  | Id of t * t * t
  | Uni of Syntax.uni_level
  | Tymod of m * t
  | Mod of m * t
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of m * ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of clos * t * clos2 * ne
  | Letmod of m * m * clos * clos * t * ne
  | J of clos3 * clos * t * t * t * ne
  | Axiom of string * t
and nf =
  | Normal of {tp : t; term : t}

let mk_var tp lev = Neutral {tp; term = Var lev}

(* env_val is giving the nth entry of the environment list, ONLY counting values. env_cell then gives the corresponding
   cell as it is required for the nbe algorithm *)

let rec env_val env i =
  match env with
  | [] -> failwith "env_val should not reach the empty list"
  | head :: lst ->
    match head with
    | Val v -> if Int.equal i 0 then v
      else if i > 0 then env_val lst (i - 1)
      else failwith "env_cell does not accept negativ Input"
    | M _ -> env_val lst i

