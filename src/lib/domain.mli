open Mode_theory
open Sexplib

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

val env_val : env -> int -> t

val mk_var : t -> int -> t

val to_sexp : ?verb:bool -> envhead -> Sexplib.Sexp.t
val to_sexp_nf : ?verb:bool -> nf -> Sexplib.Sexp.t
val to_sexp_ne : ?verb:bool -> ne -> Sexplib.Sexp.t

val pp : ?verb:bool -> t -> string
val pp_nf : ?verb:bool -> nf -> string
val pp_ne : ?verb:bool -> ne -> string
val pp_clos : ?verb:bool -> int -> Sexp.t list -> clos -> string
val pp_env : ?verb:bool -> envhead list -> string
