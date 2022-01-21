open Mode_theory
type uni_level = int
and t =
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
(*In contrast to the Domain letmod here we do not include the typing information for the modal argument*)
type envhead =
  | Ty of t
  | Mo of m

type env = envhead list
val env_length : envhead list -> int
(*val shift : env -> t -> cell -> t*)

exception Illformed
(*  val of_sexp : Sexplib.Sexp.t -> t *)
val to_sexp : Sexplib.Sexp.t list -> t -> Sexplib.Sexp.t
val pp : t -> string
