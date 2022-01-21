type ident = string
type uni_level = int

type mode = string

type m = string list

type cell =
  | Idc of m
  | Atom of string
  | HComp of cell * cell
  | VComp of cell * cell

type binder = Binder of {name : ident; body : t}
and bindern = BinderN of {names : ident list; body : t}
and binder2 = Binder2 of {name1 : ident; name2 : ident; body : t}
and binder3 = Binder3 of {name1 : ident; name2 : ident; name3 : ident; body : t}
and t =
  | Var of ident
  | Let of t * binder
  | Check of {term : t; tp : t}
  | Nat
  | Suc of t
  | Lit of int
  | NRec of {mot : binder; zero : t; suc : binder2; nat : t}
  | Pi of m * t * binder
  | Lam of bindern
  | Ap of t * (m * t) list
  | Sig of t * binder
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Id of t * t * t
  | Refl of t
  | J of {mot : binder3; refl : binder; eq : t}
  | Uni of uni_level
  | TyMod of m * t
  | Mod of m * t
  | Letmod of m * m * binder * binder * t

type decl =
    Def of {name : ident; def : t; tp : t; md : mode}
  | NormalizeDef of ident
  | NormalizeTerm of {term : t; tp : t; md : mode}
  | Axiom of {name : ident; tp : t; md : mode}
  | Quit

type signature = decl list
