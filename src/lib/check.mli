open Mode_theory
type env_entry =
    Term of {term : Domain.t; mu : m; tp : Domain.t; md : mode}
  | TopLevel of {term : Domain.t; tp : Domain.t; md : mode}
  | M of m
type env = env_entry list

val env_to_sem_env : env -> Domain.env

type error =
    Cannot_synth_term of Syntax.t
  | Type_mismatch of Domain.t * Domain.t * Syntax.t
  | Term_or_Type_mismatch of Domain.nf * Domain.nf
  | Expecting_universe of Domain.t
  | Misc of string

val pp_error : error -> string

exception Type_error of error

val check : env:env -> size:int -> term:Syntax.t -> tp:Domain.t -> m:mode -> unit
val synth : env:env -> size:int -> term:Syntax.t -> m:mode -> Domain.t
val check_tp : env:env -> size:int -> term:Syntax.t -> m:mode -> unit
