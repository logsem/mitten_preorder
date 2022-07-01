exception Nbe_failed of string

(* Main functions for doing a full normalization *)
val normalize : env:Syntax.env -> term:Syntax.t -> tp:Syntax.t -> Syntax.t

(* Evaluate a syntactic term into a semantic value *)
val eval : Syntax.t -> Domain.env -> Domain.t

val read_back_nf : int -> Domain.nf -> Syntax.t
val read_back_tp : int -> Domain.t -> Syntax.t

(* Check whether a semantic element is equal to another *)
val check_nf : Mode_theory.mode -> int -> Domain.nf -> Domain.nf -> bool
val check_ne : Mode_theory.mode -> int -> Domain.ne -> Domain.ne -> bool
(* If subtype = true then we check whether the first argument is a subtype of the latter *)
val check_tp : Mode_theory.mode -> subtype:bool -> int -> Domain.t -> Domain.t -> bool

(* Functions to manipulate elements of the semantic domain *)
val gen_do_clos : Domain.clos -> Domain.envhead -> Domain.t
val gen_do_clos2 : Domain.clos2 -> Domain.envhead -> Domain.envhead -> Domain.t
val do_clos : Domain.clos -> Domain.t -> Domain.t
val do_clos2 : Domain.clos2 -> Domain.t -> Domain.t -> Domain.t
val do_ap : Domain.t -> Domain.t -> Domain.t
