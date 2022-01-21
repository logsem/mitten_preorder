module type S =
sig
  open Sexplib
  module C = Concrete_syntax

  exception Modality_error of string

  type mode
  type m

  val idm : m
  val compm : m * m -> m

  val dom_mod : m -> mode -> mode
  val cod_mod : m -> mode -> mode

  val eq_mode : mode -> mode -> bool
    (* leq is the function that takes two modalities and returns true IFF there exists a two cell between these modalities (this 2-cell is unique, since we are in a preorder mode theory) *)
  val leq : m -> m -> bool
    (* eq_mod takes two modalities and returns true IFF the modalities are equal. A posetal mode theory can use leq here. Otherwise it boils down to checking the boundaries.  *)
  val eq_mod : m -> m -> bool

  val mode_to_sexp : mode -> Sexp.t
  val mode_pp : mode -> string

  val mod_to_sexp : m -> Sexp.t
  val mod_pp : m -> string

  (* Binding functions, inspiration can be taken from the guarded_mode_theory.ml file.
   *  Note, that during the binding process modalities have to be checked for composability!!*)
  val bind_mode : C.mode -> mode
  val bind_m : C.m -> m
end
