open Sexplib
module C = Concrete_syntax
module SMap = Map.Make(String)

exception Modality_error of string
let error_m str = raise (Modality_error str)

type mode =
  | S
  | T

let equal_mode m n =
  match m, n with
  | S, S -> true
  | T, T -> true
  | _ -> false

type m_constr =
  | L
  | D
  | G

(* In this implementation the concatenation is the wrong way around, i.e. mu :: nu = nu o mu.
   This is corrected in the compm function
*)
type m = m_constr list

let equal_m mu nu =
  match  mu,  nu with
  | L, L -> true
  | D, D -> true
  | G, G -> true
  | _ -> false

let idm = []
let compm (mu, nu) = List.append nu mu

let dom_m_constr mu =
  match mu with
  | L -> T
  | D -> S
  | G -> T

let dom_mod mu mode =
  match mu with
  | [] -> mode
  | mu :: _ ->
    dom_m_constr mu

let cod_m_constr mu =
  match mu with
  | L -> T
  | D -> T
  | G -> S

let rec cod_mod mu mode =
  match mu with
  | [] -> mode
  | mu :: tail ->
    cod_mod tail (cod_m_constr mu)


let eq_mode m1 m2 =
  match m1, m2 with
  | S, S -> true
  | T, T -> true
  | _, _ -> false

let rec purge_GD mu =
  match mu with
  | [] -> []
  | D :: tail ->
    begin
      match tail with
      | G :: tail1 -> purge_GD tail1
      | lst -> D :: lst
    end
  | nu :: tail -> nu :: purge_GD tail

let rec purge_GL mu =
  match mu with
  | [] -> []
  | L :: tail ->
    begin
      match tail with
      | G :: tail1 -> G :: purge_GL tail1
      | lst -> L :: lst
    end
  | nu :: tail -> nu :: purge_GL tail

let purger mu =
  let pre_nu = ref [] in
  let post_nu = ref mu in
  while Bool.not (List.equal equal_m !pre_nu !post_nu) do
    pre_nu := !post_nu;
    let new_mu = purge_GD (!post_nu) |> purge_GL in
    post_nu := new_mu
  done;
  !post_nu

let rec leq mu nu =
  match purger mu, purger nu with
  | [], [] -> true
  | G :: D :: tail1 , G :: D :: tail2 | L :: tail1, L :: tail2 -> leq tail1 tail2
  | G :: D :: tail, nu -> leq tail nu
  | nu, L :: tail -> leq nu tail
  | mu1 :: tail1 , mu2 :: tail2 -> Bool.(&&) (equal_m mu1 mu2) (leq tail1 tail2)
  | _ -> false

let eq_mod mu nu = Bool.(&&) (leq mu nu) (leq nu mu)

(* We only have the identity and compositions of it.
   Hence if the domain of the cells are equal, there is no flex.
*)

let mode_to_sexp = function
  | S -> Sexp.Atom "s"
  | T -> Sexp.Atom "t"

let mode_pp m = mode_to_sexp m |> Sexp.to_string_hum

let m_constr_sexp mu =
  match mu with
  | L -> Sexp.Atom "l"
  | D -> Sexp.Atom "d"
  | G -> Sexp.Atom "g"

let mod_to_sexp mu =
  let rec rec_helper mu =
    match List.rev mu with
    | [] -> []
    | mu :: tail -> m_constr_sexp mu :: rec_helper tail in
  Sexp.List (rec_helper mu)

let mod_pp mu = mod_to_sexp mu |> Sexp.to_string_hum

(* Maps for binding modalities, cells and modes *)

let mode_smap = [("s", S); ("S", S); ("t", T); ("T", T)] |> List.to_seq |> SMap.of_seq

let m_smap = [("l", L); ("d", D); ("g", G)] |> List.to_seq |> SMap.of_seq

let m_macros = [("box", "g" :: ["d"])] |> List.to_seq |> SMap.of_seq

let cell_smap = [("dg_id", ([G; D], [])); ("id_l", ([], [L]))] |> List.to_seq |> SMap.of_seq

let bind_mode str =
  match SMap.find_opt str mode_smap with
  | Some v -> v
  | None -> error_m (str ^ " is not a mode of the bowling pin")

let find_mod str =
  match SMap.find_opt str m_smap with
  | Some v -> v
  | None -> error_m (str ^ " is not a modality of bowling pin")

let find_cell str =
  match SMap.find_opt str cell_smap with
  | Some v -> v
  | None -> error_m (str ^ " is not a 2-cell of the bowling pin")

(* Macros should be purged during the bind process, so that the constructors are not part of the backend *)
let rec purge_macros mu =
  match mu with
  | [] -> []
  | str :: tail ->
    let new_tail = purge_macros tail in
    match SMap.find_opt str m_macros with
    | Option.Some lst -> List.append lst new_tail
    | Option.None -> str :: new_tail

let rec bind_m mu =
  match purge_macros mu with
  | [] -> []
  | str :: tail ->
    let bound_mod = (find_mod str) in
    let bound_tail = bind_m tail in
    if equal_mode (cod_m_constr bound_mod) (dom_mod bound_tail (cod_m_constr bound_mod)) then bound_mod :: bound_tail
    else error_m (mod_pp (bound_mod :: bound_tail) ^ " is not well-formed")
