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
  | Box

(* In this implementation the concatenation is the wrong way around, i.e. mu :: nu = nu o mu.
   This is corrected in the compm function
 *)
(* In particular: [m1 :: m2 :: m3 ...] is parsed as m3 o m2 o m1, this turns out this way because of the binding routine*)

type m = m_constr list

let equal_m mu nu =
  match  mu,  nu with
  | L, L -> true
  | D, D -> true
  | G, G -> true
  | Box, Box -> true
  | _ -> false

let idm = []
let compm (mu, nu) = List.append nu mu

let dom_m_constr mu =
  match mu with
  | L -> T
  | D -> S
  | G -> T
  | Box -> T

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
  | Box -> T

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

(* A small NbE algorithm to evaluate modalities to normal forms *)
(* L = Later, B = Box, D = Delta, G = Gamma *)
(* Due to the rewriting system of the bowling pin mode theory our normal forms should be of the form *)

type nf_m =
  | Sem_L of int
  | LB of int
  | LD of int
  | Sem_G

(* Sem_L 0 is the identity modality for any mode. we do not need to consider the modes for normalization, here we may assume that the modalities are already well formed *)
let sem_id = Sem_L 0

let nf_eq mu nu =
  match mu, nu with
  | Sem_L n , Sem_L m -> Int.equal n m
  | LB n , LB m -> Int.equal n m
  | LD n , LD m -> Int.equal n m
  | Sem_G , Sem_G -> true
  | _ -> false

let nf_leq mu nu =
  match mu, nu with
  | Sem_L n , Sem_L m -> n <= m
  | LB n , LB m -> n <= m
  | LD n , LD m -> n <= m
  | Sem_G , Sem_G -> true
  | _ -> false

let eval_m_constr mu =
  match mu with
  | L -> Sem_L 1
  | D -> LD 0
  | G -> Sem_G
  | Box -> LB 0

(* Composition of Normal form with modality constructor. Again composition is the wrong way around, so that we can use fold_left... *)
(* nf_comp Sem_L G  == G o Sem_L *)
let nf_comp nf mu =
  match nf , mu with
  | Sem_L n , L -> Sem_L (n + 1)
  | Sem_L _ , G -> Sem_G
  | Sem_L _ , Box -> LB 0
  | LB n , L -> LB (n + 1)
  | LB _ , G -> Sem_G
  | LB _ , Box -> LB 0
  | Sem_L 0 , D -> LD 0
  | LD n , L -> LD (n + 1)
  | LD _ , G -> sem_id
  | LD _ , Box -> LD 0
  | Sem_G , D -> LB 0
  | _ -> error_m "Not well defined composition of modalities or mistake in normal form algorithm, check nf_comp in mode theory implementation"

let eval mu = List.fold_left nf_comp sem_id mu

let leq mu nu = nf_leq (eval mu) (eval nu)

let eq_mod mu nu = nf_eq (eval mu) (eval nu)

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
  | Box -> Sexp.Atom "box"

let mod_to_sexp mu =
  let rec rec_helper mu =
    match List.rev mu with
    | [] -> []
    | mu :: tail -> m_constr_sexp mu :: rec_helper tail in
  Sexp.List (rec_helper mu)

let mod_pp mu = mod_to_sexp mu |> Sexp.to_string_hum

(* Maps for binding modalities, cells and modes *)

let mode_smap = [("s", S); ("S", S); ("t", T); ("T", T)] |> List.to_seq |> SMap.of_seq

let m_smap = [("l", L); ("d", D); ("g", G); ("box", Box)] |> List.to_seq |> SMap.of_seq

(*let m_macros = [("box", "g" :: ["d"])] |> List.to_seq |> SMap.of_seq *)

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

(* Macros should be expand during the bind process, so that the constructors are not part of the backend *)
(*let rec expand_macros mu =
  match mu with
  | [] -> []
  | str :: tail ->
    let new_tail = expand_macros tail in
    match SMap.find_opt str m_macros with
    | Option.Some lst -> List.append lst new_tail
    | Option.None -> str :: new_tail
*)

let rec bind_m mu =
  match mu with
  | [] -> []
  | str :: tail ->
    let bound_mod = (find_mod str) in
    let bound_tail = bind_m tail in
    if equal_mode (cod_m_constr bound_mod) (dom_mod bound_tail (cod_m_constr bound_mod)) then bound_mod :: bound_tail
    else error_m (mod_pp (bound_mod :: bound_tail) ^ " is not well-formed")
