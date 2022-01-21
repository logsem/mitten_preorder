open Sexplib
module C = Concrete_syntax

exception Modality_error of string

type mode = unit
type m_constr =
  | Mu
and m = m_constr list

and cell =
  | Idc of m
  | VComp of cell * cell (* fully annotating the cells with domain and codomain *)
  | HComp of cell * cell

(* Macros for readability *)
let idm = []
let compm (mu, nu) = List.append nu mu

let idc mu = Idc mu
let vcomp (alpha, beta) = VComp (alpha, beta)
let hcomp (alpha, beta) = HComp (alpha, beta)
let idcell = idc idm

let whisker alpha mu = HComp (alpha, Idc (mu))

let dom_mod mu mode =
  match mu with
  | [] -> mode
  | _ -> ()

let cod_mod mu mode =
  match mu with
  | [] -> mode
  | _ -> ()

let rec dom_cell alpha =
  match alpha with
  | Idc mu -> mu
  | VComp (alpha, _) -> dom_cell alpha
  | HComp (alpha, beta) -> compm (dom_cell alpha, dom_cell beta)

let rec cod_cell alpha =
  match alpha with
  | Idc mu -> mu
  (*Vertical composition, i.e. just the normal morphism composition*)
  | VComp (_, beta) -> cod_cell beta
  (* Horizontal composition, i.e. glue two cells together to be a cell between the concatenated modalities *)
  | HComp (alpha, beta) -> compm (cod_cell alpha, cod_cell beta)

let triv_l_hcomp mu alpha = HComp (alpha, Idc mu)
let triv_r_hcomp mu alpha = HComp (Idc mu, alpha)

let eq_mode _ _ = true

let count_mu = List.length

let eq_mod mu nu = Int.equal (List.length mu) (List.length nu)
let leq mu nu = eq_mod mu nu

(* We only have the identity and compositions of it. Hence if the domain of the cells are equal, there is no flex. *)
let eq_cell ~cod:_ alpha beta =
  eq_mod (dom_cell alpha) (dom_cell beta)

let rec rewrite_cell alpha =
  match alpha with
  | Idc mu -> Idc mu
  | VComp (beta, Idc _) -> rewrite_cell beta
  | VComp (Idc _, beta) -> rewrite_cell beta
  | HComp (beta, Idc _) -> rewrite_cell beta
  | HComp (Idc _, beta) -> rewrite_cell beta
  | beta -> beta

let mode_to_sexp _ = Sexp.Atom "m"
let mode_pp _ = "m"

(* only print id if the list is empty *)
let mod_to_sexp mu =
  let rec rec_helper mu =
    match mu with
    | [] -> []
    | Mu :: tail -> Sexp.Atom "mu" :: rec_helper tail
  in
  Sexp.List (rec_helper mu)

let mod_pp mu = mod_to_sexp mu |> Sexp.to_string_hum

let rec cell_to_sexp alpha =
  let helper = function
    | Idc mu -> Sexp.List [Sexp.Atom "Id"; mod_to_sexp mu]
    | VComp (alpha, beta) -> Sexp.List [Sexp.Atom "o"; cell_to_sexp alpha; cell_to_sexp beta]
    | HComp (alpha, beta) -> Sexp.List [Sexp.Atom "*"; cell_to_sexp alpha ; cell_to_sexp beta] in
  rewrite_cell alpha |> helper

let cell_pp alpha = cell_to_sexp alpha |> Sexp.to_string_hum

let bind_mode str = if String.equal str "m" then () else raise (Modality_error (str ^ " is not a mode"))

let find_mod str = if String.equal str "mu" then Mu else raise (Modality_error (str ^ " is not a modality"))

let rec bind_m mu =
  match mu with
  | [] -> []
  | str :: tail -> (find_mod str) :: bind_m tail

let rec bind_cell alpha =
  match alpha with
  | C.Idc mu -> Idc (bind_m mu)
  | C.HComp (alpha, beta) -> HComp (bind_cell alpha, bind_cell beta)
  | C.VComp (alpha, beta) -> VComp (bind_cell alpha, bind_cell beta)
  | C.Atom str -> raise (Modality_error (str ^ " is not a 2-cell in trivial mode theory"))
