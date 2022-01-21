open Sexplib
module D = Domain
module Syn = Syntax
open Mode_theory

(* The mode is the domain of the modality mu. This is needed because the implementation of modalities is ambiguous for identity modalitities.*)
type env_entry =
    Term of {term : D.t; mu : m; tp : D.t; md : mode}
  | TopLevel of {term : D.t; tp : D.t; md : mode}
  | M of m
type env = env_entry list

let rec env_to_sexp lst =
  let helper entry =
    match entry with
    | Term {mu; tp} -> Sexp.List [Sexp.Atom "["; mod_to_sexp mu; D.to_sexp (D.Val tp); Sexp.Atom "]"]
    | TopLevel {tp} -> Sexp.List [D.to_sexp (D.Val tp)]
    | M mu -> mod_to_sexp mu
  in
  match lst with
  | [] -> []
  | entry :: tail -> helper entry :: env_to_sexp tail

let rec term_env_to_sexp lst =
  let helper entry =
    match entry with
    | Term {mu; term} -> Sexp.List [Sexp.Atom "["; mod_to_sexp mu; D.to_sexp (D.Val term); Sexp.Atom "]"]
    | TopLevel {term} -> Sexp.List [D.to_sexp (D.Val term)]
    | M mu -> mod_to_sexp mu
  in
  match lst with
  | [] -> []
  | entry :: tail -> helper entry :: term_env_to_sexp tail

let env_pp lst = Sexp.List (env_to_sexp lst) |> Sexp.to_string_hum

let add_term ~md ~term ~mu ~tp env = Term {term; mu; tp; md} :: env

type error =
    Cannot_synth_term of Syn.t
  | Type_mismatch of D.t * D.t
  | Expecting_universe of D.t
  | Misc of string

let pp_error = function
  | Cannot_synth_term t -> "Cannot synthesize the type of:\n" ^ Syn.pp t
  | Type_mismatch (t1, t2) -> "Cannot equate\n" ^ D.pp t1 ^ "\nwith\n" ^ D.pp t2
  | Expecting_universe d -> "Expected some universe but found\n" ^ D.pp d
  | Misc s -> s

exception Type_error of error

let tp_error e = raise (Type_error e)

let env_to_sem_env =
  List.map
    (function
      | TopLevel {term; _} -> D.Val term
      | Term {term; mu = _; tp = _} -> D.Val term
      | M mu -> D.M mu)

let rec nth_lockless lst i =
  match lst with
  | [] -> tp_error (Misc "nth_lockless should not reach the empty list")
  | head :: lst ->
    match head with
    | Term {term; mu; tp; md} -> if Int.equal i 0 then (Term {term ; mu; tp; md} , idm)
      else if i > 0 then nth_lockless lst (i - 1)
      else tp_error (Misc "nth_lockless does not accept negativ Input")
    | TopLevel {term ; tp; md} -> if Int.equal i 0 then (TopLevel {term ; tp; md} , idm)
      else if i > 0 then nth_lockless lst (i - 1)
      else tp_error (Misc "nth_lockless does not accept negativ Input")
    | M mu -> let (tm, nu) = nth_lockless lst i in
      (tm , compm (nu, mu))

let nth_tm lst i = fst (nth_lockless lst i)
let nth_cell lst i = snd (nth_lockless lst i)

let get_var env n = match nth_tm env n with
  | Term {term = _; mu; tp; md} -> (Some mu, tp, md)
  | TopLevel {tp; term = _; md} -> (None, tp, md)
  | _ -> raise (Type_error (Misc "This case of get_var should not be reached"))

let assert_subtype m size t1 t2 =
  if Nbe.check_tp m ~subtype:true size t1 t2
  then ()
  else tp_error (Type_mismatch (t1, t2))

let assert_equal m size t1 t2 tp =
  if Nbe.check_nf m size (D.Normal {tp; term = t1}) (D.Normal {tp; term = t2})
  then ()
  else tp_error (Type_mismatch (t1, t2))

let check_mode m n =
  if eq_mode m n
  then ()
  else tp_error (Misc ("Modes do not match " ^ mode_pp m ^ " /= " ^ mode_pp n))

let check_mod nu mu errorspec =
  if eq_mod nu mu
  then ()
  else tp_error (Misc ("Modalities do not match\n" ^ mod_pp nu ^" and " ^ mod_pp mu ^ "\n" ^ errorspec))

let check_cell mu nu =
  if leq mu nu
  then ()
  else tp_error (Misc ("Cannot finde 2-cell" ^ mod_pp mu ^ "-->" ^ mod_pp nu))

let rec check ~env ~size ~term ~tp ~m =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def ~m in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    check ~env:(add_term ~md:m ~term:def_val ~mu:idm ~tp:def_tp env) ~size:(size + 1) ~term:body ~tp ~m
  | Syn.Nat ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Syn.Sig (l, r) ->
    check ~env ~size ~term:l ~tp ~m;
    let l_sem = Nbe.eval l (env_to_sem_env env) in
    let var = D.mk_var l_sem size in
    check ~env:(add_term ~md:m ~term:var ~mu:idm ~tp:l_sem env) ~size ~term:r ~tp ~m
  | Syn.Pi (mu, l, r) ->
    check_mode (cod_mod mu m) m;
    let new_env = M mu :: env in
    let new_mode = dom_mod mu m in
    check ~env:new_env ~size ~term:l ~tp ~m:new_mode;
    let l_sem = Nbe.eval l (env_to_sem_env new_env) in
    let var = D.mk_var l_sem size in
    check ~env:(add_term ~md:new_mode ~term:var ~mu:mu ~tp:l_sem env) ~size ~term:r ~tp ~m
  | Syn.Lam f ->
    begin
      match tp with
      | D.Pi (mu, src , dest) ->
        let new_mode = dom_mod mu m in
        let var = D.mk_var src size in
        let dest_tp = Nbe.do_clos dest var in
        check ~env:(add_term ~md:new_mode ~term:var ~tp:src ~mu:mu env) ~size:(size + 1) ~term:f ~tp:dest_tp ~m ;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.pp t))
    end
  | Syn.Pair (left, right) ->
    begin
      match tp with
      | D.Sig (left_tp, right_tp) ->
        check ~env ~size ~term:left ~tp:left_tp ~m;
        let left_sem = Nbe.eval left (env_to_sem_env env) in
        check ~env ~size ~term:right ~tp:(Nbe.do_clos right_tp left_sem) ~m
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.pp t))
    end
  | Syn.Uni i ->
    begin
      match tp with
      | Uni j when i < j -> ()
      | t ->
        let msg =
          "Expecting universe over " ^ string_of_int i ^ " but found\n" ^ D.pp t in
        tp_error (Misc msg)
    end
  | Syn.TyMod (mu, a) ->
    check_mode (cod_mod mu m) m;
    let new_env = M mu :: env in
    let new_mode = dom_mod mu m in
    check ~env:new_env ~size ~term:a ~tp ~m:new_mode;
  | Syn.Mod (mu, tm) ->
    check_mode (cod_mod mu m) m;
    begin
      match tp with
      | D.Tymod (nu, tp1) ->
        check_mod mu nu "mod";
        let new_env = M nu :: env in
        let new_mode = dom_mod nu m in
        check ~env:new_env ~size ~term:tm ~tp:tp1 ~m:new_mode;
      | _ -> tp_error (Misc ("Expected Modal Type but found \n" ^ D.pp tp))
    end
  | Id (tp', l, r) ->
    begin
      match tp with
      | D.Uni _ ->
        check ~env ~size ~term:tp' ~tp ~m;
        let tp' = Nbe.eval tp' (env_to_sem_env env) in
        check ~env ~size ~term:l ~tp:tp' ~m;
        check ~env ~size ~term:r ~tp:tp' ~m
      | t -> tp_error (Expecting_universe t)
    end
  | Refl term ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        check ~env ~size ~term ~tp ~m;
        let term = Nbe.eval term (env_to_sem_env env) in
        assert_equal m size term left tp;
        assert_equal m size term right tp
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.pp t))
    end
  | term -> assert_subtype m size (synth ~env ~size ~term ~m) tp;

and synth ~env ~size ~term ~m =
  match term with
  | Syn.Var id ->
    let (mu, tp, md) = get_var env id in
    let locks = nth_cell env id in
    (*  Verify whether the toplevel definitions are used at the correct 0-cell,
        (we also check terms, but they should be fine anyways)
     *  It also validates that mu has the correct boundary, since we only allow entries where md is the domain of mu *)
    check_mode md m;
    begin
      match mu with
      | Some mu ->
        begin
          (* Verify whether a cell exists that allows us to access the variable*)
          check_cell mu locks;
        end
      | None -> ()
    end;
    tp
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def ~m in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    synth ~env:(add_term ~md:m ~term:def_val ~mu:idm ~tp:def_tp env) ~size:(size + 1) ~term:body ~m
  | Syn.Check (term, tp') ->
    let tp = Nbe.eval tp' (env_to_sem_env env) in
    check ~env ~size ~term ~tp ~m;
    tp
  | Syn.Zero -> D.Nat
  | Syn.Suc term -> check ~env ~size ~term ~tp:Nat ~m; D.Nat
  | Syn.Fst p ->
    begin
      match (synth ~env ~size ~term:p ~m) with
      | Sig (left_tp, _) -> left_tp
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.pp t))
    end
  | Syn.Snd p ->
    begin
      match (synth ~env ~size ~term:p ~m) with
      | Sig (_, right_tp) ->
        let proj = Nbe.eval (Fst p) (env_to_sem_env env) in
        Nbe.do_clos right_tp proj
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.pp t))
    end
  | Syn.Ap (mu, f, a) ->
    begin
      check_mode (cod_mod mu m) m;
      match (synth ~env ~size ~term:f ~m) with
      | D.Pi (nu , src , dest) ->
        check_mod mu nu "ap";
        let new_env = (M mu :: env) in
        let new_mode = dom_mod mu m in
        check ~env:new_env ~size ~term:a ~tp:src ~m:new_mode;
        let a_sem = Nbe.eval a (env_to_sem_env new_env) in
        Nbe.do_clos dest a_sem
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.pp t))
    end
  | Syn.NRec (mot, zero, suc, n) ->
    check ~env ~size ~term:n ~tp:Nat ~m;
    let var = D.mk_var Nat size in
    check_tp ~env:(add_term ~md:m ~term:var ~mu:idm ~tp:Nat env) ~size:(size + 1) ~term:mot ~m;
    let sem_env = env_to_sem_env env in
    let zero_tp = Nbe.eval mot ((D.Val Zero) :: sem_env) in
    let ih_tp = Nbe.eval mot ((D.Val var) :: sem_env) in
    let ih_var = D.mk_var ih_tp (size + 1) in
    let suc_tp = Nbe.eval mot (Val (Suc var) :: sem_env) in
    check ~env ~size ~term:zero ~tp:zero_tp ~m;
    check
      ~env:(add_term ~md:m ~term:var ~mu:idm ~tp:Nat env |> add_term ~md:m ~term:ih_var ~mu:idm ~tp:ih_tp)
      ~size:(size + 2)
      ~term:suc
      ~tp:suc_tp
      ~m ;
    Nbe.eval mot (Val (Nbe.eval n sem_env) :: sem_env)
  | Syn.Letmod (mu, nu, mot, deptm, tm) ->
    begin
      let cod_mu = m in
      let dom_mu = dom_mod mu m in
      check_mode cod_mu m;
      let new_env = M mu :: env in
      let new_mode = dom_mu in
      match (synth ~env:new_env ~size ~term:tm ~m:new_mode) with
      | D.Tymod (nu1, tp) ->
        check_mod nu nu1 "letmod";
        let new_head = Term {term = D.mk_var (D.Tymod (nu1, tp)) size; mu = mu; tp = D.Tymod (nu1, tp); md = new_mode} in
        let mot_env = new_head :: env in
        check_tp ~env:mot_env ~size:(size + 1) ~term:mot ~m;
        let deptm_env = Term {term = D.mk_var tp size; mu = compm (mu, nu1); tp = tp; md = dom_mod (compm (mu, nu1)) m} :: env in
        let base_sem_env = env_to_sem_env env in
        let sem_env =  D.Val (D.Mod (nu1, D.mk_var tp size)) :: base_sem_env in
        let sem_deptm_ty = Nbe.eval mot sem_env in
        check ~env:deptm_env ~size:(size + 1) ~term:deptm ~tp:sem_deptm_ty ~m;
        let final_tp_env = D.Val (Nbe.eval tm base_sem_env) :: base_sem_env in
        Nbe.eval mot final_tp_env
      | t -> tp_error (Misc ("Expecting Modal Type but found \n" ^ D.pp t))
    end
  | Syn.J (mot, refl, eq) ->
    let eq_tp = synth ~env ~size ~term:eq ~m in
    begin
      let sem_env = env_to_sem_env env in
      match eq_tp with
      | D.Id (tp', left, right) ->
        let mot_var1 = D.mk_var tp' size in
        let mot_var2 = D.mk_var tp' (size + 1) in
        let mot_var3 = D.mk_var (D.Id (tp', mot_var1, mot_var2)) (size + 1) in
        let mot_env =
          add_term ~md:m ~term:mot_var1 ~mu:idm ~tp:tp' env
          |> add_term ~md:m ~term:mot_var2 ~mu:idm ~tp:tp'
          |> add_term ~md:m ~term:mot_var3 ~mu:idm ~tp:(D.Id (tp', mot_var1, mot_var2)) in
        check_tp ~env:mot_env ~size:(size + 3) ~term:mot ~m;
        let refl_var = D.mk_var tp' size in
        let refl_tp = Nbe.eval mot (D.Val (D.Refl refl_var) :: D.Val refl_var :: D.Val refl_var :: sem_env) in
        check ~env:(add_term ~md:m ~term:refl_var ~mu:idm ~tp:tp' env) ~size:(size + 1) ~term:refl ~tp:refl_tp ~m;
        Nbe.eval mot (D.Val (Nbe.eval eq sem_env) :: D.Val right :: D.Val left :: sem_env)
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.pp t))
    end
  | Syn.Axiom (_, tp) -> Nbe.eval tp (env_to_sem_env env)
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~env ~size ~term ~m =
  match term with
  | Syn.Nat -> ()
  | Syn.Uni _ -> ()
  | Syn.Pi (mu, src, dest) ->
    check_mode (cod_mod mu m) m;
    let new_env = M mu :: env in
    let new_mode = dom_mod mu m in
    check_tp ~env:new_env ~size ~term:src ~m:new_mode;
    let l_sem = Nbe.eval src (env_to_sem_env new_env) in
    let var = D.mk_var l_sem size in
    check_tp ~env:(add_term ~md:new_mode ~term:var ~mu:mu ~tp:l_sem env) ~size:(size + 1) ~term:dest ~m
  | Syn.Sig (l, r) -> check_tp ~env ~size ~term:l ~m;
    let l_sem = Nbe.eval l (env_to_sem_env env) in
    let var = D.mk_var l_sem size in
    check_tp ~env:(add_term ~md:m ~term:var ~mu:idm ~tp:l_sem env) ~size:(size + 1) ~term:r ~m
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def ~m in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    check_tp ~env:(add_term ~md:m ~term:def_val ~mu:idm ~tp:def_tp env) ~size:(size + 1) ~term:body ~m
  | Syn.TyMod (mu, tp) ->
    check_mode (cod_mod mu m) m;
    let new_env = M mu :: env in
    let new_mode = dom_mod mu m in
    check_tp ~env:new_env ~size ~term:tp ~m:new_mode;
  | Syn.Id (tp, l, r) ->
    check_tp ~env ~size ~term:tp ~m;
    let tp = Nbe.eval tp (env_to_sem_env env) in
    check ~env ~size ~term:l ~tp ~m;
    check ~env ~size ~term:r ~tp ~m
  | term ->
    begin
      match (synth ~env ~size ~term ~m) with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
