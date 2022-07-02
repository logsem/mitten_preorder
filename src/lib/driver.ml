module CS = Concrete_syntax
module S = Syntax
module D = Domain
module M = Mode_theory

type env = Env of {size : int; check_env : Check.env; bindings : string list}

let initial_env = Env {size = 0; check_env = []; bindings = []}

type output =
    NoOutput of env
  | NF_term of S.t * S.t
  | NF_def of CS.ident * S.t
  | Quit

let update_env env = function
  | NoOutput env -> env
  | NF_term _ | NF_def _ | Quit -> env

let output (Env {bindings; _}) = function
  | NoOutput _ -> ()
  | NF_term (s, t) ->
    let open Sexplib in
    let s_rep =
      Syntax.to_sexp (List.map (fun x -> Sexp.Atom x) bindings) s
      |> Sexp.to_string_hum in
    Printf.printf "Computed normal form of\n  %s\nas\n  %s\n%!" s_rep (S.pp t)
  | NF_def (name, t) -> Printf.printf "Computed normal form of [%s]:\n  %s\n%!" name (S.pp t)
  | Quit -> exit 0

let find_idx key =
  let rec go i = function
    | [] -> raise (Check.Type_error (Check.Misc ("Unbound variable: " ^ key)))
    | x :: xs -> if String.equal x key then i else go (i + 1) xs in
  go 0

let rec int_to_term = function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

let rec unravel_spine f = function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs

let rec bind env = function
  | CS.Var i -> S.Var (find_idx i env)
  | CS.Let (tp, Binder {name; body}) ->
    S.Let (bind env tp, bind (name :: env) body)
  | CS.Check {term; tp} -> S.Check (bind env term, bind env tp)
  | CS.Nat -> S.Nat
  | CS.Suc t -> S.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec
      { mot = Binder {name = mot_name; body = mot_body};
        zero;
        suc = Binder2 {name1 = suc_name1; name2 = suc_name2; body = suc_body};
        nat} ->
    S.NRec
      (bind (mot_name :: env) mot_body,
       bind env zero,
       bind (suc_name2 :: suc_name1 :: env) suc_body,
       bind env nat)
  | CS.Pi (mu, src, Binder {name; body}) -> S.Pi (M.bind_m mu, bind env src, bind (name :: env) body)
  | CS.Lam (BinderN {names = []; body}) ->
    bind env body
  | CS.Lam (BinderN {names = x :: names; body}) ->
    let lam = CS.Lam (BinderN {names; body}) in
    S.Lam (bind (x :: env) lam)
  | CS.Ap (f, args) ->
    List.map (fun (mu, t) f -> S.Ap (M.bind_m mu, f, bind env t)) args |> unravel_spine (bind env f)
  | CS.Sig (tp, Binder {name; body}) ->
    S.Sig (bind env tp, bind (name :: env) body)
  | CS.Pair (l, r) -> S.Pair (bind env l, bind env r)
  | CS.Fst p -> S.Fst (bind env p)
  | CS.Snd p -> S.Snd (bind env p)
  | CS.J
      {mot = Binder3 {name1 = left; name2 = right; name3 = prf; body = mot_body};
       refl = Binder {name = refl_name; body = refl_body};
       eq} ->
    S.J
      (bind (prf :: right :: left :: env) mot_body,
       bind (refl_name :: env) refl_body,
       bind env eq)
  | CS.Id (tp, left, right) ->
    S.Id (bind env tp, bind env left, bind env right)
  | CS.Refl t -> S.Refl (bind env t)
  | CS.Uni i -> S.Uni i
  | CS.TyMod (mu, tp) -> S.TyMod (M.bind_m mu, bind env tp)
  | CS.Mod (mu, tp) -> S.Mod (M.bind_m mu, bind env tp)
  | CS.Letmod (mu, nu, Binder {name; body = tp}, Binder {name = mod_var; body}, def) ->
    S.Letmod (M.bind_m mu, M.bind_m nu, bind (name :: env) tp, bind (mod_var :: env) body, bind env def)

let process_decl (Env {size; check_env; bindings})  = function
  | CS.Def {name; def; tp; md} ->
    let bind_md = M.bind_mode md in
    let def = bind bindings def in
    let tp = bind bindings tp in
    Check.check_tp ~size ~env:check_env ~term:tp ~m:bind_md;
    let sem_env = Check.env_to_sem_env check_env in
    let sem_tp = Nbe.eval tp sem_env in
    Check.check ~size ~env:check_env ~term:def ~tp:sem_tp ~m:bind_md;
    let sem_def = Nbe.eval def sem_env in
    let new_entry = Check.TopLevel {term = sem_def; tp = sem_tp; md = bind_md} in
    NoOutput (Env {size = size + 1; check_env = new_entry :: check_env; bindings = name :: bindings })
  | CS.NormalizeDef name ->
    let err = Check.Type_error (Check.Misc ("Unbound variable: " ^ name)) in
    begin
      match List.nth check_env (find_idx name bindings) with
      | Check.TopLevel {term; tp; md = _} -> NF_def (name, Nbe.read_back_nf 0 (D.Normal {term; tp}))
      | _ -> raise err
      | exception Failure _ -> raise err
    end
  | CS.NormalizeTerm {term; tp; md} ->
    let bind_md = M.bind_mode md in
    let term = bind bindings term in
    let tp = bind bindings tp in
    Check.check_tp ~size ~env:check_env ~term:tp ~m:bind_md;
    let sem_env = Check.env_to_sem_env check_env in
    let sem_tp = Nbe.eval tp sem_env in
    Check.check ~size ~env:check_env ~term ~tp:sem_tp ~m:bind_md;
    let sem_term = Nbe.eval term sem_env in
    let norm_term = Nbe.read_back_nf 0 (D.Normal {term = sem_term; tp = sem_tp}) in
    NF_term (term, norm_term)
  | CS.Axiom {name; tp; md} ->
    let bound_md = M.bind_mode md in
    let tp = bind bindings tp in
    Check.check_tp ~size ~env:check_env ~term:tp ~m:bound_md;
    let sem_env = Check.env_to_sem_env check_env in
    let sem_tp = Nbe.eval tp sem_env in
    let new_entry = Check.TopLevel {term = D.Neutral {tp = sem_tp; term = D.Axiom (name, sem_tp)}; tp = sem_tp; md = bound_md} in
    NoOutput (Env {size = size + 1; check_env = new_entry :: check_env; bindings = name :: bindings })
  | CS.Quit -> Quit

let rec process_sign ?env = function
  | [] -> ()
  | d :: ds ->
    let env = match env with
        None -> initial_env
      | Some e -> e in
    let o = process_decl env d in
    output env o;
    process_sign ?env:(Some (update_env env o)) ds
