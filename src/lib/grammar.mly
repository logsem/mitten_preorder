%{
  open Concrete_syntax
%}

%token <int> NUMERAL
%token <string> ATOM
%token COLON PIPE AT COMMA RIGHT_ARROW LEFT_ARROW UNDERSCORE POINT
%token LPR RPR LBR RBR LANGLE RANGLE LBRACE RBRACE ATSIGN
%token EQUALS
%token TIMES FST SND PAIR
%token LAM LET IN WITH DEF
%token REC SUC NAT ZERO
%token MOD LETMOD IDM
%token ID REFL MATCH
%token UNIV
%token QUIT NORMALIZE
%token EOF
%token AXIOM

%start <Concrete_syntax.signature> sign
%%

name:
  | s = ATOM
    { s }
  | UNDERSCORE
    { "_" }

decl:
  | LET; nm = name; COLON; tp = term; ATSIGN; md = mode; EQUALS; body = term
    { Def {name = nm; def = body; tp; md} }
  | QUIT { Quit }
  | NORMALIZE; DEF; a = name
    { NormalizeDef a  }
  | NORMALIZE; tm = term; AT; tp = term; ATSIGN; md = mode
    { NormalizeTerm {term = tm; tp; md} }
  | AXIOM; nm = name; COLON; tp = term; ATSIGN; md = mode
    { Axiom {name = nm; tp; md} }
;

sign:
  | EOF { [] }
  | d = decl; s = sign { d :: s };

atomic:
  | LPR; t = term; RPR
    { t }
  | LBR; t = term; AT; tp = term RBR
    { Check {term = t; tp} }
  | a = name
    { Var a }
  | ZERO
    { Lit 0 }
  | n = NUMERAL
    { Lit n }
  | UNIV; LANGLE; i = NUMERAL; RANGLE
    { Uni i }
  | NAT { Nat }
  | PAIR; LPR; left = term; COMMA; right = term; RPR
    { Pair (left, right) }
  | LANGLE; LANGLE; mu = modality; PIPE; tm = term; RANGLE; RANGLE
    {TyMod (mu, tm)}
;

spine:
  | LBRACE; mu = modality; COMMA; tm = term; RBRACE
    {mu, tm}
  | t = atomic
    {[], t}
;

term:
  | f = atomic; args = list(spine)
    { Ap (f, args) }
  | LET; name = name; COLON; tp = term; EQUALS; def = term; IN; body = term
    { Let (Check {term = def; tp}, Binder {name; body}) }
  | LET; name = name; EQUALS; def = term; IN; body = term
    { Let (def, Binder {name; body}) }
  | LPR t = term; AT; tp = term RPR
    { Check {term = t; tp} }
  | SUC; t = term { Suc t }
  | REC; n = term; AT; mot_name = name; RIGHT_ARROW; mot = term; WITH;
    PIPE; ZERO; RIGHT_ARROW; zero_case = term;
    PIPE; SUC; suc_var = name; COMMA; ih_var = name; RIGHT_ARROW; suc_case = term
    { NRec {
        mot = Binder {name = mot_name; body = mot};
        zero = zero_case;
        suc = Binder2 {name1 = suc_var; name2 = ih_var; body = suc_case};
        nat = n
      } }
  | MATCH; eq = term; AT; name1 = name; name2 = name; name3 = name; RIGHT_ARROW; mot_term = term; WITH
    PIPE; REFL; name = name; RIGHT_ARROW; refl = term;
    { J {mot = Binder3 {name1; name2; name3; body = mot_term}; refl = Binder {name; body = refl}; eq} }
  | ID; tp = atomic; left = atomic; right = atomic
    { Id (tp, left, right) }
  | REFL; t = atomic
    { Refl t }
  | LAM; names = nonempty_list(name); RIGHT_ARROW; body = term
    { Lam (BinderN {names; body}) }
  | LPR; name = name; COLON; LBRACE; mu = modality; PIPE; dom = term; RBRACE; RPR RIGHT_ARROW; cod = term
    { Pi (mu, dom, Binder {name; body = cod}) }
  | LBRACE; mu = modality; PIPE; dom = term; RBRACE; RIGHT_ARROW; cod = term
    { Pi (mu, dom, Binder {name = ""; body = cod}) }
  | LPR; name = name; COLON; dom = term; RPR; RIGHT_ARROW; cod = term
    { Pi ([], dom, Binder {name; body = cod}) }
  | dom = atomic; RIGHT_ARROW; cod = term
    { Pi ([], dom, Binder {name = ""; body = cod}) }
  | LPR name = name; COLON; left = term; RPR; TIMES; right = term
    { Sig (left, Binder {name; body = right}) }
  | left = atomic; TIMES; right = term
    { Sig (left, Binder {name = ""; body = right}) }
  | FST; t = term { Fst t }
  | SND; t = term { Snd t }
  | LETMOD; mu = modality; LPR; LAM; name_tp = name; RIGHT_ARROW; tp = term; RPR; MOD; nu = modality; LPR; name_tm = name; RPR; LEFT_ARROW; tm1 = term; IN; tm2 = term
    {Letmod (mu, nu, Binder {name = name_tp; body = tp}, Binder {name = name_tm; body = tm2}, tm1)}
  | MOD; mu = modality; tm = term
    {Mod (mu, tm)}
;

mode:
  | s = name
    { s };

modality:
 | mod1 = atomic_modality; POINT; mod2 = modality
    {List.append mod2 mod1}
  | mu = atomic_modality
    {mu};

atomic_modality:
  | IDM
    { [] }
  | mu = name
    { [mu] }
  | LPR; mu = modality; RPR
    {mu};
