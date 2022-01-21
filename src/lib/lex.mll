{
open Lexing
open Grammar

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

let make_table num elems =
  let table = Hashtbl.create num in
  List.iter (fun (k, v) -> Hashtbl.add table k v) elems;
  table

let keywords =
  make_table 0 [
    ("zero", ZERO);
    ("suc", SUC);
    ("Nat", NAT);
    ("let", LET);
    ("in", IN);
    ("with", WITH);
    ("rec", REC);
    ("pair", PAIR);
    ("fst", FST);
    ("snd", SND);
    ("fun", LAM);
    ("letmod", LETMOD);
    ("mod", MOD);
    ("idm", IDM);
    ("match", MATCH);
    ("Id", ID);
    ("refl", REFL);
    ("U", UNIV);
    ("def", DEF);
    ("at", AT);
    ("normalize", NORMALIZE);
    ("quit", QUIT);
    ("axiom", AXIOM);
  ]
}

let number = ['0'-'9']['0'-'9']*
let whitespace = [' ' '\t']+
let line_ending = '\r' | '\n' | "\r\n"
let atom_first = ['a'-'z' 'A'-'Z' '_']
let atom_next = ['a'-'z' 'A'-'Z' '_' '-' '*' '/' '0'-'9']
let atom = atom_first atom_next*

rule token = parse
  | number
    { (NUMERAL (int_of_string (Lexing.lexeme lexbuf))) }
  | ';'
    {comment lexbuf}
  | '{'
    { LBRACE }
  | '}'
    { RBRACE }
  | '('
    { LPR }
  | ')'
    { RPR }
  | '['
    { LBR }
  | ']'
    { RBR }
  | '|'
    { PIPE }
  | ','
    { COMMA }
  | '.'
    { POINT }
  | '*'
    { TIMES }
  | ':'
    { COLON }
  | "="
    { EQUALS }
  | "->"
    { RIGHT_ARROW }
  | "<-"
    { LEFT_ARROW }
  | "<"
    { LANGLE }
  | ">"
    { RANGLE }
  | "λ"
    { LAM }
  | "@"
    { ATSIGN }
  | '_'
    { UNDERSCORE }
  | line_ending
    { new_line lexbuf; token lexbuf }
  | whitespace
    { token lexbuf }
  | eof
    { EOF }
  | atom
    {
      let input = lexeme lexbuf in
      begin try
        let kwd = Hashtbl.find keywords input in
        kwd
      with Not_found ->
        (Grammar.ATOM input)
      end
    }
  | _
    { Printf.eprintf "Unexpected char: %s" (lexeme lexbuf); token lexbuf }
and comment = parse
  | line_ending
    { new_line lexbuf; token lexbuf }
  | _
    { comment lexbuf }
