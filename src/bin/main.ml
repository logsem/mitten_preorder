open Normalizer
open Cmdliner

let perform_norm input = Load.load_file input |> Driver.process_sign

let main input =
  try perform_norm input; 0 with
  | Invalid_argument s -> Printf.eprintf "Internal error (invalid argument): %s\n" s; 1
  | Failure s -> Printf.eprintf "Internal error (Failure): %s\n" s; 1
  | Load.Parse_error s -> Printf.eprintf "Frontend error: %s\n" s; 1
  | Nbe.Nbe_failed s -> Printf.eprintf "Internal error (Failed to normalize): %s\n" s; 1
  | Check.Type_error e -> Printf.eprintf "Type error\n%s\n" (Check.pp_error e); 1
  | Syntax.Illformed -> Printf.eprintf "Syntax error.\n"; 1
  | Mode_theory.Modality_error str -> Printf.eprintf "Modality error: %s\n" str; 1

let input_file =
  let doc = "File containing the term to reduce" in
  Arg.(value & pos 0 file "" & info [] ~docv:"input file" ~doc)

let info =
  let doc = "Typecheck and normalize terms in MTT" in
  let err_exit = Cmd.Exit.info ~doc:"on an ill-formed or terms." 1 in
  Cmd.info "mitten" ~version:"0.0" ~doc ~exits:(err_exit :: Cmd.Exit.defaults)

let () =
  let t = Term.(const main $ input_file) in
  exit @@ Cmd.eval' @@ Cmd.v info t
