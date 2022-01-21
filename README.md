### This is the version that only permits pre-order mode theories ###
A pre-order mode theory is a mode theory, that has at most one 2-cell between any pair of 1-cells.

## mitten
An implementation of MTT with modal dependent products (pi), modal types, dependent sums (sigma),
natural numbers, and a cumulative hierarchy. This implementation correctly handles eta for both pi
and sigma.

This implementation has also been extended to include a type checker based on Coquand's semantic
type checker. In order to interact with the normalizer, therefore, one can write a file containing a
list of definitions and commands to normalize various terms.

## Prerequisites 
Tested under ocaml 4.07.1 and dune 2.8.5. Sexplib, menhir, ppx_compare and cmdliner libraries need to be installed.

## How to use it
Building mitten with "make build" or "dune build". Execute mitten with "dune exec mitten PATH/TO/FILE" or "_build/install/default/bin/mitten PATH/TO/FILE". 
If there is no output, everything type checked. The commands "normalize" and "normalize def" print the normalized term to std_out.

## For example:

```
let plus : (x : {idm | Nat}) -> (y : {idm | Nat}) -> Nat @ s =
    fun m ->
    fun n ->
    rec n at x -> Nat with
    | zero -> m
    | suc _, p -> suc p

normalize plus {idm, 2} {idm, 2} at Nat @ s

let fib : (x : {idm | Nat}) -> Nat @ s =
    fun n ->
    let worker : Nat * Nat =
      rec n at _ -> Nat * Nat with
      | zero -> pair (1, 0)
      | suc _, p -> pair (plus {idm, (fst p)} {idm, (snd p)}, fst p) in
    snd worker

normalize fib {idm, 25} at Nat @ s
```

A list of other examples may be found in `test/`.

The implementation is derived from [nbe-for-mltt](https://github.com/jozefg/nbe-for-mltt).
