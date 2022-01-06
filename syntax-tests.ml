open import "prelude.ml"
open import "./parsing/lpeg.ml"
open import "./syntax.ml"

(* TESTS *)
(* (test, expected result) pairs.
 * Each section may be divided into 3 parts:
 *   tests that should succeed;
 *   tests that should fail;
 *   tests that succeed but are questionable.
 * In some cases the last part is meant to highlight ambiguities in Open's description
 *)
let parser_tests = [
  (* Basic identifiers *)

  ("list", Some (identifier_fix "list")),
  ("sum", Some (identifier_fix "sum")),
  ("foldl", Some (identifier_fix "foldl")),
  ("this_is_a_s1lly_but_v4l1d_identifier", Some (identifier_fix "this_is_a_s1lly_but_v4l1d_identifier")),

  ("_", None),
  ("++", None),
  ("_internal", None),

  ("x___", Some (identifier_fix "x___")),
  ("iCons", Some (identifier_fix "iCons")),
  ("e", Some (identifier_fix "e")),

  (* Lists *)

  ("[a,b,c]", Some (list_cons_fix [identifier_fix "a", identifier_fix "b", identifier_fix "c"])),
  ("[ a, b, c ]", Some (list_cons_fix [identifier_fix "a", identifier_fix "b", identifier_fix "c"])),

  (* Records *)

  ("{a=b,c=d,e=f}", Some (record_cons_fix [(identifier_fix "a", identifier_fix "b"), (identifier_fix "c", identifier_fix "d"), (identifier_fix "e", identifier_fix "f")])),
  ("{ a=b, c = d, e= f }", Some (record_cons_fix [(identifier_fix "a", identifier_fix "b"), (identifier_fix "c", identifier_fix "d"), (identifier_fix "e", identifier_fix "f")])),

  (* Function application *)

  ("foo()", Some (application_fix (identifier_fix "foo", []))),
  ("foo(a, b, c)", Some (application_fix (identifier_fix "foo", [identifier_fix "a", identifier_fix "b", identifier_fix "c"]))),
  ("foo (a,b,c)", Some (application_fix (identifier_fix "foo", [identifier_fix "a", identifier_fix "b", identifier_fix "c"]))),

  (* Anonymous functions / Lambdas / Abstractions *)

  ("fun(a, b, c) = body", Some (abstraction_fix (["a", "b", "c"], identifier_fix "body"))),

  (* Let expressions *)

  ("let name=expr in body", Some (let_binding_fix ("name", identifier_fix "expr", identifier_fix "body"))),
  ("let name = expr in body", Some (let_binding_fix ("name", identifier_fix "expr", identifier_fix "body")))
  (* don't forget the comma at the end of the previous line *)
  (*("let rec name = expr in body", Some (ExprLet (LetRec, LetSimple ("name", ExprId "expr"), ExprId "body"))),*)
  (*("let foo(a, b, c) = foocode in body", Some (ExprLet (Let, LetFunction ("foo", ["a", "b", "c"], ExprId "foocode"), ExprId "body")))*)

  (* TODO: other tests (depends on the parsers) *)
]

let parser_test parser (test, expected) =
  let got = parse (parser `seq` eof) test
  (* TODO: figure out how to impl eq for term, to fix this hack *)
  (* ideally impl show as well, showterm doesn't quite show the ast *)
  let sexp = showterm <$> expected
  let sgot = showterm <$> got
  in (sexp == sgot, test, sexp, sgot)

let filter_failing results = filter (fun (success, _) -> not success) results

let run_tests (parser, tests) =
  let results = parser_test parser <$> tests
  let fails = filter_failing results
  in map print fails

let _ = run_tests (parser (), parser_tests)
