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
  ("truething", Some (identifier_fix "truething")),

  (* Booleans *)

  ("true", Some (literal_bool_fix true)),
  ("false", Some (literal_bool_fix false)),

  (* Strings *)

  ("\"The quick brown fox jumps over the lazy dog.\"", Some (string_cons_fix ("The quick brown fox jumps over the lazy dog.", []))),
  ("\"The quick $color fox $(act)s over the lazy dog.\"", Some (string_cons_fix ("The quick ", [(identifier_fix "color", " fox "), (identifier_fix "act", "s over the lazy dog.")]))),
  ("\"The \\\"quick\\\" brown fox jumps over the \\\\azy dog.\"", Some (string_cons_fix ("The \"quick\" brown fox jumps over the \\azy dog.", []))),

  (* Lists *)

  ("[a,b,c]", Some (list_cons_fix [identifier_fix "a", identifier_fix "b", identifier_fix "c"])),
  ("[ a, b, c ]", Some (list_cons_fix [identifier_fix "a", identifier_fix "b", identifier_fix "c"])),

  (* Records *)

  ("{a=b,c=d,e=f}", Some (record_cons_fix [(identifier_fix "a", identifier_fix "b"), (identifier_fix "c", identifier_fix "d"), (identifier_fix "e", identifier_fix "f")])),
  ("{ a=b, c = d, e= f }", Some (record_cons_fix [(identifier_fix "a", identifier_fix "b"), (identifier_fix "c", identifier_fix "d"), (identifier_fix "e", identifier_fix "f")])),

  ("{ foo(a, b, c) = bar, \"ponies\" = \"cute\", (flopnax) = ropjar }", Some (record_cons_fix [(identifier_fix "foo", abstraction_fix (["a", "b", "c"], identifier_fix "bar")), (string_cons_fix ("ponies", []), string_cons_fix ("cute", [])), (identifier_fix "flopnax", identifier_fix "ropjar")])),

  (* Function application *)

  ("foo()", Some (application_fix (identifier_fix "foo", []))),
  ("foo(a, b, c)", Some (application_fix (identifier_fix "foo", [Some (identifier_fix "a"), Some (identifier_fix "b"), Some (identifier_fix "c")]))),
  ("foo (a,b,c)", Some (application_fix (identifier_fix "foo", [Some (identifier_fix "a"), Some (identifier_fix "b"), Some (identifier_fix "c")]))),
  ("foo(a, _, c)", Some (application_fix (identifier_fix "foo", [Some (identifier_fix "a"), None, Some (identifier_fix "c")]))),

  (* Anonymous functions / Lambdas / Abstractions *)

  ("fun(a, b, c) = body", Some (abstraction_fix (["a", "b", "c"], identifier_fix "body"))),
  ("fun (a ,b, c )=body", Some (abstraction_fix (["a", "b", "c"], identifier_fix "body"))),

  (* Let expressions *)

  ("let name=expr in body", Some (let_binding_fix ("name", identifier_fix "expr", identifier_fix "body"))),
  ("let name = expr in body", Some (let_binding_fix ("name", identifier_fix "expr", identifier_fix "body"))),
  (*("let rec name = expr in body", Some (ExprLet (LetRec, LetSimple ("name", ExprId "expr"), ExprId "body"))),*)
  ("let foo(a, b, c) = foocode in body", Some (let_binding_fix ("foo", abstraction_fix (["a", "b", "c"], identifier_fix "foocode"), identifier_fix "body"))),

  ("letname = expr in body", None),
  ("let name = expr inbody", None),

  (* Typed holes *)

  ("$?help", Some (hole_fix "help")),

  (* TODO: other tests (depends on the parsers) *)

  ("intentionally_failing_test", None)
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

let _ = run_tests (parser, parser_tests)
