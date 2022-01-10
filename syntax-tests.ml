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
 * They are split into multiple lists because of Lua limitations
 *)

(* TODO: quick-test format (test1, test2) pairs
 * where test2 is parenthesized in a way that makes parsing obvious *)

let identifier_tests = [
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
  ("truething", Some (identifier_fix "truething"))
]

let boolean_tests: list (string * option pterm) = [
  ("true", Some (literal_bool_fix true)),
  ("false", Some (literal_bool_fix false))
]

let string_tests = [
  ("\"The quick brown fox jumps over the lazy dog.\"", Some (string_cons_fix ("The quick brown fox jumps over the lazy dog.", []))),
  ("\"The quick $color fox $(act)s over the lazy dog.\"", Some (string_cons_fix ("The quick ", [(identifier_fix "color", " fox "), (identifier_fix "act", "s over the lazy dog.")]))),
  ("\"The \\\"quick\\\" brown fox jumps over the \\\\azy dog.\"", Some (string_cons_fix ("The \"quick\" brown fox jumps over the \\azy dog.", [])))
]

let list_tests = [
  ("[a,b,c]", Some (list_cons_fix [identifier_fix "a", identifier_fix "b", identifier_fix "c"])),
  ("[ a, b, c ]", Some (list_cons_fix [identifier_fix "a", identifier_fix "b", identifier_fix "c"]))
]

let record_tests = [
  ("{a=b,c=d,e=f}", Some (record_cons_fix [(identifier_fix "a", identifier_fix "b"), (identifier_fix "c", identifier_fix "d"), (identifier_fix "e", identifier_fix "f")])),
  ("{ a=b, c = d, e= f }", Some (record_cons_fix [(identifier_fix "a", identifier_fix "b"), (identifier_fix "c", identifier_fix "d"), (identifier_fix "e", identifier_fix "f")])),

  ("{ foo(a, b, c) = bar, \"ponies\" = \"cute\", (flopnax) = ropjar }", Some (record_cons_fix [(identifier_fix "foo", abstraction_fix (["a", "b", "c"], identifier_fix "bar")), (string_cons_fix ("ponies", []), string_cons_fix ("cute", [])), (identifier_fix "flopnax", identifier_fix "ropjar")]))
]

let application_tests = [
  ("foo()", Some (application_fix (identifier_fix "foo", []))),
  ("foo(a, b, c)", Some (application_fix (identifier_fix "foo", [Some (identifier_fix "a"), Some (identifier_fix "b"), Some (identifier_fix "c")]))),
  ("foo (a,b,c)", Some (application_fix (identifier_fix "foo", [Some (identifier_fix "a"), Some (identifier_fix "b"), Some (identifier_fix "c")]))),
  ("foo(a, _, c)", Some (application_fix (identifier_fix "foo", [Some (identifier_fix "a"), None, Some (identifier_fix "c")]))),
  ("foo(a)(_)(c)", Some (application_fix ((application_fix ((application_fix (identifier_fix "foo", [Some (identifier_fix "a")])), [None])), [Some (identifier_fix "c")])))
]

let infix_op_tests = [
  ("foo + bar", Some (infix_op_fix (Some (identifier_fix "foo"), "+", Some (identifier_fix "bar")))),
  ("one-to-one", Some (infix_op_fix (Some (infix_op_fix (Some (identifier_fix "one"), "-", Some (identifier_fix "to"))), "-", Some (identifier_fix "one")))),
  ("_ ^ \"n't\"", Some (infix_op_fix (None, "^", Some (string_cons_fix ("n't", []))))),
  ("+a+b+c+", Some (infix_op_fix (Some (infix_op_fix (Some (prefix_op_fix ("+", Some (identifier_fix "a"))), "+", Some (identifier_fix "b"))), "+", Some (suffix_op_fix (Some (identifier_fix "c"), "+")))))
]

let prefix_op_tests = [
  ("#hashtag", Some (prefix_op_fix ("#", Some (identifier_fix "hashtag")))),
  ("-#foo", Some (prefix_op_fix ("-#", Some (identifier_fix "foo")))),
  ("-(#bar)", Some (prefix_op_fix ("-", Some (prefix_op_fix ("#", Some (identifier_fix "bar")))))),
  ("- #bar", Some (prefix_op_fix ("-", Some (prefix_op_fix ("#", Some (identifier_fix "bar")))))),
  ("-_", Some (prefix_op_fix ("-", None))),
  ("-+- sparkle -+-", Some (prefix_op_fix ("-+-", Some (suffix_op_fix (Some (identifier_fix "sparkle"), "-+-")))))
]

let suffix_op_tests = [
  ("c++", Some (suffix_op_fix (Some (identifier_fix "c"), "++"))),
  ("_ - +", Some (suffix_op_fix (Some (suffix_op_fix (None, "-")), "+")))
]

let abstraction_tests = [
  ("fun(a, b, c) = body", Some (abstraction_fix (["a", "b", "c"], identifier_fix "body"))),
  ("fun (a ,b, c )=body", Some (abstraction_fix (["a", "b", "c"], identifier_fix "body")))
]

let let_expression_tests = [
  ("let name=expr in body", Some (let_binding_fix ("name", identifier_fix "expr", identifier_fix "body"))),
  ("let name = expr in body", Some (let_binding_fix ("name", identifier_fix "expr", identifier_fix "body"))),
  ("let foo(a, b, c) = foocode in body", Some (let_binding_fix ("foo", abstraction_fix (["a", "b", "c"], identifier_fix "foocode"), identifier_fix "body"))),

  ("letname = expr in body", None),
  ("let name = expr inbody", None)
]

let let_rec_expression_tests = [
  ("let rec name = expr in body", Some (let_rec_binding_fix ("name", identifier_fix "expr", identifier_fix "body")))
]

let hole_tests = [
  ("$?help", Some (hole_fix "help"))
]

let misc_tests = [
  ("_", None)
]

(* TODO: other tests (depends on the parsers) *)

let parser_test parser (test, expected) =
  let got = parse (parser `seq` eof) test
  let dgot = parse parser test
  (* TODO: figure out how to impl eq for term, to fix this hack *)
  (* ideally impl show as well, showterm doesn't quite show the ast *)
  let sexp = showterm <$> expected
  let sgot = showterm <$> got
  let sdgot = showterm <$> dgot
  in (sexp == sgot, test, sexp, sgot, sdgot)

let filter_failing results = filter (fun (success, _) -> not success) results

let show_result (success, test, exp, got, debug) =
  "Success : " ^ show success ^ "\n"
  ^ "Test    : " ^ test ^ "\n"
  ^ "Expected: " ^ show exp ^ "\n"
  ^ "Got     : " ^ show got ^ "\n"
  ^ "Partial : " ^ show debug ^ "\n"

let run_tests (parser, tests) =
  let results = parser_test parser <$> tests
  let fails = filter_failing results
  in map (put_line % show_result) fails

let _ = run_tests (parser, identifier_tests)
let _ = run_tests (parser, boolean_tests)
let _ = run_tests (parser, string_tests)
let _ = run_tests (parser, list_tests)
let _ = run_tests (parser, record_tests)
let _ = run_tests (parser, application_tests)
let _ = run_tests (parser, infix_op_tests)
let _ = run_tests (parser, prefix_op_tests)
let _ = run_tests (parser, suffix_op_tests)
let _ = run_tests (parser, abstraction_tests)
let _ = run_tests (parser, let_expression_tests)
let _ = run_tests (parser, let_rec_expression_tests)
let _ = run_tests (parser, hole_tests)
let _ = run_tests (parser, misc_tests)
