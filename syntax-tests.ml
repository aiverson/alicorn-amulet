open import "prelude.ml"
open import "./arg.ml"
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
  ("list", Some (identifier_basic_fix "list")),
  ("sum", Some (identifier_basic_fix "sum")),
  ("foldl", Some (identifier_basic_fix "foldl")),
  ("this_is_a_s1lly_but_v4l1d_identifier", Some (identifier_basic_fix "this_is_a_s1lly_but_v4l1d_identifier")),

  ("_", None),
  ("++", None),
  ("_internal", None),

  ("x___", Some (identifier_basic_fix "x___")),
  ("iCons", Some (identifier_basic_fix "iCons")),
  ("e", Some (identifier_basic_fix "e")),
  ("truething", Some (identifier_basic_fix "truething"))
]

let boolean_tests: list (string * option pterm) = [
  ("true", Some (literal_bool_fix true)),
  ("false", Some (literal_bool_fix false))
]

let string_tests = [
  ("\"The quick brown fox jumps over the lazy dog.\"", Some (string_cons_fix ("The quick brown fox jumps over the lazy dog.", []))),
  ("\"The quick $color fox $(act)s over the lazy dog.\"", Some (string_cons_fix ("The quick ", [(identifier_basic_fix "color", " fox "), (identifier_basic_fix "act", "s over the lazy dog.")]))),
  ("\"The \\\"quick\\\" brown fox jumps over the \\\\azy dog.\"", Some (string_cons_fix ("The \"quick\" brown fox jumps over the \\azy dog.", [])))
]

let list_tests = [
  ("[a,b,c]", Some (list_cons_fix [identifier_basic_fix "a", identifier_basic_fix "b", identifier_basic_fix "c"])),
  ("[ a, b, c ]", Some (list_cons_fix [identifier_basic_fix "a", identifier_basic_fix "b", identifier_basic_fix "c"]))
]

let record_tests = [
  ("{a=b,c=d,e=f}", Some (record_cons_fix [(identifier_basic_fix "a", identifier_basic_fix "b"), (identifier_basic_fix "c", identifier_basic_fix "d"), (identifier_basic_fix "e", identifier_basic_fix "f")])),
  ("{ a=b, c = d, e= f }", Some (record_cons_fix [(identifier_basic_fix "a", identifier_basic_fix "b"), (identifier_basic_fix "c", identifier_basic_fix "d"), (identifier_basic_fix "e", identifier_basic_fix "f")])),

  ("{ foo(a, b, c) = bar, \"ponies\" = \"cute\", (flopnax) = ropjar }", Some (record_cons_fix [(identifier_basic_fix "foo", abstraction_fix (["a", "b", "c"], identifier_basic_fix "bar")), (string_cons_fix ("ponies", []), string_cons_fix ("cute", [])), (identifier_basic_fix "flopnax", identifier_basic_fix "ropjar")]))
]

let application_tests = [
  ("foo()", Some (application_fix (identifier_basic_fix "foo", []))),
  ("foo(a, b, c)", Some (application_fix (identifier_basic_fix "foo", [Some (identifier_basic_fix "a"), Some (identifier_basic_fix "b"), Some (identifier_basic_fix "c")]))),
  ("foo (a,b,c)", Some (application_fix (identifier_basic_fix "foo", [Some (identifier_basic_fix "a"), Some (identifier_basic_fix "b"), Some (identifier_basic_fix "c")]))),
  ("foo(a, _, c)", Some (application_fix (identifier_basic_fix "foo", [Some (identifier_basic_fix "a"), None, Some (identifier_basic_fix "c")]))),
  ("foo(a)(_)(c)", Some (application_fix ((application_fix ((application_fix (identifier_basic_fix "foo", [Some (identifier_basic_fix "a")])), [None])), [Some (identifier_basic_fix "c")])))
]

let infix_op_tests = [
  ("foo + bar", Some (application_fix (identifier_infix_fix "+", [Some (identifier_basic_fix "foo"), Some (identifier_basic_fix "bar")]))),
  ("one-to-one", Some (application_fix (identifier_infix_fix "-", [Some (application_fix (identifier_infix_fix "-", [Some (identifier_basic_fix "one"), Some (identifier_basic_fix "to")])), Some (identifier_basic_fix "one")]))),
  ("_ ^ \"n't\"", Some (application_fix (identifier_infix_fix "^", [None, Some (string_cons_fix ("n't", []))]))),
  ("+a+b+c+", Some (application_fix (identifier_infix_fix "+", [Some (application_fix (identifier_infix_fix "+", [Some (application_fix (identifier_prefix_fix "+", [Some (identifier_basic_fix "a")])), Some (identifier_basic_fix "b")])), Some (application_fix (identifier_suffix_fix "+", [Some (identifier_basic_fix "c")]))])))
]

let prefix_op_tests = [
  ("#hashtag", Some (application_fix (identifier_prefix_fix "#", [Some (identifier_basic_fix "hashtag")]))),
  ("-#foo", Some (application_fix (identifier_prefix_fix "-#", [Some (identifier_basic_fix "foo")]))),
  ("-(#bar)", Some (application_fix (identifier_prefix_fix "-", [Some (application_fix (identifier_prefix_fix "#", [Some (identifier_basic_fix "bar")]))]))),
  ("- #bar", Some (application_fix (identifier_prefix_fix "-", [Some (application_fix (identifier_prefix_fix "#", [Some (identifier_basic_fix "bar")]))]))),
  ("-_", Some (application_fix (identifier_prefix_fix "-", [None]))),
  ("-+- sparkle -+-", Some (application_fix (identifier_prefix_fix "-+-", [Some (application_fix (identifier_suffix_fix "-+-", [Some (identifier_basic_fix "sparkle")]))])))
]

let suffix_op_tests = [
  ("c++", Some (application_fix (identifier_suffix_fix "++", [Some (identifier_basic_fix "c")]))),
  ("_ - +", Some (application_fix (identifier_suffix_fix "+", [Some (application_fix (identifier_suffix_fix "-", [None]))]))),
  ("click.click.click", Some (application_fix (identifier_suffix_complex_fix (".click", []), [Some (application_fix (identifier_suffix_complex_fix (".click", []), [Some (identifier_basic_fix "click")]))]))),
  ("idk.about++.this++.chief", Some (application_fix (identifier_suffix_complex_fix (".chief", []), [Some (application_fix (identifier_suffix_fix "++", [Some (application_fix (identifier_suffix_complex_fix (".this", []), [Some (application_fix (identifier_suffix_fix "++", [Some (application_fix (identifier_suffix_complex_fix (".about", []), [Some (identifier_basic_fix "idk")]))]))]))]))])))
]

let abstraction_tests = [
  ("fun(a, b, c) = body", Some (abstraction_fix (["a", "b", "c"], identifier_basic_fix "body"))),
  ("fun (a ,b, c )=body", Some (abstraction_fix (["a", "b", "c"], identifier_basic_fix "body")))
]

let let_expression_tests = [
  ("let name=expr in body", Some (let_binding_fix ("name", identifier_basic_fix "expr", identifier_basic_fix "body"))),
  ("let name = expr in body", Some (let_binding_fix ("name", identifier_basic_fix "expr", identifier_basic_fix "body"))),
  ("let foo(a, b, c) = foocode in body", Some (let_binding_fix ("foo", abstraction_fix (["a", "b", "c"], identifier_basic_fix "foocode"), identifier_basic_fix "body"))),

  ("letname = expr in body", None),
  ("let name = expr inbody", None)
]

let let_rec_expression_tests = [
  ("let rec name = expr in body", Some (let_rec_binding_fix ("name", identifier_basic_fix "expr", identifier_basic_fix "body")))
]

let hole_tests = [
  ("$?help", Some (hole_fix "help"))
]

let misc_tests = [
  ("_", None),
  ("a + + b", None) (* This is ambiguous, and should be banned *)
]

(* TODO: other tests (depends on the parsers) *)

let show_all = any ("-a" ==) (to_list arg)

let parser_test parser (test, expected) =
  let got = parse (parser `seq` eof) test
  let dgot = parse parser test
  (* TODO: figure out how to impl eq for term, to fix this hack *)
  (* ideally impl show as well, showterm doesn't quite show the ast *)
  let sexp = showterm <$> expected
  let sgot = showterm <$> got
  let sdgot = showterm <$> dgot
  in (sexp == sgot, test, sexp, sgot, sdgot)

let filter_failing results = if show_all then results else filter (fun (success, _) -> not success) results

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
