open import "prelude.ml"
open import "./arg.ml"
open import "./ast.ml"
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

let identifier_tests () = [
  ("foo", Some (identifier_basic_fix "foo")),
  ("list", Some (identifier_basic_fix "list")),
  ("sum", Some (identifier_basic_fix "sum")),
  ("foldl", Some (identifier_basic_fix "foldl")),
  ("this_is_a_s1lly_but_v4l1d_identifier", Some (identifier_basic_fix "this_is_a_s1lly_but_v4l1d_identifier")),

  ("x___", Some (identifier_basic_fix "x___")),
  ("iCons", Some (identifier_basic_fix "iCons")),
  ("e", Some (identifier_basic_fix "e")),
  ("truething", Some (identifier_basic_fix "truething"))
]

let constructor_tests () = [
  ("Foo", Some (identifier_constructor_fix "Foo")),
  ("Left(l)", Some (application_fix (identifier_constructor_fix "Left", [Some (identifier_basic_fix "l")]))),
  ("Right(_)", Some (application_fix (identifier_constructor_fix "Right", [None]))),
  ("Nil ()", Some (application_fix (identifier_constructor_fix "Nil", []))),
  ("Cons (x, [y, z])", Some (application_fix (identifier_constructor_fix "Cons", [Some (identifier_basic_fix "x"), Some (list_cons_fix ([identifier_basic_fix "y", identifier_basic_fix "z"], None))])))
]

let boolean_tests (): list (string * option pterm) = [
  ("true", Some (literal_bool_fix true)),
  ("false", Some (literal_bool_fix false))
]

let string_tests () = [
  ("\"The quick brown fox jumps over the lazy dog.\"", Some (string_cons_fix ("The quick brown fox jumps over the lazy dog.", []))),
  ("\"The quick $color fox $(act)s over the lazy dog.\"", Some (string_cons_fix ("The quick ", [(identifier_basic_fix "color", " fox "), (identifier_basic_fix "act", "s over the lazy dog.")]))),
  ("\"The \\\"quick\\\" brown fox jump\\$ over the \\\\azy dog.\"", Some (string_cons_fix ("The \"quick\" brown fox jump$ over the \\azy dog.", []))),
  ("''The quick\n\"$color\" fox\n$(act)s over\nthe lazy dog.''", Some (string_cons_fix ("The quick\n\"", [(identifier_basic_fix "color", "\" fox\n"), (identifier_basic_fix "act", "s over\nthe lazy dog.")]))),
  ("'''The \"quick\" brown fox jump$ over the \\azy dog.'''", Some (string_cons_fix ("The \"quick\" brown fox jump$ over the \\azy dog.", []))),

  ("\"\nope\"", None)
]

let list_tests () = [
  ("[a,b,c]", Some (list_cons_fix ([identifier_basic_fix "a", identifier_basic_fix "b", identifier_basic_fix "c"], None))),
  ("[ a, b, c ]", Some (list_cons_fix ([identifier_basic_fix "a", identifier_basic_fix "b", identifier_basic_fix "c"], None))),
  ("[ a, b, ...tail ]", Some (list_cons_fix ([identifier_basic_fix "a", identifier_basic_fix "b"], Some (identifier_basic_fix "tail")))),

  ("[ ...tail ]", None)
]

let record_tests () = [
  ("{a=b,c=d,e=f}", Some (record_cons_fix [(identifier_basic_fix "a", identifier_basic_fix "b"), (identifier_basic_fix "c", identifier_basic_fix "d"), (identifier_basic_fix "e", identifier_basic_fix "f")])),
  ("{ a=b, c = d, e= f }", Some (record_cons_fix [(identifier_basic_fix "a", identifier_basic_fix "b"), (identifier_basic_fix "c", identifier_basic_fix "d"), (identifier_basic_fix "e", identifier_basic_fix "f")])),

  ("{ foo(a, b, c) = bar, \"ponies\" = \"cute\", (flopnax) = ropjar }", Some (record_cons_fix [(identifier_basic_fix "foo", abstraction_fix (["a", "b", "c"], identifier_basic_fix "bar")), (string_cons_fix ("ponies", []), string_cons_fix ("cute", [])), (identifier_basic_fix "flopnax", identifier_basic_fix "ropjar")])),
  ("{ a + b = c, #x = x ^ x, l.(i) = i }", Some (record_cons_fix [(identifier_infix_fix "+", abstraction_fix (["a", "b"], identifier_basic_fix "c")), (identifier_prefix_fix "#", abstraction_fix (["x"], application_fix (identifier_infix_fix "^", [Some (identifier_basic_fix "x"), Some (identifier_basic_fix "x")]))), (identifier_suffix_complex_fix (".(", [")"]), abstraction_fix (["l", "i"], identifier_basic_fix "i"))]))
]

let application_tests () = [
  ("foo()", Some (application_fix (identifier_basic_fix "foo", []))),
  ("foo(a, b, c)", Some (application_fix (identifier_basic_fix "foo", [Some (identifier_basic_fix "a"), Some (identifier_basic_fix "b"), Some (identifier_basic_fix "c")]))),
  ("foo (a,b,c)", Some (application_fix (identifier_basic_fix "foo", [Some (identifier_basic_fix "a"), Some (identifier_basic_fix "b"), Some (identifier_basic_fix "c")]))),
  ("foo(a, _, c)", Some (application_fix (identifier_basic_fix "foo", [Some (identifier_basic_fix "a"), None, Some (identifier_basic_fix "c")]))),
  ("foo(a)(_)(c)", Some (application_fix ((application_fix ((application_fix (identifier_basic_fix "foo", [Some (identifier_basic_fix "a")])), [None])), [Some (identifier_basic_fix "c")])))
]

let infix_op_tests () = [
  ("foo + bar", Some (application_fix (identifier_infix_fix "+", [Some (identifier_basic_fix "foo"), Some (identifier_basic_fix "bar")]))),
  ("one-to-one", Some (application_fix (identifier_infix_fix "-", [Some (application_fix (identifier_infix_fix "-", [Some (identifier_basic_fix "one"), Some (identifier_basic_fix "to")])), Some (identifier_basic_fix "one")]))),
  ("_ ^ \"n't\"", Some (application_fix (identifier_infix_fix "^", [None, Some (string_cons_fix ("n't", []))]))),
  ("+a+b+c+", Some (application_fix (identifier_infix_fix "+", [Some (application_fix (identifier_infix_fix "+", [Some (application_fix (identifier_prefix_fix "+", [Some (identifier_basic_fix "a")])), Some (identifier_basic_fix "b")])), Some (application_fix (identifier_suffix_fix "+", [Some (identifier_basic_fix "c")]))])))
]

let prefix_op_tests () = [
  ("#hashtag", Some (application_fix (identifier_prefix_fix "#", [Some (identifier_basic_fix "hashtag")]))),
  ("-#foo", Some (application_fix (identifier_prefix_fix "-#", [Some (identifier_basic_fix "foo")]))),
  ("-(#bar)", Some (application_fix (identifier_prefix_fix "-", [Some (application_fix (identifier_prefix_fix "#", [Some (identifier_basic_fix "bar")]))]))),
  ("- #bar", Some (application_fix (identifier_prefix_fix "-", [Some (application_fix (identifier_prefix_fix "#", [Some (identifier_basic_fix "bar")]))]))),
  ("-_", Some (application_fix (identifier_prefix_fix "-", [None]))),
  ("-+- sparkle -+-", Some (application_fix (identifier_prefix_fix "-+-", [Some (application_fix (identifier_suffix_fix "-+-", [Some (identifier_basic_fix "sparkle")]))])))
]

let suffix_op_tests () = [
  ("c++", Some (application_fix (identifier_suffix_fix "++", [Some (identifier_basic_fix "c")]))),
  ("_ - +", Some (application_fix (identifier_suffix_fix "+", [Some (application_fix (identifier_suffix_fix "-", [None]))]))),
  ("click.click.click", Some (application_fix (identifier_suffix_complex_fix (".click", []), [Some (application_fix (identifier_suffix_complex_fix (".click", []), [Some (identifier_basic_fix "click")]))]))),
  ("idk.about++.this++.chief", Some (application_fix (identifier_suffix_complex_fix (".chief", []), [Some (application_fix (identifier_suffix_fix "++", [Some (application_fix (identifier_suffix_complex_fix (".this", []), [Some (application_fix (identifier_suffix_fix "++", [Some (application_fix (identifier_suffix_complex_fix (".about", []), [Some (identifier_basic_fix "idk")]))]))]))]))]))),
  ("over.(engineer)", Some (application_fix (identifier_suffix_complex_fix (".(", [")"]), [Some (identifier_basic_fix "over"), Some (identifier_basic_fix "engineer")]))),
  ("_.(_)", Some (application_fix (identifier_suffix_complex_fix (".(", [")"]), [None, None])))
]

let abstraction_tests () = [
  ("fun(a, b, c) = body", Some (abstraction_fix (["a", "b", "c"], identifier_basic_fix "body"))),
  ("fun (a ,b, c )=body", Some (abstraction_fix (["a", "b", "c"], identifier_basic_fix "body")))
]

let let_expression_tests () = [
  ("let name=expr in body", Some (let_binding_fix (IdentifierBasic "name", identifier_basic_fix "expr", identifier_basic_fix "body"))),
  ("let name = expr in body", Some (let_binding_fix (IdentifierBasic "name", identifier_basic_fix "expr", identifier_basic_fix "body"))),
  ("let foo(a, b, c) = foocode in body", Some (let_binding_fix (IdentifierBasic "foo", abstraction_fix (["a", "b", "c"], identifier_basic_fix "foocode"), identifier_basic_fix "body"))),
  ("let a + b = c in a + b", Some (let_binding_fix (IdentifierInfix "+", abstraction_fix (["a", "b"], identifier_basic_fix "c"), application_fix (identifier_infix_fix "+", [Some (identifier_basic_fix "a"), Some (identifier_basic_fix "b")])))),
  ("let fundament.software = qts in space", Some (let_binding_fix (IdentifierSuffixComplex (".software", []), abstraction_fix (["fundament"], identifier_basic_fix "qts"), identifier_basic_fix "space"))),

  ("letname = expr in body", None),
  ("let name = expr inbody", None)
]

let let_rec_expression_tests () = [
  ("let rec name = expr in body", Some (let_rec_binding_fix (IdentifierBasic "name", identifier_basic_fix "expr", identifier_basic_fix "body"))),
  ("let rec #x = #x+a in #y", Some (let_rec_binding_fix (IdentifierPrefix "#", abstraction_fix (["x"], application_fix (identifier_infix_fix "+", [Some (application_fix (identifier_prefix_fix "#", [Some (identifier_basic_fix "x")])), Some (identifier_basic_fix "a")])), application_fix (identifier_prefix_fix "#", [Some (identifier_basic_fix "y")])))),

  ("letrec name = expr in body", None)
]

let hole_tests () = [
  ("$?help", Some (hole_fix (Some "help"))),
  ("$?", Some (hole_fix None))
]

let misc_tests () = [
  ("_", None),
  ("_internal", None),
  ("_Cons", None),
  ("++", None),
  ("::", None),
  ("a + + b", None) (* This is ambiguous, and should be banned *)
]

(* TODO: other tests (depends on the parsers) *)

let show_all = any ("-a" ==) (to_list arg)

let parser_test p (test, expected) =
  let eof = neg star
  let got = parse (p `seq` eof) test
  let dgot = parse p test
  let sexp = showterm <$> expected
  let sgot = showterm <$> got
  let sdgot = showterm <$> dgot
  (* TODO: figure out how to impl eq for term, to fix this hack *)
  in (sexp == sgot, test, sexp, sgot, sdgot)

let filter_failing results = if show_all then results else filter (fun (success, _) -> not success) results

let show_result (success, test, exp, got, debug) =
  "Success : " ^ show success ^ "\n"
  ^ "Test    : " ^ test ^ "\n"
  ^ "Expected: " ^ show exp ^ "\n"
  ^ "Got     : " ^ show got ^ "\n"
  ^ "Partial : " ^ show debug ^ "\n"

let run_tests (p, tests) =
  let results = parser_test p <$> tests
  let fails = filter_failing results
  in map (put_line % show_result) fails

let _ = run_tests (syntax, identifier_tests ())
let _ = run_tests (syntax, constructor_tests ())
let _ = run_tests (syntax, boolean_tests ())
let _ = run_tests (syntax, string_tests ())
let _ = run_tests (syntax, list_tests ())
let _ = run_tests (syntax, record_tests ())
let _ = run_tests (syntax, application_tests ())
let _ = run_tests (syntax, infix_op_tests ())
let _ = run_tests (syntax, prefix_op_tests ())
let _ = run_tests (syntax, suffix_op_tests ())
let _ = run_tests (syntax, abstraction_tests ())
let _ = run_tests (syntax, let_expression_tests ())
let _ = run_tests (syntax, let_rec_expression_tests ())
let _ = run_tests (syntax, hole_tests ())
let _ = run_tests (syntax, misc_tests ())
