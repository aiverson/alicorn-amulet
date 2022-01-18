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

let id_tests () = [
  ("foo", Some (id_basic_fix "foo")),
  ("list", Some (id_basic_fix "list")),
  ("sum", Some (id_basic_fix "sum")),
  ("foldl", Some (id_basic_fix "foldl")),
  ("this_is_a_s1lly_but_v4l1d_identifier", Some (id_basic_fix "this_is_a_s1lly_but_v4l1d_identifier")),

  ("x___", Some (id_basic_fix "x___")),
  ("iCons", Some (id_basic_fix "iCons")),
  ("e", Some (id_basic_fix "e")),
  ("truething", Some (id_basic_fix "truething"))
]

let cons_tests () = [
  ("Foo", Some (id_cons_fix "Foo")),
  ("Left(l)", Some (term_app_fix (id_cons_fix "Left", [Some (id_basic_fix "l")]))),
  ("Right(_)", Some (term_app_fix (id_cons_fix "Right", [None]))),
  ("Nil ()", Some (term_app_fix (id_cons_fix "Nil", []))),
  ("Cons (x, [y, z])", Some (term_app_fix (id_cons_fix "Cons", [Some (id_basic_fix "x"), Some (term_list_fix ([id_basic_fix "y", id_basic_fix "z"], None))])))
]

let boolean_tests (): list (string * option pterm) = [
  ("true", Some (term_bool_fix true)),
  ("false", Some (term_bool_fix false))
]

let string_tests () = [
  ("\"The quick brown fox jumps over the lazy dog.\"", Some (term_string_fix ("The quick brown fox jumps over the lazy dog.", []))),
  ("\"The quick $color fox $(act)s over the lazy dog.\"", Some (term_string_fix ("The quick ", [(id_basic_fix "color", " fox "), (id_basic_fix "act", "s over the lazy dog.")]))),
  ("\"The \\\"quick\\\" brown fox jump\\$ over the \\\\azy dog.\"", Some (term_string_fix ("The \"quick\" brown fox jump$ over the \\azy dog.", []))),
  ("''The quick\n\"$color\" fox\n$(act)s over\nthe lazy dog.''", Some (term_string_fix ("The quick\n\"", [(id_basic_fix "color", "\" fox\n"), (id_basic_fix "act", "s over\nthe lazy dog.")]))),
  ("'''The \"quick\" brown fox jump$ over the \\azy dog.'''", Some (term_string_fix ("The \"quick\" brown fox jump$ over the \\azy dog.", []))),

  ("\"\nope\"", None)
]

let list_tests () = [
  ("[a,b,c]", Some (term_list_fix ([id_basic_fix "a", id_basic_fix "b", id_basic_fix "c"], None))),
  ("[ a, b, c ]", Some (term_list_fix ([id_basic_fix "a", id_basic_fix "b", id_basic_fix "c"], None))),
  ("[ a, b, ...tail ]", Some (term_list_fix ([id_basic_fix "a", id_basic_fix "b"], Some (id_basic_fix "tail")))),
  ("[ ...tail ]", Some (term_list_fix ([], Some (id_basic_fix "tail"))))
]

let record_tests () = [
  ("{a=b,c=d,e=f}", Some (term_record_fix [(id_basic_fix "a", id_basic_fix "b"), (id_basic_fix "c", id_basic_fix "d"), (id_basic_fix "e", id_basic_fix "f")])),
  ("{ a=b, c = d, e= f }", Some (term_record_fix [(id_basic_fix "a", id_basic_fix "b"), (id_basic_fix "c", id_basic_fix "d"), (id_basic_fix "e", id_basic_fix "f")])),

  ("{ foo(a, b, c) = bar, \"ponies\" = \"cute\", (flopnax) = ropjar }", Some (term_record_fix [(id_basic_fix "foo", term_abs_fix ([pat_bind_basic_fix "a", pat_bind_basic_fix "b", pat_bind_basic_fix "c"], id_basic_fix "bar")), (term_string_fix ("ponies", []), term_string_fix ("cute", [])), (id_basic_fix "flopnax", id_basic_fix "ropjar")])),
  ("{ a + b = c, #x = x ^ x, l.(i) = i }", Some (term_record_fix [(id_infix_fix "+", term_abs_fix ([pat_bind_basic_fix "a", pat_bind_basic_fix "b"], id_basic_fix "c")), (id_prefix_fix "#", term_abs_fix ([pat_bind_basic_fix "x"], term_app_fix (id_infix_fix "^", [Some (id_basic_fix "x"), Some (id_basic_fix "x")]))), (id_suffix_complex_fix (".(", [")"]), term_abs_fix ([pat_bind_basic_fix "l", pat_bind_basic_fix "i"], id_basic_fix "i"))]))
]

let app_tests () = [
  ("foo()", Some (term_app_fix (id_basic_fix "foo", []))),
  ("foo(a, b, c)", Some (term_app_fix (id_basic_fix "foo", [Some (id_basic_fix "a"), Some (id_basic_fix "b"), Some (id_basic_fix "c")]))),
  ("foo (a,b,c)", Some (term_app_fix (id_basic_fix "foo", [Some (id_basic_fix "a"), Some (id_basic_fix "b"), Some (id_basic_fix "c")]))),
  ("foo(a, _, c)", Some (term_app_fix (id_basic_fix "foo", [Some (id_basic_fix "a"), None, Some (id_basic_fix "c")]))),
  ("foo(a)(_)(c)", Some (term_app_fix ((term_app_fix ((term_app_fix (id_basic_fix "foo", [Some (id_basic_fix "a")])), [None])), [Some (id_basic_fix "c")])))
]

let infix_app_tests () = [
  ("foo + bar", Some (term_app_fix (id_infix_fix "+", [Some (id_basic_fix "foo"), Some (id_basic_fix "bar")]))),
  ("one-to-one", Some (term_app_fix (id_infix_fix "-", [Some (term_app_fix (id_infix_fix "-", [Some (id_basic_fix "one"), Some (id_basic_fix "to")])), Some (id_basic_fix "one")]))),
  ("_ ^ \"n't\"", Some (term_app_fix (id_infix_fix "^", [None, Some (term_string_fix ("n't", []))]))),
  ("+a+b+c+", Some (term_app_fix (id_infix_fix "+", [Some (term_app_fix (id_infix_fix "+", [Some (term_app_fix (id_prefix_fix "+", [Some (id_basic_fix "a")])), Some (id_basic_fix "b")])), Some (term_app_fix (id_suffix_fix "+", [Some (id_basic_fix "c")]))])))
]

let prefix_app_tests () = [
  ("#hashtag", Some (term_app_fix (id_prefix_fix "#", [Some (id_basic_fix "hashtag")]))),
  ("-#foo", Some (term_app_fix (id_prefix_fix "-#", [Some (id_basic_fix "foo")]))),
  ("-(#bar)", Some (term_app_fix (id_prefix_fix "-", [Some (term_app_fix (id_prefix_fix "#", [Some (id_basic_fix "bar")]))]))),
  ("- #bar", Some (term_app_fix (id_prefix_fix "-", [Some (term_app_fix (id_prefix_fix "#", [Some (id_basic_fix "bar")]))]))),
  ("-_", Some (term_app_fix (id_prefix_fix "-", [None]))),
  ("-+- sparkle -+-", Some (term_app_fix (id_prefix_fix "-+-", [Some (term_app_fix (id_suffix_fix "-+-", [Some (id_basic_fix "sparkle")]))])))
]

let suffix_app_tests () = [
  ("c++", Some (term_app_fix (id_suffix_fix "++", [Some (id_basic_fix "c")]))),
  ("_ - +", Some (term_app_fix (id_suffix_fix "+", [Some (term_app_fix (id_suffix_fix "-", [None]))]))),
  ("click.click.click", Some (term_app_fix (id_suffix_complex_fix (".click", []), [Some (term_app_fix (id_suffix_complex_fix (".click", []), [Some (id_basic_fix "click")]))]))),
  ("idk.about++.this++.chief", Some (term_app_fix (id_suffix_complex_fix (".chief", []), [Some (term_app_fix (id_suffix_fix "++", [Some (term_app_fix (id_suffix_complex_fix (".this", []), [Some (term_app_fix (id_suffix_fix "++", [Some (term_app_fix (id_suffix_complex_fix (".about", []), [Some (id_basic_fix "idk")]))]))]))]))]))),
  ("over.(engineer)", Some (term_app_fix (id_suffix_complex_fix (".(", [")"]), [Some (id_basic_fix "over"), Some (id_basic_fix "engineer")]))),
  ("_.(_)", Some (term_app_fix (id_suffix_complex_fix (".(", [")"]), [None, None])))
]

let abs_tests () = [
  ("fun(a, b, c) = body", Some (term_abs_fix ([pat_bind_basic_fix "a", pat_bind_basic_fix "b", pat_bind_basic_fix "c"], id_basic_fix "body"))),
  ("fun (a ,b, c )=body", Some (term_abs_fix ([pat_bind_basic_fix "a", pat_bind_basic_fix "b", pat_bind_basic_fix "c"], id_basic_fix "body"))),
  ("fun ([a, b, ...c], oh) = ok", Some (term_abs_fix ([pat_list_fix ([pat_bind_basic_fix "a", pat_bind_basic_fix "b"], Some (pat_bind_basic_fix "c")), pat_bind_basic_fix "oh"], id_basic_fix "ok")))
]

let let_tests () = [
  ("let name=expr in body", Some (term_let_fix (pat_bind_basic_fix "name", id_basic_fix "expr", id_basic_fix "body"))),
  ("let name = expr in body", Some (term_let_fix (pat_bind_basic_fix "name", id_basic_fix "expr", id_basic_fix "body"))),
  ("let foo(a, b, c) = foocode in body", Some (term_let_fix (pat_bind_basic_fix "foo", term_abs_fix ([pat_bind_basic_fix "a", pat_bind_basic_fix "b", pat_bind_basic_fix "c"], id_basic_fix "foocode"), id_basic_fix "body"))),
  ("let a + b = c in a + b", Some (term_let_fix (pat_bind_infix_fix "+", term_abs_fix ([pat_bind_basic_fix "a", pat_bind_basic_fix "b"], id_basic_fix "c"), term_app_fix (id_infix_fix "+", [Some (id_basic_fix "a"), Some (id_basic_fix "b")])))),
  ("let fundament.software = qts in space", Some (term_let_fix (pat_bind_suffix_complex_fix (".software", []), term_abs_fix ([pat_bind_basic_fix "fundament"], id_basic_fix "qts"), id_basic_fix "space"))),
  ("let x=f()in[x]", Some (term_let_fix (pat_bind_basic_fix "x", term_app_fix (id_basic_fix "f", []), term_list_fix ([id_basic_fix "x"], None)))),
  ("let pa=ic in the-disco", Some (term_let_fix (pat_bind_basic_fix "pa", id_basic_fix "ic", term_app_fix (id_infix_fix "-", [Some (id_basic_fix "the"), Some (id_basic_fix "disco")])))),
  ("let Pa=ic in the-disco", Some (term_let_fix (pat_bind_cons_fix "Pa", id_basic_fix "ic", term_app_fix (id_infix_fix "-", [Some (id_basic_fix "the"), Some (id_basic_fix "disco")])))),
  ("let { left = myl, right = myr } = get_left_right() in myl + myr", Some (term_let_fix (pat_record_fix [( IdentifierBasic "left", pat_bind_basic_fix "myl"), ( IdentifierBasic "right", pat_bind_basic_fix "myr")], term_app_fix (id_basic_fix "get_left_right", []), term_app_fix (id_infix_fix "+", [Some (id_basic_fix "myl"), Some (id_basic_fix "myr")])))),
  ("let [[oh, woe], [is, my]] = sanity in amulet", Some (term_let_fix (pat_list_fix ([pat_list_fix ([pat_bind_basic_fix "oh", pat_bind_basic_fix "woe"], None), pat_list_fix ([pat_bind_basic_fix "is", pat_bind_basic_fix "my"], None)], None), id_basic_fix "sanity", id_basic_fix "amulet"))),
  ("let [...what] = is in there", Some (term_let_fix (pat_list_fix ([], Some (pat_bind_basic_fix "what")), id_basic_fix "is", id_basic_fix "there"))),
  ("let _ - _ = - _ in - _ -", Some (term_let_fix (pat_bind_infix_fix "-", term_abs_fix ([pat_blank_fix, pat_blank_fix], term_app_fix (id_prefix_fix "-", [None])), term_app_fix (id_prefix_fix "-", [Some (term_app_fix (id_suffix_fix "-", [None]))])))),

  ("letname = expr in body", None),
  ("let name = expr inbody", None)
]

let let_rec_tests () = [
  ("let rec name = expr in body", Some (term_let_rec_fix (pat_bind_basic_fix "name", id_basic_fix "expr", id_basic_fix "body"))),
  ("let rec #x = #x+a in #y", Some (term_let_rec_fix (pat_bind_prefix_fix "#", term_abs_fix ([pat_bind_basic_fix "x"], term_app_fix (id_infix_fix "+", [Some (term_app_fix (id_prefix_fix "#", [Some (id_basic_fix "x")])), Some (id_basic_fix "a")])), term_app_fix (id_prefix_fix "#", [Some (id_basic_fix "y")])))),

  ("letrec name = expr in body", None)
]

let hole_tests () = [
  ("$?help", Some (term_hole_fix (Some (IdentifierBasic "help")))),
  ("$?", Some (term_hole_fix None))
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

let _ = run_tests (syntax, id_tests ())
let _ = run_tests (syntax, cons_tests ())
let _ = run_tests (syntax, boolean_tests ())
let _ = run_tests (syntax, string_tests ())
let _ = run_tests (syntax, list_tests ())
let _ = run_tests (syntax, record_tests ())
let _ = run_tests (syntax, app_tests ())
let _ = run_tests (syntax, infix_app_tests ())
let _ = run_tests (syntax, prefix_app_tests ())
let _ = run_tests (syntax, suffix_app_tests ())
let _ = run_tests (syntax, abs_tests ())
let _ = run_tests (syntax, let_tests ())
let _ = run_tests (syntax, let_rec_tests ())
let _ = run_tests (syntax, hole_tests ())
let _ = run_tests (syntax, misc_tests ())
