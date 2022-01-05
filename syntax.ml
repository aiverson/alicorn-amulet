
open import "prelude.ml"
open import "./parsing/lpeg.ml"
open import "./parsing/utils.ml"
open import "./ast.ml"
open import "./result.ml"
open import "./hylo.ml"
open import "./utils.ml"
module Map = import "data/map.ml"

type position = Pos of int
let get_pos() = cp

type pterm <- fix (term string)

let rec intercalate s ss = match ss with
| Cons (a, Cons (b, tl)) -> a ^ s ^ intercalate s (Cons (b, tl))
| Cons (a, Nil) -> a
| Nil -> ""

let matchingbracket = Map.from_list [("(|", "|)"), ("[|", "|]"), ("{|", "|}")]

let showterm = cata (function
  | LiteralBool b -> show b
  | StringCons (s, ts) -> "\"" ^ s ^ (map (fun (t, s) -> "$("^t^")"^s) ts |> foldl (^) "") ^ "\""
  | ListCons ts -> intercalate ", " ts
  | RecordCons tts -> map (fun (a, b) -> a ^ " = " ^ b) tts |> intercalate ", "
  | Identifier name -> name
  | Application (f, xs) -> f ^ "(" ^ intercalate ", " xs ^ ")"
  | PartialApplication (f, xs) -> f ^ "(" ^ intercalate "," (map (function | Some x -> x | None -> "_") xs) ^")"
  | InfixOp (a, op, b) -> "("^a^" "^op^" "^b^")"
  | PartialInfixOp (a, op, b) -> "("^(a `or_default` "_")^" "^op^" "^(b `or_default` "_")^")"
  | PrefixOp (op, b) -> "("^op^b^")"
  | PartialPrefixOp (op, b) -> "("^op^(b `or_default` "_")^")"
  | SuffixOp (a, op) -> "("^a^op^")"
  | PartialSuffixOp (a, op) -> "("^(a `or_default` "_")^op^")"
  | Abstraction (ids, body) -> "fun ("^ intercalate ", " ids ^ ") = " ^ body ^ ")"
  | LetBinding (id, def, body) -> "let " ^ id ^ " = " ^ def ^ " in " ^ body
  | Conditional (cond, cons, alt) -> "if " ^ cond ^ " then " ^ cons ^ " else " ^ alt
  | Hole id -> "$?"^id)

(* Fixed constructors *)
(* TODO: metaprogram this away *)
let literal_bool_fix x = Fix (LiteralBool x)
let string_cons_fix x = Fix (StringCons x)
let list_cons_fix x = Fix (ListCons x)
let record_cons_fix x = Fix (RecordCons x)
let identifier_fix x = Fix (Identifier x)
let application_fix x = Fix (Application x)
let partial_application_fix x = Fix (PartialApplication x)
let infix_op_fix x = Fix (InfixOp x)
let partial_infix_op_fix x = Fix (PartialInfixOp x)
let prefix_op_fix x = Fix (PrefixOp x)
let partial_prefix_op_fix x = Fix (PartialPrefixOp x)
let suffix_op_fix x = Fix (SuffixOp x)
let partial_suffix_op_fix x = Fix (PartialSuffixOp x)
let abstraction_fix x = Fix (Abstraction x)
let let_binding_fix x = Fix (LetBinding x)
let conditional_fix x = Fix (Conditional x)
let hole_fix x = Fix (Hole x)

let num = r "09"
let alpha_upper = r "AZ"
let alpha_lower = r "az"
let alpha = alpha_upper `alt` alpha_lower
let alnum = alpha `alt` num
let alnum_ext = alnum `alt` p "_"
let eof = neg star

let keyword str = p str `seq` wsp
let keysym str = p str `seq` wsq
let commasep pat = collect_list (sepseq pat (keysym ","))
let basic_id = c (alpha_lower `seq` (alnum_ext `rep` 0)) `seq` wsq

let escapechars = lit "\\n" "\n" `alt` lit "\\t" "\t"
(* TODO: fix this *)
(*
let stringfrag = cs (((neg @@ s "\"$\\") `seq` star `alt` escapechars `rep` 0))
*)

(* TODO: that wsp is sus, what about a tailgating operator? *)
let literal_bool: parser1 pterm = lit "true" true `alt` lit "false" false `act` literal_bool_fix `seq` wsp
(* TODO: is wsq correct? *)
let identifier = basic_id `act` identifier_fix
(* TODO: metaprogram this away *)
let string_cons: parser1 pterm = v "string_cons"
let list_cons: parser1 pterm = v "list_cons"
let record_cons: parser1 pterm = v "record_cons"
let application: parser1 pterm = v "application"
let abstraction: parser1 pterm = v "abstraction"
let let_binding: parser1 pterm = v "let_binding"
let term: parser1 pterm = v "term"

(* mega-TODO:
 *   let rec bindings
 *   let function bindings
 *   everything else
 *)
let parser =
  grammar {
  (*
    string_cons = p"\""
    `seq` stringfrag
    `seq` collect_list( collect_tuple (
      p"$" `seq` (identifier `alt` (p"(" `seq` term `seq` p")"))
      `seq` stringfrag) `rep` 0)
  *)
    (* don't forget the comma here *)
    list_cons = keysym "[" `seq` commasep term `seq` keysym "]" `act` list_cons_fix
  , record_cons =
      let record_key = identifier `alt` (* string_cons `alt` *) (keysym "(" `seq` term `seq` keysym ")")
      let record_pair = collect_tuple (record_key `seq` keysym "=" `seq` term)
      in keysym "{" `seq` commasep record_pair `seq` keysym "}" `act` record_cons_fix
    (* TODO: arbitrary terms on the left? too spicy for lpeg *)
  , application = collect_tuple (identifier `seq` keysym "(" `seq` commasep term `seq` keysym ")") `act` application_fix
    (* TODO: is keysym "fun" correct? *)
  , abstraction = keysym "fun" `seq` collect_tuple (keysym "(" `seq` commasep basic_id `seq` keysym ")" `seq` keysym "=" `seq` term) `act` abstraction_fix
    (* TODO: is keysym "in" correct? (probably not) *)
  , let_binding = keyword "let" `seq` collect_tuple (basic_id `seq` keysym "=" `seq` term `seq` keysym "in" `seq` term) `act` let_binding_fix

  , term =
      (* first, parsers that start with keywords/keysyms *)
      literal_bool `alt` (* string_cons `alt` *) list_cons `alt` record_cons `alt` abstraction `alt` let_binding
      (* lastly, function application before basic identifiers *)
      `alt` application `alt` identifier
  } term

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
  (sexp == sgot, test, sexp, sgot)
let filter_failing results = filter (fun (success, _) -> not success) results
let run_tests (parser, tests) =
  let results = parser_test parser <$> tests
  let fails = filter_failing results
  map print fails
let _ = run_tests (parser, parser_tests)
