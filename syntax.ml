
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

let sep_commas xs = intercalate ", " xs

let matchingbracket = Map.from_list [("(|", "|)"), ("[|", "|]"), ("{|", "|}")]

let showterm = cata (function
  | LiteralBool b -> show b
  | StringCons (s, ts) -> "\"" ^ s ^ (map (fun (t, s) -> "$("^t^")"^s) ts |> foldl (^) "") ^ "\""
  | ListCons ts -> "[" ^ sep_commas ts ^ "]"
  | RecordCons tts -> "{" ^ (map (fun (a, b) -> a ^ " = " ^ b) tts |> sep_commas) ^ "}"
  | Identifier name -> show name
  | Application (f, xs) -> f ^ "(" ^ sep_commas (map (`or_default` "_") xs) ^ ")"
  | Abstraction (ids, body) -> "fun (" ^ sep_commas ids ^ ") = " ^ body ^ ")"
  | LetBinding (id, def, body) -> "let " ^ id ^ " = " ^ def ^ " in " ^ body
  | LetRecBinding (id, def, body) -> "let rec " ^ id ^ " = " ^ def ^ " in " ^ body
  | Conditional (cond, cons, alt) -> "if " ^ cond ^ " then " ^ cons ^ " else " ^ alt
  | Hole id -> "$?"^id)

(* Fixed constructors *)
(* TODO: metaprogram this away *)
let identifier_basic_fix x = Fix (Identifier (IdentifierBasic x))
let identifier_constructor_fix x = Fix (Identifier (IdentifierConstructor x))
let identifier_infix_fix x = Fix (Identifier (IdentifierInfix x))
let identifier_prefix_fix x = Fix (Identifier (IdentifierPrefix x))
let identifier_suffix_fix x = Fix (Identifier (IdentifierSuffix x))
let identifier_suffix_complex_fix x = Fix (Identifier (IdentifierSuffixComplex x))
let literal_bool_fix x = Fix (LiteralBool x)
let string_cons_fix x = Fix (StringCons x)
let list_cons_fix x = Fix (ListCons x)
let record_cons_fix x = Fix (RecordCons x)
let application_fix x = Fix (Application x)
let abstraction_fix x = Fix (Abstraction x)
let let_binding_fix x = Fix (LetBinding x)
let let_rec_binding_fix x = Fix (LetRecBinding x)
let conditional_fix x = Fix (Conditional x)
let hole_fix x = Fix (Hole x)

let num = r "09"
let alpha_upper = r "AZ"
let alpha_lower = r "az"
let alpha = alpha_upper `alt` alpha_lower
let alnum = alpha `alt` num
let alnum_ext = alnum `alt` p "_"
let eof = neg star

let id_basic_shy = c (alpha_lower `seq` (alnum_ext `rep` 0))
let id_basic = id_basic_shy `seq` wsq
(* TODO: different infix precedences *)
let id_infix = c (s "&+-<@^" `seq` (s "&+-@>" `rep` 0)) `seq` wsq
let id_prefix = c (s "#+-" `rep` 1) `seq` wsq
let id_suffix = c (s "+-" `rep` 1) `seq` wsq
(* TODO: cancel id_basic capture to use it here *)
(* TODO: more complex suffix identifiers *)
let id_suffix_complex = c (p "." `seq` alpha_lower `seq` (alnum_ext `rep` 0))

(* TODO: ideally this would recognize an id_basic, check if the capture is equal to str, and cancel the capture *)
(* the problem is idk how to cancel the capture *)
let keyword str = p str `seq` neg alnum_ext `seq` wsq
let keysym str = p str `seq` wsq
let cap pat res = pat `seq` cc res
let excl pat unless = neg unless `seq` pat
let collect_sep pat sep = collect_list (sepseq pat sep)
let comma_sep pat = collect_sep pat (keysym ",")

(* TODO: bools are just type bool = True | False *)
(* this means conditionals are just pattern matches on bool *)
(* (not strictly true, Open has Ideas) *)
let parse_bool = function | "true" -> Some true | "false" -> Some false | _ -> None
let literal_bool: parser1 pterm = id_basic `actx` parse_bool `act` literal_bool_fix
let identifier_shy = id_basic_shy `act` identifier_basic_fix
let identifier = id_basic `act` identifier_basic_fix

let infix_op = id_infix `act` identifier_infix_fix
let prefix_op = id_prefix `act` identifier_prefix_fix
let suffix_op = id_suffix `act` identifier_suffix_fix
let suffix_complex_op = id_suffix_complex `act` (fun x -> identifier_suffix_complex_fix (x, []))

let term_ref: parser1 pterm = v "term"
let term_paren_shy = keysym "(" `seq` term_ref `seq` p ")"
let term_paren = term_paren_shy `seq` wsq

let abstraction_body =
  collect_tuple (
          keysym "(" `seq` comma_sep id_basic `seq` keysym ")"
    `seq` keysym "=" `seq` term_ref
  ) `act` abstraction_fix
(* TODO: this is not enough, we need a whole pattern match identifier type
 * it needs to handle identifiers, functions, operators,
 * and possibly more possibly self-referencing cases
 * this will also allow operators to be represented as function application
 * with operator-type identifiers *)
let abstraction_sugar idtype = id_basic `act` idtype `seq` abstraction_body

let partial_argument t = (t `act` Some) `alt` (keysym "_" `cap` None)

let string_cons =
  let escape_chars =
    foldl1 alt ((fun (s, r) -> lit s r) <$> [
      ("\\t", "\t"),
      ("\\n", "\n"),
      ("\\\"", "\""),
      ("\\\\", "\\")
    ])
  (* This looks really weird because escape_chars provides a capture,
   * and nested captures are buggy, so some fiddling is needed *)
  (* TODO: newlines (as in actual 0A byte in the input) probably not allowed in strings *)
  let string_frag = collect_list (c (star `excl` s "\"$\\") `alt` escape_chars `rep` 0) `act` foldl (^) ""
  let splice_frag = p "$" `seq` (identifier_shy `alt` term_paren_shy)
  (* types are hard, and they don't let me use collect_sep here *)
  let splice_list = collect_list (collect_tuple (splice_frag `seq` string_frag) `rep` 0)
  in p "\"" `seq` collect_tuple (string_frag `seq` splice_list) `seq` keysym "\"" `act` string_cons_fix

let list_cons = keysym "[" `seq` comma_sep term_ref `seq` keysym "]" `act` list_cons_fix

let record_cons =
  let record_key = identifier `alt` string_cons `alt` term_paren
  let record_binding = collect_tuple (
    (record_key `seq` keysym "=" `seq` term_ref) `alt` abstraction_sugar identifier_basic_fix
  )
  in keysym "{" `seq` comma_sep record_binding `seq` keysym "}" `act` record_cons_fix

let abstraction = keyword "fun" `seq` abstraction_body

(* TODO: operator bindings *)
let let_body =
  let binding = (id_basic `seq` keysym "=" `seq` term_ref) `alt` abstraction_sugar id
  in collect_tuple (binding `seq` keyword "in" `seq` term_ref)

let let_binding = keyword "let" `seq` let_body `act` let_binding_fix

let let_rec_binding = keyword "let" `seq` keyword "rec" `seq` let_body `act` let_rec_binding_fix

(* TODO: id optional *)
let hole = p "$?" `seq` id_basic `act` hole_fix

let term_key = (
        term_paren
  `alt` literal_bool
  `alt` string_cons
  `alt` list_cons
  `alt` record_cons
  `alt` abstraction
  `alt` let_binding
  `alt` let_rec_binding
  `alt` hole
  `alt` identifier
)

(* Left-recursive parsers are hard >< *)
(* The basic idea here is we're isolating each left-recursive parser
 * in a way where each parser can collect itself in a loop, and
 * higher-precedence parsers, but requires parens for lower-
 * -precedence parsers *)

let application =
  (* cursed idea: _(arg) meta-partial function application *)
  let left = term_key
  let paren_app = keysym "(" `seq` comma_sep (partial_argument term_ref) `seq` keysym ")"
  let paren_rep = collect_list (paren_app `rep` 0)
  let application_ops = collect_tuple (left `seq` paren_rep)
  let fold (l, ps) = foldl (fun l p -> application_fix (l, p)) l ps
  in application_ops `act` fold

let suffix_op_application =
  let left = partial_argument application
  (* hacky workaround to make sure suffix ops don't eat infix ops *)
  (* TODO: possibly causes a lot of backtracking, test this! *)
  let suffix_op = (suffix_op `seq` neg term_ref) `alt` suffix_complex_op
  let suffix_rep = collect_list (suffix_op `rep` 0)
  let suffix_ops = collect_tuple (left `seq` suffix_rep)
  let fold (l, ops) = foldl (fun l op -> Some (application_fix (op, [l]))) l ops
  in suffix_ops `actx` fold

(* prefix ops aren't left recursive, but putting
 * them here is necessary for correct precedence *)
let prefix_op_application =
  let right = partial_argument suffix_op_application
  let prefix_rep = collect_list (prefix_op `rep` 0)
  let prefix_ops = collect_tuple (prefix_rep `seq` right)
  let fold (ops, r) = foldr (fun op r -> Some (application_fix (op, [r]))) r ops
  in prefix_ops `actx` fold

let infix_op_application =
  let left = partial_argument prefix_op_application
  let right = collect_tuple (infix_op `seq` left)
  let right_rep = collect_list (right `rep` 0)
  let infix_ops = collect_tuple (left `seq` right_rep)
  let fold (l, rs) = foldl (fun l (op, r) -> Some (application_fix (op, [l, r]))) l rs
  in infix_ops `actx` fold

let term = infix_op_application

let parser = grammar { term = term } term_ref
