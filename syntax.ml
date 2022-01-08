
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
  | Application (f, xs) -> f ^ "(" ^ intercalate "," (map (function | Some x -> x | None -> "_") xs) ^")"
  | InfixOp (a, op, b) -> "("^(a `or_default` "_")^" "^op^" "^(b `or_default` "_")^")"
  | PrefixOp (op, b) -> "("^op^(b `or_default` "_")^")"
  | SuffixOp (a, op) -> "("^(a `or_default` "_")^op^")"
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
let infix_op_fix x = Fix (InfixOp x)
let prefix_op_fix x = Fix (PrefixOp x)
let suffix_op_fix x = Fix (SuffixOp x)
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

let id_basic_shy = c (alpha_lower `seq` (alnum_ext `rep` 0))
let id_basic = id_basic_shy `seq` wsq
let id_prefix = c (s "#+-" `rep` 1) `seq` wsq
let id_suffix_simple = c (s "+-" `rep` 1) `seq` wsq

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
let identifier_shy = id_basic_shy `act` identifier_fix
let identifier = id_basic `act` identifier_fix

let term_ref: parser1 pterm = v "term"
let term_paren_shy = keysym "(" `seq` term_ref `seq` p ")"
let term_paren = term_paren_shy `seq` wsq

let abstraction_body =
  collect_tuple (
          keysym "(" `seq` comma_sep id_basic `seq` keysym ")"
    `seq` keysym "=" `seq` term_ref
  ) `act` abstraction_fix
let abstraction_sugar idtype = id_basic `act` idtype `seq` abstraction_body

let partial_argument = (term_ref `act` Some) `alt` (keysym "_" `cap` None)

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
    (record_key `seq` keysym "=" `seq` term_ref) `alt` abstraction_sugar identifier_fix
  )
  in keysym "{" `seq` comma_sep record_binding `seq` keysym "}" `act` record_cons_fix

let application =
  (* TODO: the term case is not specified in the design doc, is it ok? (probably not, eg f(x)(y)) *)
  let left = identifier `alt` term_paren
  in collect_tuple (left `seq` keysym "(" `seq` comma_sep partial_argument `seq` keysym ")") `act` application_fix

let prefix_op_application = collect_tuple (id_prefix `seq` partial_argument) `act` prefix_op_fix

(* TODO: advanced suffix operators *)
let suffix_op_application = collect_tuple (partial_argument `seq` id_suffix_simple) `act` suffix_op_fix

let abstraction = keyword "fun" `seq` abstraction_body

(* TODO: let rec bindings *)
(* TODO: operator bindings *)
let let_binding =
  let binding = (id_basic `seq` keysym "=" `seq` term_ref) `alt` abstraction_sugar id
  in keyword "let"
     `seq` collect_tuple (binding `seq` keyword "in" `seq` term_ref)
     `act` let_binding_fix

let hole = p "$?" `seq` id_basic `act` hole_fix

let term = (
  (* first, parsers that start with keywords/keysyms *)
        term_paren
  `alt` literal_bool
  `alt` string_cons
  `alt` list_cons
  `alt` record_cons
  `alt` abstraction
  `alt` let_binding
  `alt` hole
  (* next, function application before basic identifiers *)
  `alt` application
  `alt` identifier
  (* lastly, operators *)
  (* TODO: terms on the left are scary *)
  (*`alt` suffix_op_application*)
  `alt` prefix_op_application
  (*`alt` infix_op_application*)
)

let parser = grammar { term = term } term_ref
