
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

let catstr cs = foldl (^) "" cs

let matchingbracket = Map.from_list [("(|", "|)"), ("[|", "|]"), ("{|", "|}")]

let showterm = cata (function
  | LiteralBool b -> show b
  | StringCons (s, ts) -> "\"" ^ s ^ (map (fun (t, s) -> "$("^t^")"^s) ts |> catstr) ^ "\""
  | ListCons ts -> "[" ^ sep_commas ts ^ "]"
  | RecordCons tts -> "{" ^ (map (fun (a, b) -> a ^ " = " ^ b) tts |> sep_commas) ^ "}"
  | Identifier name -> show name
  (* TODO: prettier operators *)
  | Application (f, xs) -> f ^ "(" ^ (map (`or_default` "_") xs |> sep_commas) ^ ")"
  (* TODO: prettier function definitions *)
  | Abstraction (ids, body) -> "(fun (" ^ sep_commas ids ^ ") = " ^ body ^ ")"
  | LetBinding (id, def, body) -> "let " ^ show id ^ " = " ^ def ^ " in " ^ body
  | LetRecBinding (id, def, body) -> "let rec " ^ show id ^ " = " ^ def ^ " in " ^ body
  | Conditional (cond, cons, alt) -> "if " ^ cond ^ " then " ^ cons ^ " else " ^ alt
  | Hole (Some id) -> "$?"^id
  | Hole None -> "$?")

(* Fixed constructors *)
(* TODO: metaprogram this away *)
let identifier_fix x = Fix (Identifier x)
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

let id_basic_shy = c (alpha_lower `seq` (alnum_ext `rep` 0))
let id_basic = id_basic_shy `seq` wsq
let id_constructor = c (alpha_upper `seq` (alnum_ext `rep` 0)) `seq` wsq
(* TODO: different infix precedences *)
let id_infix = c (s "&+-<@^" `seq` (s "&+-@>" `rep` 0)) `seq` wsq
let id_prefix = c (s "#+-" `rep` 1) `seq` wsq
let id_suffix = c (s "+-" `rep` 1) `seq` wsq

(* TODO: ideally this would recognize an id_basic, check
 * if the capture is equal to str, and cancel the capture *)
(* the problem is idk how to cancel the capture *)
let keyword str = p str `seq` neg alnum_ext `seq` wsq
let keysym str = p str `seq` wsq
let cap pat res = pat `seq` cc res
let excl pat unless = neg unless `seq` pat
let comma_sep pat = collect_list (sepseq pat (keysym ","))

(* x *MUST* capture something, even if it's something dumb like cc () *)
(* otherwise types don't line up *)
(* also amulet doesn't like parser1 'a in the type ascription, who knows why *)
let id_suffix_complex (x: parser (parservals 'a emptyparservals)) =
  (* TODO: cancel id_basic capture to use it here *)
  let variant1 = collect_tuple (c (p "." `seq` alpha_lower `seq` (alnum_ext `rep` 0)) `cap` [])
  let variant2 = collect_tuple (c (p ".(") `seq` wsq `seq` collect_list (collect_tuple (x `seq` c (p ")"))))
  in variant1 `alt` variant2 `seq` wsq

(* TODO: bools are just type bool = True | False *)
(* this means conditionals are just pattern matches on bool *)
(* (not strictly true, Open has Ideas) *)
let parse_bool = function | "true" -> Some true | "false" -> Some false | _ -> None
let literal_bool: parser1 pterm = id_basic `actx` parse_bool `act` literal_bool_fix
let identifier_shy = id_basic_shy `act` identifier_basic_fix
let identifier = id_basic `act` identifier_basic_fix
let constructor = id_constructor `act` identifier_constructor_fix
let infix_op = id_infix `act` identifier_infix_fix
let prefix_op = id_prefix `act` identifier_prefix_fix
let suffix_op = id_suffix `act` identifier_suffix_fix
(* https://www.youtube.com/watch?v=T-BoDW1_9P4&t=11m3s *)
let unzip xs = foldr (fun (l, r) (ls, rs) -> (l::ls, r::rs)) ([], []) xs
let fixsuffix f (h, rs) = let (args, parts) = unzip rs in (f (h, parts), args)
let suffix_complex_op x = id_suffix_complex x `act` fixsuffix identifier_suffix_complex_fix

(* Attempt to control variables usage in compiled lua *)
(* TODO: move this even higher and figure out the type errors *)
let syntax () =

  let term_ref: parser1 pterm = v "term"
  let term_paren_shy = keysym "(" `seq` term_ref `seq` p ")"
  let term_paren = term_paren_shy `seq` wsq
  let term_definition = keysym "=" `seq` term_ref

  let abstraction_body =
    let args = keysym "(" `seq` comma_sep id_basic `seq` keysym ")"
    in collect_tuple (args `seq` term_definition) `act` abstraction_fix

  (* TODO: this is not enough, we need a whole pattern match identifier type
   * it needs to handle possibly self-referencing cases like lists and tuples *)
  let define_simple =
    let name = id_basic `act` IdentifierBasic
    in collect_tuple (name `seq` term_definition)

  let define_function = collect_tuple (id_basic `act` IdentifierBasic `seq` abstraction_body)

  let define_infix =
    let left = id_basic
    let op = id_infix `act` IdentifierInfix
    let right = id_basic
    let fixup (l, op, r, body) = (op, abstraction_fix ([l, r], body))
    in collect_tuple (left `seq` op `seq` right `seq` term_definition) `act` fixup

  let define_prefix =
    let op = id_prefix `act` IdentifierPrefix
    let right = id_basic
    let fixup (op, r, body) = (op, abstraction_fix ([r], body))
    in collect_tuple (op `seq` right `seq` term_definition) `act` fixup

  let define_suffix =
    let left = id_basic
    let op = id_suffix `act` IdentifierSuffix
    let fixup (l, op, body) = (op, abstraction_fix ([l], body))
    in collect_tuple (left `seq` op `seq` term_definition) `act` fixup

  let define_suffix_complex =
    let left = id_basic
    let rights = id_suffix_complex id_basic `act` fixsuffix IdentifierSuffixComplex
    let fixup (l, (op, rs), body) = (op, abstraction_fix (l::rs, body))
    in collect_tuple (left `seq` rights `seq` term_definition) `act` fixup

  let define_pattern = (
          define_simple
    `alt` define_function
    `alt` define_infix
    `alt` define_prefix
    `alt` define_suffix
    `alt` define_suffix_complex
  )

  let string_cons =
    (* TODO: newlines (as in actual 0A byte in the input) probably not allowed in strings *)
    (* TODO: other kinds of strings *)
    let regular_chars = c (star `excl` s "\"$\\")
    let escape_chars =
      foldl1 alt ((fun (s, r) -> lit s r) <$> [
        ("\\t", "\t"),
        ("\\n", "\n"),
        ("\\\"", "\""),
        ("\\\\", "\\")
      ])
    (* This looks really weird because escape_chars provides a custom capture,
     * which can't be handled with a simple c (bad things happen) *)
    let string_frag = collect_list (regular_chars `alt` escape_chars `rep` 0) `act` catstr
    let splice_frag = p "$" `seq` (identifier_shy `alt` term_paren_shy)
    let splice_list = collect_list (collect_tuple (splice_frag `seq` string_frag) `rep` 0)
    let string_inside = collect_tuple (string_frag `seq` splice_list)
    in p "\"" `seq` string_inside `seq` keysym "\"" `act` string_cons_fix

  let list_cons = keysym "[" `seq` comma_sep term_ref `seq` keysym "]" `act` list_cons_fix

  let record_cons =
    let record_binding1 = define_pattern `act` (fun (l, r) -> (identifier_fix l, r))
    let record_binding2 = collect_tuple (string_cons `alt` term_paren `seq` term_definition)
    let record_binding = record_binding1 `alt` record_binding2
    in keysym "{" `seq` comma_sep record_binding `seq` keysym "}" `act` record_cons_fix

  let abstraction = keyword "fun" `seq` abstraction_body

  let let_body =
    let fixup ((a, b), c) = (a, b, c)
    in collect_tuple (define_pattern `seq` keyword "in" `seq` term_ref) `act` fixup
  let let_binding = keyword "let" `seq` let_body `act` let_binding_fix
  let let_rec_binding = keyword "let" `seq` keyword "rec" `seq` let_body `act` let_rec_binding_fix

  let hole =
    let id_part = id_basic `act` Some `alt` cc None
    in p "$?" `seq` id_part `act` hole_fix

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
    `alt` constructor
  )

  (* Left-recursive parsers are hard >< *)
  (* The basic idea here is we're isolating each left-recursive parser
   * in a way where each parser can collect itself in a loop, and
   * higher-precedence parsers, but requires parens for lower-
   * -precedence parsers *)
  (* Incidentally, these are all function application of some kind. Go figure. *)

  let partial_argument t = (t `act` Some) `alt` (keysym "_" `cap` None)

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
    let suffix1 = suffix_op `seq` neg term_ref `act` (fun x -> (x, []))
    let suffix2 = suffix_complex_op (partial_argument term_ref)
    let suffix = suffix1 `alt` suffix2
    let suffix_rep = collect_list (suffix `rep` 0)
    let suffix_ops = collect_tuple (left `seq` suffix_rep)
    let fold (l, ops) = foldl (fun l (op, args) -> Some (application_fix (op, l::args))) l ops
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

  in grammar { term = term } term_ref

let syntax = syntax ()
