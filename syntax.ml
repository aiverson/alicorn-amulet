
open import "prelude.ml"
open import "./parsing/lpeg.ml"
open import "./parsing/utils.ml"
open import "./ast.ml"
open import "./hylo.ml"

let num = r "09"
let alpha_upper = r "AZ"
let alpha_lower = r "az"
let alpha = alpha_upper `alt` alpha_lower
let alnum = alpha `alt` num
let alnum_ext = alnum `alt` p "_"

let id_basic_shy = c (alpha_lower `seq` (alnum_ext `rep` 0))
let id_basic = id_basic_shy `seq` wsq
let id_cons = c (alpha_upper `seq` (alnum_ext `rep` 0)) `seq` wsq
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
let opt pat = pat `act` Some `alt` cc None

(* x *MUST* capture something, even if it's something dumb like cc () *)
(* otherwise types don't line up *)
(* also amulet doesn't like parser1 'a in the type ascription, who knows why *)
let id_suffix_complex (x: parser (parservals 'a emptyparservals)) =
  (* TODO: cancel id_basic capture to use it here *)
  let variant1 = collect_tuple (c (p "." `seq` alpha_lower `seq` (alnum_ext `rep` 0)) `cap` [])
  let variant2 = collect_tuple (c (p ".(") `seq` wsq `seq` collect_list (collect_tuple (x `seq` c (p ")"))))
  in variant1 `alt` variant2 `seq` wsq

(* TODO: bools aren't pattern matched rn. should they be? *)
let parse_bool = function | "true" -> Some true | "false" -> Some false | _ -> None
let term_bool: parser1 pterm = id_basic `actx` parse_bool `act` term_bool_fix
let term_id_shy: parser1 pterm = id_basic_shy `act` id_basic_fix
let term_id: parser1 pterm = id_basic `act` id_basic_fix
let term_cons: parser1 pterm = id_cons `act` id_cons_fix
let infix_op: parser1 pterm = id_infix `act` id_infix_fix
let prefix_op: parser1 pterm = id_prefix `act` id_prefix_fix
let suffix_op: parser1 pterm = id_suffix `act` id_suffix_fix
(* https://www.youtube.com/watch?v=T-BoDW1_9P4&t=11m3s *)
(* ^ this is kindof a mood throughout *)
(* specifically: complex suffix ops, pattern matching *)
let unzip xs = foldr (fun (l, r) (ls, rs) -> (l::ls, r::rs)) ([], []) xs
let fixsuffix f (h, rs) = let (args, parts) = unzip rs in (f (h, parts), args)
let suffix_complex_op x = id_suffix_complex x `act` fixsuffix id_suffix_complex_fix

let list_sequence (elem: parser (parservals 'a emptyparservals)) =
  let list_elements = comma_sep elem
  let list_tail = keysym "..." `seq` elem
  let list_alt_t = list_tail `act` (fun t -> ([], Some t))
  let list_alt_et = collect_tuple (list_elements `seq` opt (keysym "," `seq` list_tail))
  let list_body = list_alt_t `alt` list_alt_et
  in keysym "[" `seq` list_body `seq` keysym "]"

let record_sequence elem = keysym "{" `seq` comma_sep elem `seq` keysym "}"

(* Attempt to control variables usage in compiled lua *)
(* TODO: move this even higher and figure out the type errors *)
let syntax () =

  (* TODO: pattern matching seems to slow the parser way down. find out why and fix! *)
  let pat_ref: parser1 ppat = v "pat"
  let pat_paren = keysym "(" `seq` pat_ref `seq` keysym ")"

  let pat () =
    let pat_blank = keysym "_" `cap` pat_blank_fix

    let pat_bind = id_basic `act` pat_bind_basic_fix

    let pat_cons =
      let name = id_cons `act` IdentifierConstructor
      let args = keysym "(" `seq` comma_sep pat_ref `seq` keysym ")"
      let cons_args = collect_tuple (name `seq` args) `act` pat_cons_fix
      let cons_noargs = id_cons `act` pat_bind_cons_fix
      in cons_args `alt` cons_noargs

    let pat_list = list_sequence pat_ref `act` pat_list_fix

    let pat_record =
      let key = id_basic `act` IdentifierBasic
      let bind = collect_tuple (key `seq` keysym "=" `seq` pat_ref)
      in record_sequence bind `act` pat_record_fix

    in (
            pat_paren
      `alt` pat_blank
      `alt` pat_bind
      `alt` pat_cons
      `alt` pat_list
      `alt` pat_record
    )
  let pat = pat ()

  let pat_grammar = grammar { pat = pat } pat_ref

  let term_ref: parser1 pterm = v "term"
  let term_paren_shy = keysym "(" `seq` term_ref `seq` p ")"
  let term_paren = term_paren_shy `seq` wsq
  let term_definition = keysym "=" `seq` term_ref

  let abs_body =
    let args = keysym "(" `seq` comma_sep pat_grammar `seq` keysym ")"
    in collect_tuple (args `seq` term_definition) `act` term_abs_fix

  let define_sequence () =
    let define_simple =
      let pat = pat_grammar
      in collect_tuple (pat `seq` term_definition)

    let define_function =
      let left = id_basic `act` pat_bind_basic_fix
      in collect_tuple (left `seq` abs_body)

    let define_infix =
      let left = pat_grammar
      let op = id_infix `act` pat_bind_infix_fix
      let right = pat_grammar
      let fixup (l, op, r, body) = (op, term_abs_fix ([l, r], body))
      in collect_tuple (left `seq` op `seq` right `seq` term_definition) `act` fixup

    let define_prefix =
      let op = id_prefix `act` pat_bind_prefix_fix
      let right = pat_grammar
      let fixup (op, r, body) = (op, term_abs_fix ([r], body))
      in collect_tuple (op `seq` right `seq` term_definition) `act` fixup

    let define_suffix =
      let left = pat_grammar
      let op = id_suffix `act` pat_bind_suffix_fix
      let fixup (l, op, body) = (op, term_abs_fix ([l], body))
      in collect_tuple (left `seq` op `seq` term_definition) `act` fixup

    let define_suffix_complex =
      let left = pat_grammar
      let rights = id_suffix_complex pat_grammar `act` fixsuffix pat_bind_suffix_complex_fix
      let fixup (l, (op, rs), body) = (op, term_abs_fix (l::rs, body))
      in collect_tuple (left `seq` rights `seq` term_definition) `act` fixup

    in (
            define_simple
      `alt` define_function
      `alt` define_infix
      `alt` define_prefix
      `alt` define_suffix
      `alt` define_suffix_complex
    )
  let define_sequence = define_sequence ()

  let term_key () =
    let term_string =
      let chars_regular = c (star `excl` s "\n\r\"$\\")
      let chars_multiline = c (star `excl` (s "$\\" `alt` p "''"))
      let chars_triple = star `excl` p "'''"
      let escape_chars =
        foldl1 alt ((fun (s, r) -> lit s r) <$> [
          ("\\t", "\t"),
          ("\\n", "\n"),
          ("\\r", "\r"),
          ("\\\"", "\""),
          ("\\$", "$"),
          ("\\\\", "\\")
        ])
      (* This looks really weird because escape_chars provides a custom capture,
       * which can't be handled with a simple c (bad things happen) *)
      let string_body chars =
        let string_frag = collect_list (chars `alt` escape_chars `rep` 0) `act` foldl (^) ""
        let splice_frag = p "$" `seq` (term_id_shy `alt` term_paren_shy)
        let splice_list = collect_list (collect_tuple (splice_frag `seq` string_frag) `rep` 0)
        in collect_tuple (string_frag `seq` splice_list)
      let string_regular = p "\"" `seq` string_body chars_regular `seq` keysym "\""
      (* TODO: magic whitespace sensitivity? *)
      let string_multiline = p "''" `seq` string_body chars_multiline `seq` keysym "''"
      let string_triple_body = collect_tuple (c (chars_triple `rep` 0) `cap` [])
      let string_triple = p "'''" `seq` string_triple_body `seq` keysym "'''"
      in string_regular `alt` string_multiline `alt` string_triple `act` term_string_fix

    let term_list = list_sequence term_ref `act` term_list_fix

    let term_record =
      let unrepresentable (l, r) = match unfix l with
        | PatternBinding id -> Some (term_id_fix id, r)
        | _ -> None
      let record_bind1 = define_sequence `actx` unrepresentable
      let record_bind2 = collect_tuple (term_string `alt` term_paren `seq` term_definition)
      let record_bind = record_bind1 `alt` record_bind2
      in record_sequence record_bind `act` term_record_fix

    let term_abs = keyword "fun" `seq` abs_body

    let let_body =
      let fixup ((a, b), c) = (a, b, c)
      in collect_tuple (define_sequence `seq` keyword "in" `seq` term_ref) `act` fixup
    let term_let = keyword "let" `seq` let_body `act` term_let_fix
    let term_let_rec = keyword "let" `seq` keyword "rec" `seq` let_body `act` term_let_rec_fix

    let term_cond =
      let head = keyword "if" `seq` term_ref
      let body = keyword "then" `seq` term_ref
      let tail = keyword "else" `seq` term_ref
      in collect_tuple (head `seq` body `seq` tail) `act` term_cond_fix

    let term_match =
      let head = keyword "match" `seq` term_ref `seq` keyword "with"
      let body = collect_list (keysym "|" `seq` define_sequence `rep` 1)
      in collect_tuple (head `seq` body) `act` term_match_fix

    let term_hole = p "$?" `seq` opt (id_basic `act` IdentifierBasic) `act` term_hole_fix

    in (
            term_paren
      `alt` term_bool
      `alt` term_string
      `alt` term_list
      `alt` term_record
      `alt` term_abs
      `alt` term_let
      `alt` term_let_rec
      `alt` term_cond
      `alt` term_match
      `alt` term_hole
      `alt` term_id
      `alt` term_cons
    )
  let term_key = term_key ()

  (* Left-recursive parsers are hard >< *)
  (* The basic idea here is we're isolating each left-recursive parser
   * in a way where each parser can collect itself in a loop, and
   * higher-precedence parsers, but requires parens for lower-
   * -precedence parsers *)
  (* Incidentally, these are all function application of some kind. Go figure. *)

  let term () =
    let partial_argument t = (t `act` Some) `alt` (keysym "_" `cap` None)

    let app =
      (* cursed idea: _(arg) meta-partial function application *)
      let left = term_key
      let paren_app = keysym "(" `seq` comma_sep (partial_argument term_ref) `seq` keysym ")"
      let paren_rep = collect_list (paren_app `rep` 0)
      let app_ops = collect_tuple (left `seq` paren_rep)
      let fold (l, ps) = foldl (fun l p -> term_app_fix (l, p)) l ps
      in app_ops `act` fold

    let suffix_app =
      let left = partial_argument app
      (* hacky workaround to make sure suffix ops don't eat infix ops *)
      (* TODO: possibly causes a lot of backtracking, test this! *)
      let suffix1 = suffix_op `seq` neg term_ref `act` (fun x -> (x, []))
      let suffix2 = suffix_complex_op (partial_argument term_ref)
      let suffix = suffix1 `alt` suffix2
      let suffix_rep = collect_list (suffix `rep` 0)
      let suffix_ops = collect_tuple (left `seq` suffix_rep)
      let fold (l, ops) = foldl (fun l (op, args) -> Some (term_app_fix (op, l::args))) l ops
      in suffix_ops `actx` fold

    (* prefix ops aren't left recursive, but putting
     * them here is necessary for correct precedence *)
    let prefix_app =
      let right = partial_argument suffix_app
      let prefix_rep = collect_list (prefix_op `rep` 0)
      let prefix_ops = collect_tuple (prefix_rep `seq` right)
      let fold (ops, r) = foldr (fun op r -> Some (term_app_fix (op, [r]))) r ops
      in prefix_ops `actx` fold

    let infix_app =
      let left = partial_argument prefix_app
      let right = collect_tuple (infix_op `seq` left)
      let right_rep = collect_list (right `rep` 0)
      let infix_ops = collect_tuple (left `seq` right_rep)
      let fold (l, rs) = foldl (fun l (op, r) -> Some (term_app_fix (op, [l, r]))) l rs
      in infix_ops `actx` fold

    in infix_app
  let term = term ()

  in grammar { term = term } term_ref

let syntax = syntax ()
