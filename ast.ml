
open import "amulet/typeable.ml"
open import "amulet/base.ml"
open import "amulet/category.ml"
open import "amulet/option.ml"

type idkind 'id =
| IdentifierBasic of 'id
| IdentifierConstructor of 'id
| IdentifierInfix of 'id
| IdentifierPrefix of 'id
| IdentifierSuffix of 'id
| IdentifierSuffixComplex of 'id * list 'id

type pattern 'id 'pat =
| PatternBlank
| PatternBinding of 'id
| PatternConstructor of 'id * list 'pat
| PatternList of list 'pat * option 'pat
(* TODO: strings and terms as keys? *)
| PatternRecord of list ('id * 'pat)

instance functor (pattern 'id)
  let f <$> p = match p with
  | PatternBlank -> PatternBlank
  | PatternBinding id -> PatternBinding id
  | PatternConstructor (id, args) -> PatternConstructor (id, f <$> args)
  | PatternList (ps, tl) -> PatternList (f <$> ps, f <$> tl)
  | PatternRecord tts -> PatternRecord ((second f) <$> tts)

type term 'id 'pat 'term =
| TermBool of bool
| TermString of string * list ('term * string) (* strings with splices *)
| TermList of list 'term * option 'term
| TermRecord of list ('term * 'term)
| TermIdentifier of 'id
| TermApplication of 'term * list (option 'term) (* single argument positional application, save named and optional arguments for later *)
(* | BracketOp of 'id *)
| TermAbstraction of list 'pat * 'term
| TermLet of 'pat * 'term * 'term
| TermLetRec of 'pat * 'term * 'term
(* | AsBinding of 'term * 'id * 'typ *)
| TermConditional of 'term * 'term * 'term
| TermHole of option 'id

instance functor (term 'id 'pat)
  let f <$> t = match t with
  | TermBool b -> TermBool b
  | TermString (s, ts) -> TermString (s, (first f) <$> ts)
  | TermList (ts, tl) -> TermList (f <$> ts, f <$> tl)
  | TermRecord tts -> TermRecord (f *** f <$> tts)
  | TermIdentifier i -> TermIdentifier i
  | TermApplication (t, ts) -> TermApplication (f t, (f <$>) <$> ts)
  (* | BracketOp i -> BracketOp i *)
  | TermAbstraction (v, t) -> TermAbstraction (v, f t)
  | TermLet (v, t, r) -> TermLet (v, f t, f r)
  | TermLetRec (v, t, r) -> TermLetRec (v, f t, f r)
  | TermConditional (c, i, e) -> TermConditional (f c, f i, f e)
  | TermHole i -> TermHole i

open import "prelude.ml"
open import "./hylo.ml"
open import "./utils.ml"
module Map = import "data/map.ml"

type pidk <- idkind string
type ppat <- fix (pattern pidk)
type pterm <- fix (term pidk ppat)

let rec intercalate s ss = match ss with
| Cons (a, Cons (b, tl)) -> a ^ s ^ intercalate s (Cons (b, tl))
| Cons (a, Nil) -> a
| Nil -> ""

let sep_commas xs = intercalate ", " xs

let matchingbracket = Map.from_list [("(|", "|)"), ("[|", "|]"), ("{|", "|}")]

let showid = function
  | IdentifierBasic id -> id
  | IdentifierConstructor id -> id
  | IdentifierInfix id -> "(_"^id^"_)"
  | IdentifierPrefix id -> "("^id^"_)"
  | IdentifierSuffix id -> "(_"^id^")"
  | IdentifierSuffixComplex (id, ids) -> "(_" ^ foldl (fun a x -> a ^ "_" ^ x) id ids ^ ")"

let show_list xs = "[" ^ sep_commas xs ^ "]"
let show_list_tail xs tl = "[" ^ sep_commas (xs ++ ["..."^tl]) ^ "]"
let show_record f kvs = "{" ^ sep_commas (map (fun (k, v) -> f k ^ " = " ^ v) kvs) ^ "}"

let showpat = cata (function
  | PatternBlank -> "_"
  | PatternBinding id -> showid id
  | PatternConstructor (id, args) -> showid id ^ " (" ^ sep_commas args ^ ")"
  | PatternList (ps, None) -> show_list ps
  | PatternList (ps, Some tl) -> show_list_tail ps tl
  | PatternRecord tts -> show_record showid tts
)

let showterm = cata (function
  | TermBool b -> show b
  | TermString (s, ts) -> "\"" ^ s ^ (map (fun (t, s) -> "$("^t^")"^s) ts |> foldl (^) "") ^ "\""
  | TermList (ts, None) -> show_list ts
  | TermList (ts, Some tl) -> show_list_tail ts tl
  | TermRecord tts -> show_record id tts
  | TermIdentifier name -> showid name
  (* TODO: prettier operators *)
  | TermApplication (f, xs) -> f ^ "(" ^ (map (`or_default` "_") xs |> sep_commas) ^ ")"
  (* TODO: prettier function definitions *)
  | TermAbstraction (pats, body) -> "(fun (" ^ sep_commas (showpat <$> pats) ^ ") = " ^ body ^ ")"
  | TermLet (pat, def, body) -> "let " ^ showpat pat ^ " = " ^ def ^ " in " ^ body
  | TermLetRec (pat, def, body) -> "let rec " ^ showpat pat ^ " = " ^ def ^ " in " ^ body
  | TermConditional (cond, cons, alt) -> "if " ^ cond ^ " then " ^ cons ^ " else " ^ alt
  | TermHole None -> "$?"
  | TermHole (Some id) -> "$?" ^ showid id
)

(* Fixed constructors *)
(* TODO: this is a massive hog of limited variables. figure something out! *)
let pat_blank_fix = Fix PatternBlank
let pat_bind_basic_fix x = Fix (PatternBinding (IdentifierBasic x))
let pat_bind_cons_fix x = Fix (PatternBinding (IdentifierConstructor x))
let pat_bind_infix_fix x = Fix (PatternBinding (IdentifierInfix x))
let pat_bind_prefix_fix x = Fix (PatternBinding (IdentifierPrefix x))
let pat_bind_suffix_fix x = Fix (PatternBinding (IdentifierSuffix x))
let pat_bind_suffix_complex_fix x = Fix (PatternBinding (IdentifierSuffixComplex x))
let pat_cons_fix x = Fix (PatternConstructor x)
let pat_list_fix x = Fix (PatternList x)
let pat_record_fix x = Fix (PatternRecord x)
let term_id_fix x = Fix (TermIdentifier x)
let id_basic_fix x = Fix (TermIdentifier (IdentifierBasic x))
let id_cons_fix x = Fix (TermIdentifier (IdentifierConstructor x))
let id_infix_fix x = Fix (TermIdentifier (IdentifierInfix x))
let id_prefix_fix x = Fix (TermIdentifier (IdentifierPrefix x))
let id_suffix_fix x = Fix (TermIdentifier (IdentifierSuffix x))
let id_suffix_complex_fix x = Fix (TermIdentifier (IdentifierSuffixComplex x))
let term_bool_fix x = Fix (TermBool x)
let term_string_fix x = Fix (TermString x)
let term_list_fix x = Fix (TermList x)
let term_record_fix x = Fix (TermRecord x)
let term_app_fix x = Fix (TermApplication x)
let term_abs_fix x = Fix (TermAbstraction x)
let term_let_fix x = Fix (TermLet x)
let term_let_rec_fix x = Fix (TermLetRec x)
let term_cond_fix x = Fix (TermConditional x)
let term_hole_fix x = Fix (TermHole x)
