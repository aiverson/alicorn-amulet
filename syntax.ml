
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

let escapechars = lit "\\n" "\n" `alt` lit "\\t" "\t"
(* TODO: fix this *)
(*
let stringfrag = cs (((neg @@ s "\"$\\") `seq` star `alt` escapechars `rep` 0))
*)

let num = r "09"
let alpha_upper = r "AZ"
let alpha_lower = r "az"
let alpha = alpha_upper `alt` alpha_lower
let alnum = alpha `alt` num
let alnum_ext = alnum `alt` p "_"

let keyword str = p str `seq` wsp
let keysym str = p str `seq` wsq
(* TODO: that wsp is sus, what about a tailgating operator? *)
let literal_bool: parser1 pterm = lit "true" true `alt` lit "false" false `act` LiteralBool `act` Fix `seq` wsp
(* TODO: is wsq correct? *)
let identifier = c (alpha_lower `seq` (alnum_ext `rep` 0)) `act` Identifier `act` Fix `seq` wsq
(* TODO: metaprogram this away *)
let string_cons: parser1 pterm = v "string_cons"
let list_cons: parser1 pterm = v "list_cons"
let record_cons: parser1 pterm = v "record_cons"
let term: parser1 pterm = v "term"

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
    list_cons = keysym "[" `seq` collect_list (sepseq term (keysym ",")) `seq` keysym "]" `act` ListCons `act` Fix
  , record_cons =
      let record_key = identifier `alt` (* string_cons `alt` *) (keysym "(" `seq` term `seq` keysym ")")
      let record_pair = collect_tuple (record_key `seq` keysym "=" `seq` term)
      in keysym "{" `seq` collect_list (sepseq record_pair (keysym ",")) `seq` keysym "}" `act` RecordCons `act` Fix
  , term = literal_bool `alt` (* string_cons `alt` *) list_cons `alt` record_cons `alt` identifier
  } term

let foo = 0
