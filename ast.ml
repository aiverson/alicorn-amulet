
open import "amulet/typeable.ml"
open import "amulet/base.ml"
open import "amulet/category.ml"
open import "amulet/option.ml"

type idstyle 'id =
| IdentifierBasic of 'id
| IdentifierConstructor of 'id
| IdentifierInfix of 'id
| IdentifierPrefix of 'id
| IdentifierSuffix of 'id
| IdentifierSuffixComplex of 'id * list 'id

instance show (idstyle string)
  let show = function
  | IdentifierBasic id -> id
  | IdentifierConstructor id -> id
  | IdentifierInfix id -> "(_" ^ id ^ "_)"
  | IdentifierPrefix id -> "(" ^ id ^ "_)"
  | IdentifierSuffix id -> "(_" ^ id ^ ")"
  | IdentifierSuffixComplex (id, ids) ->
    let rec foldl f a = function | Nil -> a | Cons (x, xs) -> foldl f (f a x) xs
    in "(_" ^ foldl (fun a x -> a ^ "_" ^ x) id ids ^ ")"

type term 'id 'term =
| LiteralBool of bool
| StringCons of string * list ('term * string) (* strings with splices *)
| ListCons of list 'term
| RecordCons of list ('term * 'term)
| Identifier of idstyle 'id
| Application of 'term * list (option 'term) (* single argument positional application, save named and optional arguments for later *)
(* | BracketOp of 'id *)
(* TODO: pattern-matching type for arguments and let binding *)
| Abstraction of list 'id * 'term
| LetBinding of idstyle 'id * 'term * 'term
| LetRecBinding of idstyle 'id * 'term * 'term
(* | AsBinding of 'term * 'id * 'typ *)
| Conditional of 'term * 'term * 'term
| Hole of 'id

instance functor (term 'id)
  let f <$> t = match t with
  | LiteralBool b -> LiteralBool b
  | StringCons (s, ts) -> StringCons (s, (first f) <$> ts)
  | ListCons ts -> ListCons (f <$> ts)
  | RecordCons tts -> RecordCons (f *** f <$> tts)
  | Identifier i -> Identifier i
  | Application (t, ts) -> Application (f t, (f <$>) <$> ts)
  (* | BracketOp i -> BracketOp i *)
  | Abstraction (v, t) -> Abstraction (v, f t)
  | LetBinding (v, t, r) -> LetBinding (v, f t, f r)
  | LetRecBinding (v, t, r) -> LetRecBinding (v, f t, f r)
  | Conditional (c, i, e) -> Conditional (f c, f i, f e)
  | Hole i -> Hole i

let () = ()
