
open import "amulet/typeable.ml"
open import "amulet/base.ml"
open import "amulet/category.ml"
open import "amulet/option.ml"


type term 'id 'term =
| LiteralBool of bool
| StringCons of string * list ('term * string) (* strings with splices *)
| ListCons of list 'term
| RecordCons of list ('term * 'term)
| Identifier of 'id
| Application of 'term * list (option 'term) (* single argument positional application, save named and optional arguments for later *)
(* | BracketOp of 'id *)
| InfixOp of option 'term * 'id * option 'term
| PrefixOp of 'id * option 'term
| SuffixOp of option 'term * 'id
| Abstraction of list 'id * 'term
| LetBinding of 'id * 'term * 'term
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
  | InfixOp (a, i, b) -> InfixOp (f <$> a, i, f <$> b)
  | PrefixOp (i, b)   -> PrefixOp (i, f <$> b)
  | SuffixOp (a, i)   -> SuffixOp (f <$> a, i)
  | Abstraction (v, t) -> Abstraction (v, f t)
  | LetBinding (v, t, r) -> LetBinding (v, f t, f r)
  | Conditional (c, i, e) -> Conditional (f c, f i, f e)
  | Hole i -> Hole i

let () = ()
