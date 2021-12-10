
private module S = import "lua/string.ml"
open import "prelude.ml"
open import "amulet/exception.ml"

type subject = private Subject of string * int

let emptysubj = Subject ("", 1)

type presult 'a =
| Fail of subject * list string * string
| Partial of subject -> presult 'a
| Done of subject * 'a

type parser 'a = private Parser of (subject -> presult 'a)

instance functor presult
  let f <$> r = match r with
  | Fail s -> Fail s
  | Partial cont -> Partial (fun subj -> f <$> cont subj)
  | Done (subj, x) -> Done (subj, f x)

(* instance applicative presult
 *   let pure f = Done (emptysubj, f)
 *   let f' <*> x' = match f' with
 *   | Fail s -> Fail s
 *   | Partial cont -> match x' with
 *     | Fail s -> Fail s *)

(* instance monad presult
 *   let r >>= f = match r with
 *   | Fail s -> Fail s
 *   | Done (subj) *)

let parse (Parser f) str = f (Subject (str, 1))
let feed r str = match r with
| Fail s -> Fail s
| Partial cont -> cont (Subject (str, 1))
| Done d -> Done d
let parseOnly (Parser f) str = match f (Subject (str, 1)) with
| Fail (_, _, err) -> Left err
| Partial cont -> match cont emptysubj with
  | Fail (_, _, err) -> Left err
  | Done d -> Right d
  | Partial _ -> throw (Invalid "broken parser failed to terminate when resumed with empty input")
| Done d -> Right d

let anyChar =
  Parser (fun subj ->
    let Subject (s, p) = subj
    if p + 1 <= S.length s then
      Done (Subject(s, p + 1), S.substring s p p)
    else
      Partial (fun subj ->
        let Subject (s, p) = subj
        if S.length s > 0 then
          Done (Subject(s, p + 1), S.substring s p p)
        else
          Fail (subj, [], "end of subject when expecting a character")))

let satisfy pred =
  Parser (fun subj ->
    let Subject (s, p) = subj
    if p + 1 <= S.length s then
      let c = S.substring s p p
      if pred c then
        Done (Subject(s, p + 1), c)
      else
        Fail (subj, [], "character at point doesn't satisfy predicate")
    else
      Partial (fun subj ->
        let Subject (s, p) = subj
        if S.length s > 0 then
          let c = S.substring s p p
          if pred c then
            Done (Subject(s, p + 1), c)
          else
            Fail (subj, [], "character at point doesn't satisfy predicate")
        else
          Fail (subj, [], "end of subject when expecting a character")))

let satisfyWith f pred =
  Parser (fun subj ->
    let Subject (s, p) = subj
    if p + 1 <= S.length s then
      let c = f (S.substring s p p)
      if pred c then
        Done (Subject(s, p + 1), c)
      else
        Fail (subj, [], "character at point doesn't satisfy predicate")
    else
      Partial (fun subj ->
        let Subject (s, p) = subj
        if S.length s > 0 then
          let c = f @@ S.substring s p p
          if pred c then
            Done (Subject(s, p + 1), c)
          else
            Fail (subj, [], "character at point doesn't satisfy predicate")
        else
          Fail (subj, [], "end of subject when expecting a character")))

let string str =
  let strlen = S.length str
  Parser (fun subj ->
    let Subject (s, p) = subj
    let slen = (S.length s) - p + 1
    if strlen > slen - p + 1 then
      if S.substring s p (p + strlen) == str then
        Done (Subject (s, p + strlen), str)
      else Fail (subj, [], "string didn't match section of subject at point")
    else if S.substring 1 slen ==
)
