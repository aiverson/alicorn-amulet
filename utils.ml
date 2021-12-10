
open import "amulet/option.ml"

let or_default x d = match x with | Some x -> x | None -> d
