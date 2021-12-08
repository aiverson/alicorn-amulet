open import "amulet/typeable.ml"
open import "prelude.ml"

let x = Dynamic 3

let f = Dynamic (fun x -> x + 1)

let arrow = type_of (Proxy @(->))

let binfunc = type_of (Proxy @(int -> int -> int))
