open import "data/array.ml"
(* horrible hack to make it look like an array with minimal bs *)
external val arg : array string = "{ [1] = { length = #arg, backing = arg } }"
