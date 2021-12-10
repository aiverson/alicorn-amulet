
open import "./lpeg.ml"
open import "prelude.ml"

let nsepseq pat sep = pat `seq` (sep `seq` pat `rep` 0)
let sepseq pat sep = nsepseq pat sep `rep` -1

let ws = s " \t\n\r"
let wsp = ws `rep` 1
let wsq = ws `rep` 0

let int_parser  = s "+-" `rep` -1 `seq` (r "09" `rep` 1) `cx` parse_int
let float_parser  = s "+-" `rep` -1 `seq` (r "09" `rep` 1) `seq` (p "." `seq` (r"09" `rep` 1 `seq` (s "eE" `seq` (s"+-" `rep` -1) `seq` (r "09" `rep` 1) `rep` -1) `rep` -1) `rep` -1) `cx` parse_float

let lit text value = c (p text) `act` const value
