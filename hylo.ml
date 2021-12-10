
open import "prelude.ml"

type fix 'f = Fix of 'f (fix 'f)
let unfix (Fix x) = x

type coalgebra 'f 'a <- functor 'f => 'a -> 'f 'a
type algebra 'f 'a <- functor 'f => 'f 'a -> 'a

let rec cata: forall 'f 'a. functor 'f => algebra 'f 'a -> fix 'f -> 'a = fun f xs -> unfix xs |> map (cata f) |> f
let rec ana: forall 'f 'a. functor 'f => coalgebra 'f 'a -> 'a -> fix 'f = fun f x -> Fix @@ map (ana f) @@ f x
