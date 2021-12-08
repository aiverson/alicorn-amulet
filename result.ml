
open import "prelude.ml"

type result 'a 'b =
| Ok of 'a
| Err of 'b

let bool_of_result = function | Ok _ -> true | Err _ -> false

let map_ok f = function | Ok x -> Ok (f x) | Err x -> Err x
let map_err f = function | Ok x -> Ok x | Err x -> Err (f x)

let res_join rs = foldr (fun (a: result 'a 'b) (b: result (list 'a) 'b) ->
    match (a, b) with
    | (Ok a, Ok b) -> Ok (a :: b)
    | (_, Err b) -> Err b
    | (Err a, _) -> Err a
                        ) (Ok []) rs

let res_partition rs = foldr (fun a (successes, fails) -> match a with | Ok x -> (x :: successes, fails) | Err x -> (successes, x :: fails)) ([], []) rs

let res_and s f1 f2 a b = match (a, b) with
| (Ok r1 , Ok r2)  -> Ok  @@ s (r1, r2)
| (Ok _  , Err r2) -> Err @@ f2 r2
| (Err r1, _)      -> Err @@ f1 r1

let res_or s1 s2 f a b = match (a, b) with
| (Ok  r1, _)      -> Ok  @@ s1 r1
| (Err _, Ok r2)   -> Ok  @@ s2 r2
| (Err r1, Err r2) -> Err @@ f (r1, r2)
