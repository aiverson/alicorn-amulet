open import "prelude.ml"
open import "./parsing/lpeg.ml"
open import "./hylo.ml"

type tree 'prim 'func 'tree =
| Leaf of 'prim
| Node of 'prim * ('func 'tree)
type tree_fix <- fix (tree string list)
let leaf_fix x = Fix (Leaf x)
let node_fix xy = Fix (Node xy)

let any x = x `rep` 0
let many x = x `rep` 1
let excl l r = neg r `seq` l

let ws = r "\t\r" `alt` s " "
let wsq = any ws
let key x = p x `seq` wsq
let paren = s "()"
let primchar = star `excl` (ws `alt` paren)

let paren_expr =
  let paren_ref: parser1 tree_fix = v "paren"
  let prim = c (many primchar) `seq` wsq
  let paren_leaf = prim `act` leaf_fix
  let paren_body = collect_tuple (prim `seq` collect_list (any (paren_leaf `alt` paren_ref))) `act` node_fix
  let paren_node = key "(" `seq` paren_body `seq` key ")"
  in grammar { paren = paren_node } paren_ref

instance functor 'func => functor (tree 'prim 'func)
  let f <$> t = match t with
  | Leaf x -> Leaf x
  | Node (x, xs) -> Node (x, f <$> xs)

let show_tree (t: fix (tree string list)) = cata (function
  | Leaf x -> x
  | Node (x, xs) -> "(" ^ x ^ (foldl (fun a x -> a ^ " " ^ x) "" xs) ^ ")"
                                           ) t

let Some t = parse paren_expr "(woah hello (there i have) something (to see here (i think)) perhaps?)"
let () = put_line (show_tree t)
