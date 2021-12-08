
open import "./types.ml"
open import "prelude.ml"
open import "amulet/exception.ml"
open import "amulet/typeable.ml"
open import "data/map.ml"


(* convenience tool for giving values we have in amulet to alicorn *)
class typeable 'a => alicorn_literal 'a
 val lit_of: 'a -> dynamic * altype
 val altype_of : proxy 'a -> altype

instance alicorn_literal bool
  let lit_of b = (Dynamic b, Bool)
  let altype_of Proxy = Bool

instance alicorn_literal 'a * alicorn_literal 'b => alicorn_literal ('a -> 'b)
  let altype_of Proxy = Func (altype_of (Proxy: proxy 'a), altype_of (Proxy: proxy 'a))
  let lit_of f = (Dynamic f, altype_of (Proxy: proxy ('a -> 'b)))

(* define AST-style terms *)
(* the term type we get from reading the syntax in with optional type annotations *)
type part_typed_term =
| UAbstraction of int * part_typed_term
| Abstraction of int * part_typed_term * altype
| UApplication of part_typed_term * part_typed_term
| Application of part_typed_term * part_typed_term * altype
| UVariable of int
| Variable of int * altype
| UDePair of int * int * part_typed_term * part_typed_term
| DePair of int * int * part_typed_term * part_typed_term * altype
| UPair of part_typed_term * part_typed_term
| Pair of part_typed_term * part_typed_term * altype
| ULit of dynamic
| Lit of dynamic * altype

(* the fully typed terms we can have after type inference *)
type typed_term =
| Abstraction of int * typed_term * altype
| Application of typed_term * typed_term * altype
| Variable of int * altype
| DePair of int * int * typed_term * typed_term * altype
| Pair of typed_term * typed_term * altype
| Lit of dynamic * altype

(* terms with all types erased *)
type untyped_term =
| UAbstraction of int * untyped_term
| UApplication of untyped_term * untyped_term
| UVariable of int
| UDePair of int * int * untyped_term * untyped_term
| UPair of untyped_term * untyped_term
| ULit of dynamic

(* erase the types *)
let untyped_term_of_typed_term =
  let rec ut = function
  | Abstraction (v, r, _) -> UAbstraction (v, ut r)
  | Application (f, x, _) -> UApplication (ut f, ut x)
  | Variable (v, _) -> UVariable v
  | DePair (v1, v2, v, r, _) -> UDePair (v1, v2, ut v, ut r)
  | Pair (t1, t2, _) -> UPair (ut t1, ut t2)
  | Lit (x, _) -> ULit x
  ut

(* definition of interaction networks *)

(* a reference to a particular slot in a node *)
type slot 'node <- 'node * int
type slotref 'node <- ref ('node * int)

(* untyped interaction network nodes *)
type ut_node =
| Lam of (slotref ut_node) * (slotref ut_node) * (slotref ut_node)
| Dup of (slotref ut_node) * (slotref ut_node) * (slotref ut_node)
| ForeignCall of (slotref ut_node) * (slotref ut_node) * dynamic
| ForeignVal of (slotref ut_node) * dynamic
| Unbound

let unbound_slot() = ref (Unbound, 0)

(* find the slotref linked to a given slotref *)
let local_ref r = match r with
| (Lam (r', _, _), 0) -> r'
| (Lam (_, r', _), 1) -> r'
| (Lam (_, _, r'), 2) -> r'
| (Dup (r', _, _), 0) -> r'
| (Dup (_, r', _), 1) -> r'
| (Dup (_, _, r'), 2) -> r'
| (ForeignCall (r', _, _), 0) -> r'
| (ForeignCall (_, r', _), 1) -> r'
| (ForeignVal (r', _), 0) -> r'
| _ -> throw @@ Invalid "tried to get the ref at a slot that doesn't exist"

let linked_ref r = local_ref !r


let link_slots s1 s2 =
  local_ref s2 := s1
  local_ref s1 := s2

(* given an untyped term ast, convert it into an untyped interaction network *)
(* let rec utnet_of_utterm (t: untyped_term) (env: Map.t int (slot ut_node))  = match t with
 * | ULit x -> Some ((Val (unbound_slot(), x), 0), Map.empty)
 * | UAbstraction (v, r) ->
 *   let param = unbound_slot ()
 *   utnet_of_utterm r (env.(v)<- param )
 *   >>= fun (ret, renv) ->
 *     let arg = unbound_slot()
 *     let node = Lam (unbound_slot(), arg, ret)
 *     let () = link_slots (node, 1) renv.(v)
 *     Some ((node, 0), renv) *)

module Hacks = import "./hacks.ml"

let eligible_for_rewrite node = match !(local_ref (node, 0)) with
| (_, 0) -> true
| _ -> false

let rewrite_node node = match (node, let (x, _) = !(local_ref (node, 0)) in x) with
(* first the annihilation cases *)
| Lam (_, arg, res), Lam (_, param, ret) ->  (* calling a function *)
  link_slots !(linked_ref arg) !(linked_ref param) (* link the argument of the call to the parameter of the function *)
  link_slots !(linked_ref res) !(linked_ref ret)   (* link the return of the function to the result of the call *)
  (* the function node and the call node annihilate *)
| Dup (_, v1, v2), Dup (_, x1, x2) ->    (* destructuring a pair *)
  link_slots !(linked_ref v1) !(linked_ref x1) (* link the first value of the pair with the first variable of the destructuring *)
  link_slots !(linked_ref v2) !(linked_ref x2) (* link the second value of the pair with the second variable of the destructuring *)
  (* the pair construction and destruction annihilate *)
(* next the commutation cases *)
| (Lam (_, arg, res)) as c1, (Dup (_, f1, f2)) as d1 -> (* calling a pair of functions on the same argument *)
  (* create the new nodes of the commutation *)
  let c2 = Lam (unbound_slot(), unbound_slot(), unbound_slot()) (* a second call node for the second function call*)
  let d2 = Dup (unbound_slot(), unbound_slot(), unbound_slot()) (* node for duplicating the argument to both calls *)
  (* fetch the far side of the connections *)
  let arg' = !(linked_ref arg)
  let res' = !(linked_ref res)
  let f1' = !(linked_ref f1)
  let f2' = !(linked_ref f2)
  link_slots arg' (d2, 0) (* connect the newly created duplication node to the argument *)
  link_slots (c1, 1) (d2, 1) (* connect one of the duplicated copies of the argument to the argument of the first call *)
  link_slots (c2, 1) (d2, 2) (* connnect the other duplicated copy of the argument to the argument of the second call *)
  link_slots res' (d1, 0) (* the function pair node is reused to pair up the results of the calls *)
  link_slots (c1, 2) (d1, 1) (* the first entry of the pair is the result of the first call *)
  link_slots (c2, 2) (d1, 2) (* the second entry of the pair is the result of the second call *)
  link_slots f1' (c1, 0) (* the original call node is reused as the call of the first function in the pair *)
  link_slots f2' (c2, 0) (* the new call node is connected to the second function in the pair *)
| (Dup (_, use1, use2)) as d1, (Lam (_, param, ret)) as l1 -> (* Duplicating a function *)
  (* create the new nodes of the commutation *)
  let l2 = Lam (unbound_slot(), unbound_slot(), unbound_slot()) (* a second lambda node for the newly created function *)
  let d2 = Dup (unbound_slot(), unbound_slot(), unbound_slot()) (* node for duplicating the argument to both calls *)
  (* fetch the far side of the connections *)
  let param' = !(linked_ref param)
  let ret' = !(linked_ref ret)
  let use1' = !(linked_ref use1)
  let use2' = !(linked_ref use2)
  link_slots param' (d2, 0) (* connect the usages of the parameter of the original function to a pair of the two new parameters for parallel evaluation *)
  link_slots (l1, 1) (d2, 1) (* connect the parameter of one of the new functions to the first value of the pair, reusing the original lambda node *)
  link_slots (l2, 1) (d2, 2) (* connnect the parameter of the other new function to the second value of the pair, using the new node *)
  link_slots ret' (d1, 0) (* unpair the results of the parallel evaluation *)
  link_slots (l1, 2) (d1, 1) (* and send the first result to the first function *)
  link_slots (l2, 2) (d1, 2) (* and send the second result to the second function *)
  link_slots use1' (l1, 0) (* connect the first lambda node to the first usage *)
  link_slots use2' (l2, 0) (* connect the second lambda node to the second usage *)
(* finally, the foreign value cases *)
| Lam (_, arg, res), ForeignVal (_, f) -> (* Call a foreign value which is hopefully a function, transmute into a ForeignCall node to cause reduction of the argument *)
  let call = ForeignCall (unbound_slot(), unbound_slot(), f)
  link_slots !(linked_ref arg) (call, 0) (* link the argument of the original call with the argument slot of the foreign call node. *)
  link_slots !(linked_ref res) (call, 1) (* link the result of the foreign call the the usage of the original call's result *)
  (* the original lambda and foreign value nodes are destroyed *)
| Dup (_, use1, use2), (ForeignVal (_, x)) as orig -> (* duplicating a foreign value *)
  let copy = ForeignVal (unbound_slot(), x)
  link_slots !(linked_ref use1) (orig, 0) (* connect the original value to the first usage *)
  link_slots !(linked_ref use2) (copy, 0) (* connect the copied value to the second usage *)
  (* the original duplication node is destroyed *)
| (ForeignCall(_, res, f)) as call1, (Dup(_, arg1, arg2)) as d -> (* foreign call on a pair *)
  let res' = !(linked_ref res)
  let call2 = ForeignCall(unbound_slot(), unbound_slot(), f)
  link_slots !(linked_ref arg1) (call1, 0)
  link_slots !(linked_ref arg2) (call2, 0)
  link_slots (d, 1) (call1, 1)
  link_slots (d, 2) (call2, 1)
  link_slots (d, 0) res'
| ForeignCall(_, res, f), ForeignVal(_, x) -> (* call a foreign function with a foreign value, resulting in a foreign value *)
  let yq = Hacks.dynamic_call f x
  match yq with
  | Some y -> (* the types matched so the call happened *)
    let yn = ForeignVal (unbound_slot(), y)
    link_slots !(linked_ref res) (yn, 0)
    (* the original foreign call and foreign value are destroyed *)
  | None -> throw @@ Invalid "a foreign call with mismatched types was found during rewriting"
| ForeignVal (_, f), Lam (_, arg, res) -> (* Call a foreign value which is hopefully a function, transmute into a ForeignCall node to cause reduction of the argument *)
  let call = ForeignCall (unbound_slot(), unbound_slot(), f)
  link_slots !(linked_ref arg) (call, 0) (* link the argument of the original call with the argument slot of the foreign call node. *)
  link_slots !(linked_ref res) (call, 1) (* link the result of the foreign call the the usage of the original call's result *)
  (* the original lambda and foreign value nodes are destroyed *)
| (ForeignVal (_, x)) as orig, Dup (_, use1, use2) -> (* duplicating a foreign value *)
  let copy = ForeignVal (unbound_slot(), x)
  link_slots !(linked_ref use1) (orig, 0) (* connect the original value to the first usage *)
  link_slots !(linked_ref use2) (copy, 0) (* connect the copied value to the second usage *)
  (* the original duplication node is destroyed *)
| (Dup(_, arg1, arg2)) as d, (ForeignCall(_, res, f)) as call1 -> (* foreign call on a pair *)
  let res' = !(linked_ref res)
  let call2 = ForeignCall(unbound_slot(), unbound_slot(), f)
  link_slots !(linked_ref arg1) (call1, 0)
  link_slots !(linked_ref arg2) (call2, 0)
  link_slots (d, 1) (call1, 1)
  link_slots (d, 2) (call2, 1)
  link_slots (d, 0) res'
| ForeignVal(_, x), ForeignCall(_, res, f) -> (* call a foreign function with a foreign value, resulting in a foreign value *)
  let yq = Hacks.dynamic_call f x
  match yq with
  | Some y -> (* the types matched so the call happened *)
    let yn = ForeignVal (unbound_slot(), y)
    link_slots !(linked_ref res) (yn, 0)
    (* the original foreign call and foreign value are destroyed *)
  | None -> throw @@ Invalid "a foreign call with mismatched types was found during rewriting"

(* lastly the error cases *)
| Lam _, ForeignCall _ -> throw @@ Invalid "found a lambda head to head with a foreign call during rewriting"
| ForeignCall _, Lam _ -> throw @@ Invalid "found a lambda head to head with a foreign call during rewriting"
| ForeignCall _, ForeignCall _ -> throw @@ Invalid "two head to head foreign calls found during rewriting"
| ForeignVal _, ForeignVal _ -> throw @@ Invalid "two head to head foreign values found during rewriting"
| Unbound, _ -> throw @@ Invalid "an unbound slot was found during rewriting"
| _, Unbound -> throw @@ Invalid "an unbound slot was found during rewriting"
