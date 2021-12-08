
open import "prelude.ml"
open import "data/index.ml"
open import "./result.ml"
module Map = import "data/map.ml"
module Set = import "data/set.ml"

type altype =
(* elementary type constructors for basic types; form a poset *)
| Bool
| Func of altype * altype
| Prod of altype * altype
| Record of Map.t string altype
(* Top and bottom are needed to make the types form a bounded poset *)
| Top
| Bottom
(* Add meet and join to make it form a distributive lattice
 * meet and join are explicitly represented in the type sytem so that the lattice is fully distributive, which is important.
 * Not all will be inhabited, but that doesn't mean they aren't sensible types, and the algebra requires them to be representable.
 * Where the meet or join of types represents a compact type of some other primitive kind, they will be converted to that other type constructor during normalization or output.
 * Algebraically, the structure requires it to contain finite meets and joins; all lists in amulet are finite. *)
| Meet of altype * altype (* greatest lower bound, least specific common subtype *)
| Join of altype * altype (* least upper bound, most specific common supertype *)
(* type variables must exist as types different from every other type in order for open world type assignment to work
 * integer index is used for making them unique, names will be summoned from the graph context by the pretty printer
 * This also allows backtracing the process of unification efficiently to ask why things have specific types *)
| TypeVar of int
(* Recursive types fulfill the Profinite Distributive Lattice we need
 * Recursive types are represented with a variable ID and a type that variable is free in
 * Recursive types must be guarded, any instance of the recursive type variable must be inside a function type, product type, or record type
 * this ensures the uniqueness of the fixed point *)
| RecursiveType of int * altype

(* helper function to verify a predicate across all fields of a record and explain the results *)
let record_fields_are pred fields =
  let (successes, failures) = res_partition @@ map (fun (k, r) -> map_ok (k,) @@ map_err (k,) r) @@ Map.assocs @@ map pred fields
  if length failures == 0 then
    Ok @@ Map.from_list successes
  else
    Err @@ Map.from_list failures

(* explanations of success and failure for checking if a type is guarded *)
type guarded_success =
| GuardedBool
| GuardedFunc of guarded_success * guarded_success
| GuardedProd of guarded_success * guarded_success
| GuardedRecord of Map.t string guarded_success
| GuardedTop
| GuardedBottom
| GuardedMeet of guarded_success * guarded_success
| GuardedJoin of guarded_success * guarded_success
| GuardedTypeVar of int
| GuardedRecursive of int * guarded_success
type guarded_fail =
| GuardedFuncF1 of guarded_fail
| GuardedFuncF2 of guarded_fail
| GuardedProdF1 of guarded_fail
| GuardedProdF2 of guarded_fail
| GuardedRecordF of Map.t string guarded_fail
| GuardedMeetF1 of guarded_fail
| GuardedMeetF2 of guarded_fail
| GuardedJoinF1 of guarded_fail
| GuardedJoinF2 of guarded_fail
| GuardedTypeVarF of int
| GuardedRecursiveF of int * guarded_fail

let rec is_guarded (t: altype) : result guarded_success guarded_fail = match t with
| Bool -> Ok GuardedBool
| Func (a, b) -> res_and GuardedFunc GuardedFuncF1 GuardedFuncF2 (is_guarded a) (is_guarded b)
| Prod (a, b) -> res_and GuardedProd GuardedProdF1 GuardedProdF2 (is_guarded a) (is_guarded b)
| Record m -> record_fields_are is_guarded m |> map_ok GuardedRecord |> map_err GuardedRecordF
| Top -> Ok GuardedTop
| Bottom -> Ok GuardedBottom
| Meet (a, b) -> res_and GuardedMeet GuardedMeetF1 GuardedMeetF2 (is_guarded a) (is_guarded b)
| Join (a, b) -> res_and GuardedJoin GuardedJoinF1 GuardedJoinF2 (is_guarded a) (is_guarded b)
| TypeVar v -> Ok @@ GuardedTypeVar v
| RecursiveType (v, t') -> is_guarded_wrt v t' |> map_ok (GuardedRecursive % (v,)) |> map_err (GuardedRecursiveF % (v,))
(* | RecursiveType (v, t') *)
and is_guarded_wrt (v: int) (t: altype): result guarded_success guarded_fail = match t with
| TypeVar v' -> if v == v' then Err @@ GuardedTypeVarF v' else Ok @@ GuardedTypeVar v'
| Meet (a, b) -> res_and GuardedMeet GuardedMeetF1 GuardedMeetF2 (is_guarded_wrt v a) (is_guarded_wrt v b)
| Join (a, b) -> res_and GuardedJoin GuardedJoinF1 GuardedJoinF2 (is_guarded_wrt v a) (is_guarded_wrt v b)
| _ -> is_guarded t

(* explanations of success and failure for if some type is a subtype of another *)
type subtype_success =
| PrimRefl of altype
| TopSuccess
| BottomSuccess
| FuncSuccess of subtype_success * subtype_success
| ProdSuccess of subtype_success * subtype_success
| RecordSuccess of Map.t string subtype_success
| MeetSuccessR of subtype_success * subtype_success
| JoinSuccessR1 of subtype_success
| JoinSuccessR2 of subtype_success
| MeetSuccessL1 of subtype_success
| MeetSuccessL2 of subtype_success
| JoinSuccessL of subtype_success * subtype_success
| TypeVarMatch of int

type subtype_fail =
| FuncFail1 of subtype_fail
| FuncFail2 of subtype_fail
| ProdFail1 of subtype_fail
| ProdFail2 of subtype_fail
| RecordFailAt of Map.t string subtype_fail
| RecordFailMissing of Set.t string
| MeetFailR1 of subtype_fail
| MeetFailR2 of subtype_fail
| JoinFailR of subtype_fail * subtype_fail
| MeetFailL of subtype_fail * subtype_fail
| JoinFailL1 of subtype_fail
| JoinFailL2 of subtype_fail
| NoRelFail of altype * altype
| NYI_FIXME_Fail of altype * altype

let rec subtype (a: altype) (b: altype): result subtype_success subtype_fail = match (a, b) with
(* first the subtyping relations within a type family *)
| (Bool, Bool) -> Ok (PrimRefl Bool)
| (Func (in1, out1), Func (in2, out2)) ->
  res_and FuncSuccess FuncFail1 FuncFail2 (subtype in2 in1) (subtype out1 out2)
  (* match (subtype in2 in1, subtype out1 out2) with
   * | (Ok r1, Ok r2) -> Ok @@ FuncSuccess (r1, r2)
   * | (Ok _, Err r2) -> Err @@ FuncFail2 r2
   * | (Err r1, _) -> Err @@ FuncFail1 r1 *)
| (Prod (a1, b1), Prod(a2, b2)) ->
  match (subtype a1 a2, subtype b1 b2) with
  | (Ok r1, Ok r2) -> Ok @@ ProdSuccess (r1, r2)
  | (Ok _, Err r2) -> Err @@ ProdFail2 r2
  | (Err r1, _) -> Err @@ ProdFail1 r1
| (Record left, Record right) ->
  let left_only = Map.difference left right (* fields that are only in the left record, there must be none of these *)
  (*let right_only = Map.difference right left*) (* fields that are only in the right record, there is no restriction on these *)
  let common = Map.intersection left right (* fields common to both records must fulfill the subtyping relation *)
  let (common_success, common_fail) = res_partition (map (fun k -> map_ok (k,) @@ map_err (k,) @@ subtype (left.(k)) (right.(k))) (Map.keys common))
  if length left_only == 0 then
    if length common_fail == 0 then
      Ok @@ RecordSuccess (Map.from_list common_success)
    else
      Err @@ RecordFailAt (Map.from_list common_fail)
  else Err @@ RecordFailMissing (Set.from_list @@ Map.keys left_only)

(* next for top and bottom *)
| (_, Top) -> Ok TopSuccess
| (Bottom, _) -> Ok BottomSuccess

(* join and meet, subtypes split across join and meet *)
| (t, Join(a, b)) -> res_or  JoinSuccessR1 JoinSuccessR2 JoinFailR  (subtype t a) (subtype t b) (* t is a subtype of the least common supertype of a and b if it's a subtype of either a or b, because distributive lattice *)
| (t, Meet(a, b)) -> res_and MeetSuccessR  MeetFailR1    MeetFailR2 (subtype t a) (subtype t b) (* t is a subtype of the greatest common subtype of a and be if it's a subtype of both a and b *)
| (Join(a, b), t) -> res_and JoinSuccessL  JoinFailL1    JoinFailL2 (subtype a t) (subtype b t) (* the least common supertype of a and b is a subtype of t if both a and b are subtypes of t *)
| (Meet(a, b), t) -> res_or  MeetSuccessL1 MeetSuccessL2 MeetFailL (subtype a t) (subtype b t) (* the greatest common subtype of a and b is a subtype of t if either a or b is a subtype of t *)

| (TypeVar a, TypeVar b) -> if a == b then Ok (TypeVarMatch a) else Err @@ NoRelFail (TypeVar a, TypeVar b)

| (RecursiveType _ as a, RecursiveType _ as b) -> Err @@ NYI_FIXME_Fail (a, b)

| (a, b) -> Err @@ NoRelFail (a, b)

(* explanations for success and failure of regarding a type as a polar type *)
type positive_success_internal 'a =
| TypeVarPos
| JoinPos of positive_success_internal 'a * positive_success_internal 'a
| BottomPos
| BoolPos
| FuncPos of 'a * positive_success_internal 'a
| ProdPos of positive_success_internal 'a * positive_success_internal 'a
| RecordPos of Map.t string (positive_success_internal 'a)
| RecursivePos of guarded_success * positive_success_internal 'a

type positive_fail_internal 'a =
| JoinPosF1 of positive_fail_internal 'a
| JoinPosF2 of positive_fail_internal 'a
| MeetPos
| TopPos
| FuncPosF1 of 'a
| FuncPosF2 of positive_fail_internal 'a
| ProdPosF1 of positive_fail_internal 'a
| ProdPosF2 of positive_fail_internal 'a
| RecordPosF of Map.t string (positive_fail_internal 'a)
| RecursivePosUnguarded of guarded_fail
| RecursivePosSign of positive_fail_internal 'a

type negative_success =
| TypeVarNeg
| MeetNeg of negative_success * negative_success
| TopNeg
| BoolNeg
| FuncNeg of positive_success_internal negative_success * negative_success
| ProdNeg of negative_success * negative_success
| RecordNeg of Map.t string negative_success
| RecursiveNeg of guarded_success * negative_success

type negative_fail =
| JoinNeg
| MeetNegF1 of negative_fail
| MeetNegF2 of negative_fail
| BottomNeg
| FuncNegF1 of positive_fail_internal negative_fail
| FuncNegF2 of negative_fail
| ProdNegF1 of negative_fail
| ProdNegF2 of negative_fail
| RecordNegF of Map.t string negative_fail
| RecursiveNegUnguarded of guarded_fail
| RecursiveNegSign of negative_fail

type positive_success <- positive_success_internal negative_success
type positive_fail <- positive_fail_internal negative_fail

let rec is_positive (t: altype): result positive_success positive_fail = match t with
| Bool -> Ok BoolPos
| Func (a, b) -> res_and FuncPos FuncPosF1 FuncPosF2 (is_negative a) (is_positive b)
| Prod (a, b) -> res_and ProdPos ProdPosF1 ProdPosF2 (is_positive a) (is_positive b)
| Record m -> record_fields_are is_positive m |> map_ok RecordPos |> map_err RecordPosF
| Top -> Err TopPos
| Bottom -> Ok BottomPos
| Meet _ -> Err MeetPos
| Join (a, b) -> res_and JoinPos JoinPosF1 JoinPosF2 (is_positive a) (is_positive b)
| TypeVar _ -> Ok TypeVarPos
| RecursiveType (_, t') -> res_and RecursivePos RecursivePosUnguarded RecursivePosSign (is_guarded t) (is_positive t')

and is_negative (t: altype): result negative_success negative_fail = match t with
| Bool -> Ok BoolNeg
| Func (a, b) -> res_and FuncNeg FuncNegF1 FuncNegF2 (is_positive a) (is_negative b)
| Prod (a, b) -> res_and ProdNeg ProdNegF1 ProdNegF2 (is_negative a) (is_negative b)
| Record m -> record_fields_are is_negative m |> map_ok RecordNeg |> map_err RecordNegF
| Top -> Ok TopNeg
| Bottom -> Err BottomNeg
| Meet (a, b) -> res_and MeetNeg MeetNegF1 MeetNegF2 (is_negative a) (is_negative b)
| Join _ -> Err JoinNeg
| TypeVar _ -> Ok TypeVarNeg
| RecursiveType (_, t') -> res_and RecursiveNeg RecursiveNegUnguarded RecursiveNegSign (is_guarded t) (is_negative t')
