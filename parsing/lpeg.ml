
(* open import "../base.ml" *)
open import "prelude.ml"
open import "data/array.ml"
open Amc

type emptyparservals = PNil
type parservals 'a 'tail = PCons of 'a * 'tail
type parservalslist 'a = PNil | PCons of 'a * parservalslist 'a
type parserbottom

type parser 'a

(* type function parserseq 'a 'b begin
 *   parserseq emptyparservals 'b = 'b
 *   parserseq 'a emptyparservals = 'a
 *   parserseq parserbottom 'b = parserbottom
 *   parserseq 'a parserbottom = parserbottom
 *   parserseq (parservals 'a 'tail) (parservals 'b 'btail) = parservals 'a (parserseq 'tail (parservals 'b 'btail))
 *   parserseq (parservals 'a 'tail) (parservalslist 'b) = parservals 'a (parserseq 'tail (parservalslist 'b))
 *   parserseq (parservalslist 'a) (parservals 'a 'tail) = parserseq (parservalslist 'a) 'tail
 *   parserseq (parservalslist 'a) (parservals 'b 'tail) = type_error (String "Tried to sequence two incompatible parsers, first captures a variable number of ":<>: ShowType 'a :<>: String " but second has a capture of type " :<>: ShowType 'b)
 *   parserseq (parservalslist 'a) (parservalslist 'a) = parservalslist 'a
 *   parserseq (parservalslist 'a) (parservalslist 'b) = type_error (String "Tried to sequence two incompatible parsers, first captures a variable number of ":<>: ShowType 'a :<>: String " but second captures a variable number of type " :<>: ShowType 'b)
 * end
 *
 * type function parseralt 'a 'b begin
 *   parseralt 'a 'a = 'a
 *   parseralt 'a parserbottom = 'a
 *   parseralt parserbottom 'b = 'b
 *   parseralt (parservalslist 'a) emptyparservals = parservalslist 'a
 *   parseralt emptyparservals (parservalslist 'a) = parservalslist 'a
 *   parseralt (parservalslist 'a) (parservals 'a 'tail) = parseralt (parservalslist 'a) 'tail
 *   parseralt (parservals 'a 'tail) (parservalslist 'a) = parseralt 'tail (parservalslist 'a)
 *   parseralt (parservals 'a 'atail) (parservals 'a 'btail) = parservals 'a (parseralt 'atail 'btail)
 *   parseralt (parservals 'a 'atail) (parservals 'b 'btail) = type_error (String "Tried to alternate two incompatible parsers, capture types are " :<>: ShowType (parservals 'a 'atail) :<>: String " and " :<>: ShowType (parservals 'b 'btail))
 *   parseralt (parservalslist 'a) (parservalslist 'a) = parservalslist 'a
 *   parseralt (parservalslist 'a) (parservalslist 'b) = type_error (String "Tried to alternate two incompatible parsers, capture types are " :<>: ShowType 'a :<>: String " and " :<>: ShowType 'b)
 * end
 *
 * type function parser_rep 'a begin
 *   parser_rep parserbottom = parserbottom
 *   parser_rep emptyparservals = emptyparservals
 *   parser_rep (parservalslist 'a) = parservalslist 'a
 *   parser_rep (parservals 'a emptyparservals) = parservalslist 'a
 *   parser_rep (parservals 'a (parservals 'a 'tail)) = parser_rep (parservals 'a 'tail)
 *   parser_rep (parservals 'a (parservals 'b 'tail)) = type_error (String "Tried to replicate a parser that produces multiple distinct captures " :<>: ShowType 'a :<>: String " and " :<>: ShowType 'b :<>: String "; consider using collect_tuple to merge them")
 * end *)

(* type function parser_collect_tuple_internal 'a begin
 *   parser_collect_tuple_internal emptyparservals = ()
 *   parser_collect_tuple_internal (parservals 'a emptyparservals) = 'a
 *   parser_collect_tuple_internal (parservals 'a (parservals 'b 'tail)) = 'a * (parser_collect_tuple_internal (parservals 'b 'tail))
 * end
 *
 * type function parser_collect_tuple 'a begin
 *   parser_collect_tuple parserbottom = parserbottom
 *   parser_collect_tuple emptyparservals = parservals (parser_collect_tuple_internal emptyparservals) emptyparservals
 *   parser_collect_tuple (parservals 'a 'tail) = parservals (parser_collect_tuple_internal (parservals 'a 'tail)) emptyparservals
 * end *)

type function parser_collect_list_internal 'a 'coll begin
  (* parser_collect_list_internal emptyparservals 'b = list 'b *)
  parser_collect_list_internal (parservals 'a emptyparservals) 'coll = 'coll 'a
  parser_collect_list_internal (parservalslist 'a) 'coll  = 'coll 'a
  parser_collect_list_internal (parservals 'a (parservalslist 'a)) 'coll = 'coll 'a
  parser_collect_list_internal (parservals 'a (parservals 'a 'tail)) 'coll = parser_collect_list_internal (parservals 'a 'tail) 'coll
  (* parser_collect_list_internal (parservals 'a (parservals 'b 'tail)) 'coll = type_error (String "Tried to collect a " :<>: ShowType 'coll :<>: String " from the the outputs of a parser with heterogenous outputs containing both " :<>: ShowType 'a :<>: String " and " :<>: ShowType 'b) *)
end

type function parser_collect_list 'a 'coll begin
  parser_collect_list parserbottom 'coll = parserbottom
  (* parser_collect_list emptyparservals 'b = parservals (parser_collect_list_internal emptyparservals 'b) emptyparservals *)
  parser_collect_list emptyparservals 'coll = type_error (String "Tried to collect a " :<>: ShowType 'coll :<>: String " from the outputs of a parser that is always empty. This is not allowed due to limitations of the type system. Try using a constant capture instead.")
  (* Because there is no monomorphic type of the empty list without algebraic subtyping and a typeclass instance cannot include a polymorphic value because the existing unifier cannot solve it, there is no way to return the always-empty list resulting from collecting an always empty parser result without requiring an inconvenient type annotation. Since this is really easy to work around by using a constant capture, the case has been banned so that the typing can always infer correctly without annotations. *)
  parser_collect_list (parservals 'a 'tail) 'coll = parservals (parser_collect_list_internal (parservals 'a 'tail) 'coll) emptyparservals
  parser_collect_list (parservalslist 'a) 'coll = parservals (parser_collect_list_internal (parservalslist 'a) 'coll) emptyparservals
end

type function parser1 'a begin
  parser1 'a = parser (parservals 'a emptyparservals)
end

type function parser_extract 'a begin
  parser_extract (parservals 'a emptyparservals) = option 'a
  parser_extract emptyparservals = option ()
  parser_extract 'a = type_error (String "tried to extract a value from a parser that doesn't fit")
end

(* external val seq: parser 'a -> parser 'b -> parser (parserseq 'a 'b) = "function(a, b) return a * b end" *)
external private val seq_prim: parser 'a -> parser 'b -> parser 'c = "function(a, b) return a * b end"
class seqable 'a 'b 'c | 'a 'b -> 'c begin
  val seq: 'a -> 'b -> 'c
end
(* instance seqable (parser emptyparservals) (parser emptyparservals) (parser emptyparservals) begin let seq = seq_prim end
 * instance seqable (parser emptyparservals) (parser (parservals 'a 'tail)) (parser (parservals 'a 'tail)) begin let seq = seq_prim end
 * instance seqable (parser 'tail) (parser 'b) (parser 'ctail) => seqable (parser (parservals 'a 'tail)) (parser 'b) (parser (parservals 'a 'ctail)) begin let seq = seq_prim end
 * instance seqable (parser parserbottom) (parser 'a) (parser parserbottom) begin let seq = seq_prim end
 * instance seqable (parser 'a) (parser parserbottom) (parser parserbottom) begin let seq = seq_prim end *)

instance seqable (parser emptyparservals) (parser emptyparservals) (parser emptyparservals) begin let seq = seq_prim end
instance seqable (parser emptyparservals) (parser (parservals 'a 'tail)) (parser (parservals 'a 'tail)) begin let seq = seq_prim end
instance seqable (parser emptyparservals) (parser (parservalslist 'a)) (parser (parservalslist 'a)) begin let seq = seq_prim end
instance seqable (parser emptyparservals) (parser parserbottom) (parser parserbottom) begin let seq = seq_prim end
instance seqable (parser (parservals 'a 'atail)) (parser emptyparservals) (parser (parservals 'a 'atail)) begin let seq = seq_prim end
instance seqable (parser 'atail) (parser (parservals 'b 'btail)) (parser 'c) => seqable (parser (parservals 'a 'atail)) (parser (parservals 'b 'btail)) (parser (parservals 'a 'c)) begin let seq = seq_prim end
instance seqable (parser 'atail) (parser (parservalslist 'b)) (parser 'c) => seqable (parser (parservals 'a 'atail)) (parser (parservalslist 'b)) (parser (parservals 'a 'c)) begin let seq = seq_prim end
instance seqable (parser (parservals 'a 'atail)) (parser parserbottom) (parser parserbottom) begin let seq = seq_prim end
instance seqable (parser (parservalslist 'a)) (parser emptyparservals) (parser emptyparservals) begin let seq = seq_prim end
instance seqable (parser (parservalslist 'a)) (parser 'atail) (parser (parservalslist 'a)) => seqable (parser (parservalslist 'a)) (parser (parservals 'a 'atail)) (parser (parservalslist 'a)) begin let seq = seq_prim end
instance seqable (parser (parservalslist 'a)) (parser (parservalslist 'a)) (parser (parservalslist 'a)) begin let seq = seq_prim end
(* instance type_error (String "invalid sequencing of parsers with different captures") => seqable (parser (parservalslist 'a)) (parser (parservalslist 'b)) (parser (parservalslist 'a)) begin end *)
instance seqable (parser (parservalslist 'a)) (parser parserbottom) (parser parserbottom) begin let seq = seq_prim end
instance seqable (parser parserbottom) (parser 'a) (parser parserbottom) begin let seq = seq_prim end

external private val alt_prim: parser 'a -> parser 'b -> parser 'c = "function(a, b) return a + b end"
class altable 'a 'b 'c | 'a 'b -> 'c begin
  val alt: 'a -> 'b -> 'c
end
(* instance altable (parser emptyparservals) (parser emptyparservals) (parser emptyparservals) begin let alt = alt_prim end *)
instance altable (parser emptyparservals) (parser (parservals 'a 'tail)) (parser (parservalslist 'a)) => altable (parser emptyparservals) (parser (parservals 'a (parservals 'a 'tail))) (parser (parservalslist 'a)) begin let alt = alt_prim end
instance altable (parser emptyparservals) (parser (parservals 'a emptyparservals)) (parser (parservalslist 'a)) begin let alt = alt_prim end
instance altable (parser emptyparservals) (parser (parservalslist 'b)) (parser (parservalslist 'b)) begin let alt = alt_prim end
instance altable (parser emptyparservals) (parser parserbottom) (parser emptyparservals) begin let alt = alt_prim end
instance altable (parser (parservals 'a 'tail)) (parser emptyparservals) (parser (parservalslist 'a)) => altable (parser (parservals 'a (parservals 'a 'tail))) (parser emptyparservals) (parser parserbottom) begin let alt = alt_prim end
instance altable (parser (parservals 'a emptyparservals)) (parser emptyparservals) (parser (parservalslist 'a)) begin let alt = alt_prim end
(* instance altable (parser 'atail) (parser 'btail) (parser 'ctail) => altable (parser (parservals 'a 'atail)) (parser (parservals 'a 'btail)) (parser (parservals 'a 'ctail)) begin let alt = alt_prim end *)
instance altable (parser 'atail) (parser (parservalslist 'a)) (parser (parservalslist 'a)) => altable (parser (parservals 'a 'atail)) (parser (parservalslist 'a)) (parser (parservalslist 'a)) begin let alt = alt_prim end
instance altable (parser (parservals 'a 'atail)) (parser parserbottom) (parser (parservals 'a 'atail)) begin let alt = alt_prim end
instance altable (parser (parservalslist 'a)) (parser emptyparservals) (parser (parservalslist 'a)) begin let alt = alt_prim end
instance altable (parser (parservalslist 'a)) (parser 'btail) (parser (parservalslist 'a)) => altable (parser (parservalslist 'a)) (parser (parservals 'a 'btail)) (parser (parservalslist 'a)) begin let alt = alt_prim end
(* instance altable (parser (parservalslist 'a)) (parser (parservalslist 'a)) (parser (parservalslist 'a)) begin let alt = alt_prim end *)
instance altable (parser (parservalslist 'a)) (parser parserbottom) (parser (parservalslist 'a)) begin let alt = alt_prim end
instance altable (parser parserbottom) (parser emptyparservals) (parser emptyparservals) begin let alt = alt_prim end
instance altable (parser parserbottom) (parser (parservals 'b 'btail)) (parser (parservals 'b 'btail)) begin let alt = alt_prim end
instance altable (parser parserbottom) (parser (parservalslist 'b)) (parser (parservalslist 'b)) begin let alt = alt_prim end
(* instance altable (parser parserbottom) (parser parserbottom) (parser parserbottom) begin let alt = alt_prim end *)
instance altable (parser 'a) (parser 'a) (parser 'a) begin let alt = alt_prim end

external val act: parser (parservals 'a emptyparservals) -> ('a -> 'b) -> parser (parservals 'b emptyparservals) = "function(a, b) return a / b end"

external private val rep_prim: parser 'a -> int -> parser 'b = "function(a, b) return a ^ b end"
class repable 'a 'b | 'a -> 'b begin
  val rep: 'a -> int -> 'b
end
instance repable (parser emptyparservals) (parser emptyparservals) begin let rep = rep_prim end
instance repable (parser (parservals 'a emptyparservals)) (parser (parservalslist 'a)) begin let rep = rep_prim end
instance repable (parser (parservals 'a 'tail)) (parser (parservalslist 'a)) => repable (parser (parservals 'a (parservals 'a 'tail))) (parser (parservalslist 'a)) begin let rep = rep_prim end
instance repable (parser (parservals 'a (parservalslist 'a))) (parser (parservalslist 'a)) begin let rep = rep_prim end
instance repable (parser (parservalslist 'a)) (parser (parservalslist 'a)) begin let rep = rep_prim end
instance repable (parser parserbottom) (parser parserbottom) begin let rep = rep_prim end

external val neg: parser 'a -> parser emptyparservals = "function(pat) return -pat end"


class parser_tuple 'a 'b | 'a -> 'b begin end
instance parser_tuple (parser emptyparservals) (parser (parservals () emptyparservals)) begin end
instance parser_tuple (parser (parservals 'a emptyparservals)) (parser (parservals 'a emptyparservals)) begin end
instance parser_tuple (parser (parservals 'b 'tail)) (parser (parservals 'c emptyparservals)) => parser_tuple (parser (parservals 'a (parservals 'b 'tail))) (parser (parservals ('a * 'c) emptyparservals)) begin end
(* instance type_error (String "Can't tuplifiy a parser with variable length captures") => parser_tuple (parser (parservalslist 'a)) 'b begin end *)
instance parser_tuple (parser parserbottom) (parser parserbottom) begin end

private class parser_coll 'a 'coll 'b | 'a 'coll -> 'b, 'a 'b -> 'coll begin end
(* instance parser_coll (parser emptyparservals) 'coll (parser (parservals 'coll empt)) *)
instance parser_coll (parser (parservals 'a emptyparservals)) 'coll (parser (parservals ('coll 'a) emptyparservals)) begin end
instance parser_coll (parser (parservals 'b 'tail)) 'coll (parser (parservals ('coll 'a) emptyparservals)) => parser_coll (parser (parservals 'a (parservals 'b 'tail))) 'coll (parser (parservals ('coll 'a) emptyparservals)) begin end
instance parser_coll (parser (parservals 'a (parservalslist 'a))) 'coll (parser (parservals ('coll 'a) emptyparservals)) begin end
instance parser_coll (parser (parservalslist 'a)) 'coll (parser (parservals ('coll 'a) emptyparservals)) begin end



private class parser_coll_list 'a 'b | 'a -> 'b begin end
(* instance parser_coll (parser emptyparservals) 'coll (parser (parservals 'coll empt)) *)
instance parser_coll_list (parser (parservals 'a emptyparservals)) (parser (parservals (list 'a) emptyparservals)) begin end
instance parser_coll_list (parser (parservals 'b 'tail)) (parser (parservals (list 'a) emptyparservals)) => parser_coll_list (parser (parservals 'a (parservals 'b 'tail))) (parser (parservals (list 'a) emptyparservals)) begin end
instance parser_coll_list (parser (parservals 'a (parservalslist 'a))) (parser (parservals (list 'a) emptyparservals)) begin end
instance parser_coll_list (parser (parservalslist 'a)) (parser (parservals (list 'a) emptyparservals)) begin end




private class parser_coll_array 'a 'b | 'a -> 'b begin end
(* instance parser_coll (parser emptyparservals) 'coll (parser (parservals 'coll empt)) *)
instance parser_coll_array (parser (parservals 'a emptyparservals)) (parser (parservals (array 'a) emptyparservals)) begin end
instance parser_coll_array (parser (parservals 'b 'tail)) (parser (parservals (array 'a) emptyparservals)) => parser_coll_array (parser (parservals 'a (parservals 'b 'tail))) (parser (parservals (array 'a) emptyparservals)) begin end
instance parser_coll_array (parser (parservals 'a (parservalslist 'a))) (parser (parservals (array 'a) emptyparservals)) begin end
instance parser_coll_array (parser (parservalslist 'a)) (parser (parservals (array 'a) emptyparservals)) begin end

external private val lpeg:
  { p: string -> parser emptyparservals
  , c: parser 'a -> parser (parservals string 'a)
  , r: string -> parser emptyparservals
  , s: string -> parser emptyparservals
  , cc: 'a -> parser (parservals 'a emptyparservals)
  , cp: parser (parservals int emptyparservals)
  , cs: parser (parservalslist string) -> parser (parservals string emptyparservals)
  , cx: parser emptyparservals -> (string -> option 'b) -> parser (parservals 'b emptyparservals)
  , actx: parser (parservals 'a emptyparservals) -> ('a -> option 'b) -> parser (parservals 'b emptyparservals)
  , zero: parser parserbottom
  , one: parser emptyparservals
  , star: parser emptyparservals
  , v: string -> parser 'a
  , grammar: {'a| } -> parser 'b -> parser 'b
  (* , rep: parser 'a -> int -> parser (parser_rep 'a) *)
  (* , collect_tuple: parser 'a -> parser (parser_collect_tuple 'a) *)
  , collect_tuple: parser_tuple 'a 'b => 'a -> 'b
  , collect_list: list 'b -> ('b * list 'b -> list 'b) -> parser_coll_list 'a 'c => 'a -> 'c
  , collect_array: parser_coll_array 'a 'b => 'a -> 'b
  , parse: parser (parservals 'a emptyparservals) -> string -> option 'a
  } =
  "(function() \
    local lpeg = require('lpeg') \
    local function tuple_collect(xs) \
      if #xs == 0 then \
        return nil \
      elseif #xs == 1 then \
        return xs[1] \
      else \
        local l = xs[#xs] \
        for i = #xs - 1, 1, -1 do \
          l = {_1 = xs[i], _2 = l} \
        end \
        return l \
      end \
    end \
    local function list_collect(n, c, xs) \
      local l = n \
      for i = #xs, 1, -1 do \
        l = c{_1 = xs[i], _2 = l} \
      end \
      return l \
    end \
    local function make_array(tab) \
      return {__tag = \"Array\", {length = #tab, backing = tab}} \
    end \
    return { \
      p = lpeg.P, \
      c = lpeg.C, \
      r = lpeg.R, \
      s = lpeg.S, \
      cc = lpeg.Cc, \
      cs = lpeg.Cs, \
      cp = lpeg.Cp(), \
      cx = function(pat) return function(f) \
        return lpeg.Cmt(lpeg.C(pat) * lpeg.Cp(), function(_, _, cap, pos) \
          local val = f(cap) \
          if val.__tag == \"Some\" then \
            return pos, val[1] \
          else \
            return false \
          end \
        end) \
      end end, \
      actx = function(pat) return function(f) \
        return lpeg.Cmt(pat * lpeg.Cp(), function(_, _, cap, pos) \
          local val = f(cap) \
          if val.__tag == \"Some\" then \
            return pos, val[1] \
          else \
            return false \
          end \
        end) \
      end end, \
      zero = lpeg.P(false), \
      one = lpeg.P(true), \
      star = lpeg.P(1), \
      v = lpeg.V, \
      grammar = function(g) \
        return function(start) \
          local g2 = {} \
          for k, v in pairs(g) do \
            g2[k] = v \
          end \
          g2[1] = start \
          return lpeg.p(g2) \
        end \
      end, \
      rep = function(p) return function(r) return p ^ r end end, \
      collect_tuple = function(typefam) return function(p) return lpeg.Ct(p) / tuple_collect end end, \
      collect_list = function(n) return function(c) return function(typefam) return function(p) return lpeg.Ct(p) / function(xs) return list_collect(n, c, xs) end end end end end, \
      collect_array = function(typefam) return function(p) return lpeg.Ct(p)/make_array end end, \
      parse = function(pat) return function(str) \
        local res = lpeg.match(pat, str) \
        if res then \
          return {__tag = \"Some\", res} \
        else \
          return {__tag = \"None\"} \
        end \
      end end \
    } \
  end)()"

let p = lpeg.p
let c = lpeg.c
let cc = lpeg.cc
let cp = lpeg.cp
let cs = lpeg.cs
let cx = lpeg.cx
let actx = lpeg.actx
let r = lpeg.r
let s = lpeg.s
let zero = lpeg.zero
let one = lpeg.one
let star = lpeg.star
(* let rep = lpeg.rep *)

let v = lpeg.v
let grammar = lpeg.grammar

let collect_tuple = lpeg.collect_tuple
let collect_list p = lpeg.collect_list Nil Cons p
let collect_array = lpeg.collect_array

let parse p s = lpeg.parse p s

(* class adder 'a 'b 'c | 'a 'b -> 'c begin end *)
(* instance (parseralt 'a 'b) ~ 'c => adder 'a 'b 'c begin end
 * instance monoidal parser parserbottom adder begin
 *   let (<+>) = alt
 *   let zero = lpeg.zero
 * end
 *
 * instance semiringal parser 'a emptyparservals begin
 *   let (<*>) = seq
 *   let one: parser unit = lpeg.one
 * end *)
(* let ws = s " \n\t" `rep` 0
 * let num = c (r "09" `rep` 1) `act` parse_float
 * let x = collect_list ((num `seq` p ",") `rep` 0)
 * let y = x `parse` "1,2,3,4,"
 * let () = print y *)
