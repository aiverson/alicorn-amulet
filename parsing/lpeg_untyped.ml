
open import "amulet/base.ml"
open import "amulet/option.ml"

type parser

type parser1 'a <- parser

external private val lpeg:
  { p: string -> parser
  , c: parser -> parser
  , r: string -> parser
  , s: string -> parser
  , cc: 'a -> parser
  , cp: parser
  , cs: parser -> parser
  , cx: parser -> (string -> option 'b) -> parser
  , actx: parser -> ('a -> option 'b) -> parser
  , zero: parser
  , one: parser
  , star: parser
  , v: string -> parser
  , grammar: {'a| } -> parser -> parser
  (* , rep: parser 'a -> int -> parser (parser_rep 'a) *)
  (* , collect_tuple: parser 'a -> parser (parser_collect_tuple 'a) *)
  , collect_tuple: parser -> parser
  , collect_list: list 'b -> ('b * list 'b -> list 'b) -> parser -> parser
  , collect_array: parser -> parser
  , parse: parser -> string -> option 'a
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
      collect_list = function(n) return function(c) return function(p) return lpeg.Ct(p) / function(xs) return list_collect(n, c, xs) end end end end, \
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

external val alt: parser -> parser -> parser = "function(a, b) return a + b end"
external val seq: parser -> parser -> parser = "function(a, b) return a * b end"
external val rep: parser -> int -> parser = "function(pat, n) return pat ^ n end"
external val act: parser -> ('a -> 'b) -> parser = "function(pat, f) return pat / f end"
external val neg: parser -> parser = "function(pat) return -pat end"


let v = lpeg.v
let grammar = lpeg.grammar

let collect_tuple = lpeg.collect_tuple
let collect_list p = lpeg.collect_list Nil Cons p
let collect_array = lpeg.collect_array

let parse p s = lpeg.parse p s
