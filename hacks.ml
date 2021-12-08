

open import "prelude.ml"
open import "amulet/typeable.ml"


(* hack to break out of the type system and dynamically check the types of a dynamic call *)
external private val dynamic_call_prim: option dynamic -> (dynamic -> option dynamic) -> type_rep (->) -> dynamic -> dynamic -> option dynamic = "\
  function(None, Some, arrow, f, x) \
    local function deconstruct_dynamic_type_app(type_rep) \
      local typecons, arg string.gmatch(type_rep, '(%b())$:(%b()))') \
      if not typecons then return nil end \
      return typecons:sub(2, -2) arg:sub(2, -2) \
    end \
    local f_arrow_arg, f_result = deconstruct_dynamic_type_app(f[1][1].name) \
    if not f_arrow_arg then return None end \
    local f_arrow, f_arg = deconstruct_dynamic_type_app(f_arrow_arg) \
    if not f_arrow then return None end \
    if f_arrow ~= arrow[1].name then return None end \
    if f_arg ~= x[1][1].name then return None end \
    return Some{__tag = 'Dynamic', {__tag = 'TypeRep', {name = f_result}}, f[2](x[2])} \
  end"

let dynamic_call f x = dynamic_call_prim None Some (type_of  (Proxy @(->))) f x
