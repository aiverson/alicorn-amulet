do
  local Proxy = { __tag = "Proxy" }
  local function Amc_dotrestrict_row(tmp)
    return function(tmp0)
      return { _1 = tmp0[tmp], _2 = tmp0 }
    end
  end
  local function g(tmp)
    return function(x)
      return ({ _1 = x[tmp], _2 = x })._1
    end
  end
  local x = ({
    _1 = ({ foo = 1, bar = 2 }).foo,
    _2 = { foo = 1, bar = 2 }
  })._1
  local _print = print
  local function h(tmp)
    return function(tmp0)
      return _print(Proxy)
    end
  end
  _print(Proxy)
  local foo = print
  foo("quux")
  return {
    f = Amc_dotrestrict_row,
    foo = foo,
    g = g,
    h = h,
    ["print"] = _print,
    x = x
  }
end