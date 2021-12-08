do
  local function Dynamic(a)
    return function(b)
      return { __tag = "Dynamic", a, b }
    end
  end
  local Proxy = { __tag = "Proxy" }
  local function _Typeable_kk(finger, name)
    return {
      { name = name .. "#" .. finger },
      __tag = "TypeRep"
    }
  end
  local function _Typeable_app(pair)
    local ta, tb = pair._1[1], pair._2[1]
    return {
      {
        name = "(" .. ta.name .. ") :$ (" .. tb.name .. ")"
      },
      __tag = "TypeRep"
    }
  end
  local io_stdout = io.stdout
  local io_stderr = io.stderr
  local io_stdin = io.stdin
  local x = Dynamic(_Typeable_kk(-2, "int"))(3)
  local f = Dynamic(_Typeable_app({
    _1 = _Typeable_app({
      _2 = _Typeable_kk(-2, "int"),
      _1 = _Typeable_kk(-7, "->")
    }),
    _2 = _Typeable_kk(-2, "int")
  }))(function(x0) return x0 + 1 end)
  local arrow = (function()
    return _Typeable_kk(-7, "->")
  end)(Proxy)
  local binfunc = (function()
    return _Typeable_app({
      _2 = _Typeable_app({
        _2 = _Typeable_kk(-2, "int"),
        _1 = _Typeable_app({
          _2 = _Typeable_kk(-2, "int"),
          _1 = _Typeable_kk(-7, "->")
        })
      }),
      _1 = _Typeable_app({
        _1 = _Typeable_kk(-7, "->"),
        _2 = _Typeable_kk(-2, "int")
      })
    })
  end)(Proxy)
  return {
    arrow = arrow,
    binfunc = binfunc,
    f = f,
    x = x
  }
end