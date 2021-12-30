local _t = {
    name = "Jiang",
    date = "1926.8"
}
t = {}
local mt = {
    -- Access t.k
    __index = function (t, k)
        return _t[k]
    end,
    -- Insert t.k = v
    __newindex = function(t, k, v)
        print("table t is read-only!!")
    end
}
setmetatable(t, mt)
t["date"] = "1926.9"    -- `t` is empty thus `__newindex` method is triggerred
t["sex"] = "male"
print(t["date"])
print(t["sex"])