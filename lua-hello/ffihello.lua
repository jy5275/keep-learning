local ffi = require "ffi"
local myffi = ffi.load('libmyffi.so', true)

local function Basic()
    ffi.cdef[[
        int printf(const char *fmt, ...);
    ]]
    ffi.C.printf("Hello %s!\n", "world")

    ffi.cdef[[
        int add(int x, int y);
    ]]
    local res = myffi.add(1, 2)
    local c_type_int = ffi.typeof("int")
    print(res, c_type_int)          -- ctype<int>

    local c_data = ffi.new(ffi.typeof("int"))
    print(c_data, type(c_data))               -- cdata<int>:0x...

    local c_str_t = ffi.typeof("const char")
    local c_str = ffi.cast(c_str_t, "myStr")
    print(c_str_t, c_str, type(c_str))           -- cdata<const char*>:0x...

    local uintptr_t = ffi.typeof("uintptr_t")
    print(tonumber(ffi.cast(uintptr_t, c_str)))
end

local function MyStruct()
    local ffi = require("ffi")
    ffi.cdef[[
        typedef struct { double x, y; } point_t;
    ]]

    local point
    local mt = {
        __add = function(a, b) 
            local np = ffi.new(ffi.typeof("point_t"))
            np.x = a.x + b.x
            np.y = a.y + b.y
            return np
        end,
        __len = function(a) return math.sqrt(a.x*a.x + a.y*a.y) end, -- for # operand
        __index = {
            area = function(a) return a.x*a.x + a.y*a.y end,
        },
    }
    point = ffi.metatype("point_t", mt)  -- enable c-like constructor in lua

    local a = ffi.new(ffi.typeof("point_t"))
    local b = point(0.5, 8)
    a.x = 3; a.y = 4
    print(a.x, a.y)  --> 3  4
    print(#a)        --> 5
    print(a:area())  --> 25

    local c = a + b
    print(#c)        --> 12.5
    -- local b = a + point(0.5, 8)
    -- print(#b)        --> 12.5
end
Basic()
MyStruct()