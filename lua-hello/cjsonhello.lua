package.cpath = package.cpath..";/usr/local/openresty/lualib/cjson.so"
local cjson = require "cjson"

_M = {}

local function TraverseTable(t, level)
    if level == nil then
        level = 0
    end
    for k,v in pairs(t) do 
        if type(v) == "table" then
            print(string.rep(" ", 2*level)..k..":")
            TraverseTable(v, level+1)
        elseif type(v) == "function" then
        else
            print(string.rep(" ", 2*level)..k..":"..v)
        end
    end
end

local function Test()
    -- 对象类型
    lua_object = {
            ["name"] = "Jiang",
            ["age"] = 24,
            ["addr"] = "BeiJing",
            ["email"] = "1569989xxxx@126.com",
            ["tel"] = "1569989xxxx"
    }
    local val = cjson.encode(lua_object)
    local myStr = '{"rules":[{"match_path":"/","match_type":"","directives":{"allow_list":{"ips":["10.129.98.209"],"policies":["office_ip"]},"limit_count":{"count":99999,"time_window":1},"deny_list":["all"],"traffic_forwarding":{"percentage":1}}}],"directives":{"allow_list":{"ips":["10.129.98.209"],"policies":["office_ip"]},"limit_count":{"count":99999,"time_window":1},"deny_list":["all"],"traffic_forwarding":{"percentage":1}},"md5_ver":"f51e789b18d7284a0fef278ebd6869b0","id":3707,"domain":"test.shopee.systems","env":"test"}'
    local obj = cjson.decode(myStr)
    -- print(val, type(val))
    print("=======")
    TraverseTable(obj)
    print(type(TraverseTable))
    print(obj.rules)
end

_M.TraverseTable = TraverseTable

return _M