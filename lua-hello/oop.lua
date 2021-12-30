function clone(org)
    local function copy(org, res)
        for k,v in pairs(org) do
            if type(v) ~= "table" then
                res[k] = v;
            else
                res[k] = {};
                copy(v, res[k])
            end
        end
    end

    local res = {}
    copy(org, res)
    return res
end

-- Meta class
Shape = {area = 0}

-- 基础类方法 new
function Shape:new(o, side)
  o = o or {}
  setmetatable(o, self)
  self.__index = self
  side = side or 0
  self.area = side*side;
  return o
end

-- 基础类方法 printArea
function Shape:printArea ()
  print("Area size:", self.area)
end

Rectangle = Shape:new()
function Rectangle:new (o,length,breadth)
    o = o or Shape:new(o)
    setmetatable(o, self)
    self.__index = self
    self.area = length * breadth
    return o
end
  
function Rectangle:printArea ()
    print("矩形面积为 ", self.area)
end

r1 = Rectangle:new(nil,10,20)
r1:printArea()

r2 = Rectangle:new(nil, 1, 2)
r1:printArea()
r2:printArea()
  