##
## Introduction to Julia
## See https://docs.julialang.org/ for lots, lots more
##
## Note:
## Some of these examples are designed to show things that cause errors.
## These have been commented out so that you can run this whole file,
## but uncomment those lines to see the errors if you wish.
##

# ----------------------------------------------------------------------

# variables and expressions

# typical infix notation, literals, assignment
# note dynamic typing
x = 1.32 + (3 * 4)^2
println(x)

# alternate syntax for using binary operations as variable-arity ones
println(+(1,2,3))

# ----------------------------------------------------------------------

# tuples and multiple assignment

# tuples
t = (1,2,3)
println(t)

# multiple assignment
u, v = 2, 3
println(u + v)

# ----------------------------------------------------------------------

# lists/arrays (1-indexed!!)

# declaring with initialization
a = [1,2,3,4]
println(a)

# indexing -- remember: 1-based
println(a[1])

# assignment to elements
a[1] = 42
println(a)

# "slice" subarray notation
println(a[2:3])
println(a[3:end])

# pushing and popping
push!(a,99)
println(a)
y = pop!(a)
println(y)
println(a)

# vectorized operations (like Python, but use .<op>)
println(a .+ 2)

# list comprehension
b = [x * 2 for x in a] # works like map
println(b)
c = [x * 2 for x in a if x > 3] # works like filter followed by map
println(c)

# ----------------------------------------------------------------------

# dictionaries

d = Dict("wesley" => 3, "buttercup" => 42, "inigo" => 99)
println(d)
println(typeof(d))

println(d["buttercup"])

println(keys(d))
println(values(d))

println(haskey(d,"inigo"))
println(haskey(d,"dread pirate roberts"))

# ----------------------------------------------------------------------

# functions

# standard form
# if no "return" statement, it returns whatever the last line evaluates to
function f(x)
    x + 1
end

# call them using notation similar to C, C++, Java, and lots of others
println(f(3))

# shorthand for simple functions
g(x) = x + 2
println(g(3))

# multiple return values
function f2(x)
    return x + 2, x * 2
end
println(f2(3))
u, v = f2(3)
println(u + v)

# higher-order functions
println(map(f,a))

# ----------------------------------------------------------------------

# control flow

# if / elseif / else chains

if x < 5
    println("Here")
elseif x > 100
    println("There")
else
    println("Everywhere")
end

# loops

let z = 5
    while z > 0
        println(z)
        z = z - 1
    end
end

# for loops

println(a)
for x in a
    println(x)
end

for (k,v) in d
    println(k)
end

# try/catch

try
    println(saywhat)
catch e
    println(e)
end

# ----------------------------------------------------------------------

# types

println(typeof(x))
println(typeof(a))

# typed functions
function h(x::Int)
    x + 1
end
println(h(3))
println(f(3.2))
# println(h(3.2)) -- should error

# type promotion
function j(x::Number)
    x + 1
end
println(j(3))
println(j(3.2))
# println(f("hello")) # should error inside the function on the +
# println(j("hello")) # should error on the call

# multiple dispatch (like overloading but much more powerful)
function j(x::String)
    println(x)
end
println(j(3.2))
j("hello")

# the "Any" type -- the parent of all other types
# arrays sort of look hetergeneous, but they are actually homogeneous
# and can be of type "Any"
a2 = [1,2,3,"hello"]
println(a2)

# ----------------------------------------------------------------------

# structures

struct MyPt
    x :: Real
    y :: Real
end

p = MyPt(3,4.2)
println("(", p.x, ",", p.y,")")
# q = MyPt("hello",5) # this fails

# Note: leaving off the field type causes it to default to "Any"

# ----------------------------------------------------------------------

# subtyping

abstract type MyPoint end

struct IntPt <: MyPoint
    x :: Int
    y :: Int
end

struct RealPt <: MyPoint
    x :: Real
    y :: Real
end

struct UIntPt <: MyPoint
    x :: UInt
    y :: UInt
end

p2 = IntPt(3,4)
println(p2)

p3 = RealPt(3,4)
println(p3)

p4 = UIntPt(3,4)
println(p4)

# ----------------------------------------------------------------------

# dispatching with subtypes

function showpt(p :: MyPoint)
    println("A Point!")
end

function showpt(p :: IntPt)
    println("An Int Point!")
end

function showpt(p :: RealPt)
    println("A Real Point!")
end

showpt(p2) # dispatches to the one for int points
showpt(p3) # dispatches to the one for real points
showpt(p4) # dispatches to the one for all points
