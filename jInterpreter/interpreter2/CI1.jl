#
# Class Interpreter 1
# With numbers, plus, minus, and if0
#

module CI1

push!(LOAD_PATH, pwd())

using Error
using Lexer
export parse, calc, interp

#
# ==================================================
#

abstract type AE
end

# <AE> ::= <number>
struct NumNode <: AE
    n::Real
end

# <AE> ::= (+ <AE> <AE>)
struct PlusNode <: AE
    lhs::AE
    rhs::AE
end

# <AE> ::= (- <AE> <AE>)
struct MinusNode <: AE
    lhs::AE
    rhs::AE
end

# <AE> ::= (if0 <AE> <AE> <AE>)
struct If0Node <: AE
    cond::AE
    zerobranch::AE
    nzerobranch::AE
end

#
# ==================================================
#

function parse( expr::Number )
    return NumNode( expr )
end

function parse( expr::Array{Any} )

    if expr[1] == :+
        return PlusNode( parse( expr[2] ), parse( expr[3] ) )

    elseif expr[1] == :-
        return MinusNode( parse( expr[2] ), parse( expr[3] ) )

    elseif expr[1] == :if0
        return If0Node( parse(expr[2]), parse(expr[3]) , parse(expr[4]) )

    end

    throw(LispError("Unknown operator!"))
end

function parse( expr::Any )
  throw( LispError("Invalid type $expr") )
end

#
# ==================================================
#

function calc( ast::NumNode )
    return ast.n
end

function calc( ast::PlusNode )
    return calc( ast.lhs ) + calc( ast.rhs )
end

function calc( ast::MinusNode )
    return calc( ast.lhs ) - calc( ast.rhs )
end

function calc( ast::If0Node )
    cond = calc( ast.cond )
    if cond == 0
        return calc( ast.zerobranch )
    else
        return calc( ast.nzerobranch )
    end
end

#
# ==================================================
#

function interp( cs::AbstractString )
    lxd = Lexer.lex( cs )
    ast = parse( lxd )
    return calc( ast )
end

end #module
