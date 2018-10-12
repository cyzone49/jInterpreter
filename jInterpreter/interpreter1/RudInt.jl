#
# RudInt
# Base interpreter with numbers, plus, and minus
#

module RudInt
push!(LOAD_PATH, pwd())
using Revise
using Error
using Lexer

export parse, calc, interp

#
# ==================================================
#



function collatz( n::Real )
  return collatz_helper( n, 0 )
end

function collatz_helper( n::Real, num_iters::Int )
  if n == 1
    return num_iters
  end
  if mod(n,2)==0
    return collatz_helper( n/2, num_iters+1 )
  else
    return collatz_helper( 3*n+1, num_iters+1 )
  end
end

opDict = Dict(:+ => +, :- => -, :* => *, :/ => /, :mod => mod, :collatz => collatz)

#
# ==================================================
#

abstract type AE
end

# <AE> ::= <number>
struct NumNode <: AE
    n::Real
end

# <AE> ::= (op <AE> <AE>)
struct BinopNode <: AE
	op::Function
	lhs::AE
	rhs::AE
end

struct SoloNode <: AE
	op::Function
	n::AE
end

#
# ==================================================
#

function parse( expr::Number )
    return NumNode( expr )
end

function parse( expr::Array{Any} )

	# check if op is of type symbol
	if ( typeof(expr[1]) != Symbol )
		throw(LispError("Invalid! Operator must be of type Symbol"))
	end

	# check if op is defined in Dictionary opDict
	if ( !haskey( opDict, expr[1] ))
		throw(LispError("Invalid/Undefined operator!"))
	end

	# if expression has 2 arguments
	# Case: Collatz(collatz <AE><AE>) or Negate (:- <AE>)
	if ( length(expr) == 2 )
		if (expr[1] == (:-))
			return SoloNode( opDict[expr[1]], parse( expr[2] ) )
		elseif (expr[1] == (:collatz))
			if ( calc(parse(expr[2])) < 1 )
				throw(LispError("Arg for collatz must be >= 1!"))
			end
			return SoloNode( opDict[expr[1]], parse( expr[2] ) )
		else
			throw(LispError("Invalid operator!"))
		end
	# if expression has 3 arguments
	# Case: arithmatic ops
	elseif ( length(expr) == 3 )
		if (expr[1] == (:collatz))
			throw(LispError("Invalid number of arguments! Collatz takes only 1 <AE>"))
		end
		return BinopNode( opDict[ expr[1] ], parse( expr[2] ), parse( expr[3] ) )
	# expression has < 2 or > 3 arguments => Invalid
	else
		throw(LispError("Invalid number of arguments!"))
	end
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

function calc( ast::BinopNode )

	if (ast.op == (/))
		if (calc(ast.rhs) == 0)
			throw( LispError("Cannot divide by 0") )
		end
	end

	return ( ast.op( calc( ast.lhs ), calc( ast.rhs ) ) )
end

function calc( ast::SoloNode )
	if ( ast.op == (-) )
		return 0 - calc(ast.n)
	else
		return collatz( calc(ast.n) )
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
