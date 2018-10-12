#
# Class Interpreter 2
# With numbers, plus, minus, if0, with, and variable references
#

module CI2

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

# <AE> ::= (with (<id> <AE>) <AE>)
struct WithNode <: AE
    sym::Symbol
    binding_expr::AE
    body::AE
end

# <AE> ::= <id>
struct VarRefNode <: AE
    sym::Symbol
end

#
# ==================================================
#

abstract type Environment
end

struct EmptyEnv <: Environment
end

struct ExtendedEnv <: Environment
    sym::Symbol
    val::Real
    parent::Environment
end

#
# ==================================================
#

function parse( expr::Number )
    return NumNode( expr )
end

function parse( expr::Symbol )
    return VarRefNode( expr )
end

function parse( expr::Array{Any} )

    if expr[1] == :+
        return PlusNode( parse( expr[2] ), parse( expr[3] ) )

    elseif expr[1] == :-
        return MinusNode( parse( expr[2] ), parse( expr[3] ) )

    elseif expr[1] == :if0
        return If0Node( parse(expr[2]), parse(expr[3]) , parse(expr[4]) )

    elseif expr[1] == :with
        println("1 = ", expr[1])
        println("2 (binding)= ", expr[2])
        println("2 (binding)\tsym (1) = ", expr[2][1])
        println("2 (binding)\tbiding_expr (2) = ", expr[2][2])
        println("3 = ", expr[3])

        binding = expr[2]
        return WithNode(binding[1],parse(binding[2]),parse(expr[3]))

    end

    throw(LispError("Unknown operator!"))
end

function parse( expr::Any )
  throw( LispError("Invalid type $expr") )
end

#
# ==================================================
#

function calc( ast::NumNode, env::Environment )
    return ast.n
end

function calc( ast::PlusNode, env::Environment )
    return calc( ast.lhs, env ) + calc( ast.rhs, env )
end

function calc( ast::MinusNode, env::Environment )
    return calc( ast.lhs, env ) - calc( ast.rhs, env )
end

function calc( ast::If0Node, env::Environment )
    cond = calc( ast.cond, env )
    if cond == 0
        return calc( ast.zerobranch, env )
    else
        return calc( ast.nzerobranch, env )
    end
end

function calc( ast::WithNode, env::Environment )
    binding_val = calc( ast.binding_expr, env )
    ext_env = ExtendedEnv( ast.sym, binding_val, env )
    return calc( ast.body, ext_env )
end

function calc( ast::VarRefNode, env::EmptyEnv )
    throw( Error.LispError("Undefined variable " * string( ast.sym )) )
end

function calc( ast::VarRefNode, env::ExtendedEnv )
    if ast.sym == env.sym
        return env.val
    else
        return calc( ast, env.parent )
    end
end

#
# ==================================================
#

function interp( cs::AbstractString )
    lxd = Lexer.lex( cs )
    ast = parse( lxd )
    return calc( ast, EmptyEnv() )
end

# evaluate a series of tests in a file
function interpf( fn::AbstractString )
  f = open( fn )

  cur_prog = ""
  for ln in eachline(f)
      ln = chomp( ln )
      if length(ln) == 0 && length(cur_prog) > 0
          println( "" )
          println( "--------- Evaluating ----------" )
          println( cur_prog )
          println( "---------- Returned -----------" )
          try
              println( interp( cur_prog ) )
          catch errobj
              println( ">> ERROR: lxd" )
              lxd = Lexer.lex( cur_prog )
              println( lxd )
              println( ">> ERROR: ast" )
              ast = parse( lxd )
              println( ast )
              println( ">> ERROR: rethrowing error" )
              throw( errobj )
          end
          println( "------------ done -------------" )
          println( "" )
          cur_prog = ""
      else
          cur_prog *= ln
      end
  end

  close( f )
end

end #module
