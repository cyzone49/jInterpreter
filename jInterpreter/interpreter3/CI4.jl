#
# Class Interpreter 4
# With numbers, plus, minus, if0, with, variable references,
# user-defined functions (lambda), and function calls.
#
# Includes analysis of the AST to add literal folding, collapsing conditionals,
# and with -> function application translation.
#

module CI4

push!(LOAD_PATH, pwd())

using Error
using Lexer
export parse, calc, analyze, interp

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

# <AE> ::= (with <id> <AE> <AE>)
struct WithNode <: AE
    sym::Symbol
    binding_expr::AE
    body::AE
end

# <AE> ::= <id>
struct VarRefNode <: AE
    sym::Symbol
end

# <AE> ::= (lambda <id> <AE>)
struct FuncDefNode <: AE
    formal::Symbol
    body::AE
end

# <AE> ::= (<AE> <AE>)
struct FuncAppNode <: AE
    fun_expr::AE
    arg_expr::AE
end

#
# ==================================================
#

abstract type RetVal
end

abstract type Environment
end

struct NumVal <: RetVal
    n::Real
end

struct ClosureVal <: RetVal
    formal::Symbol
    body::AE
    env::Environment
end

#
# ==================================================
#

struct EmptyEnv <: Environment
end

struct ExtendedEnv <: Environment
    sym::Symbol
    val::RetVal
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
        binding = expr[2]
        return WithNode(binding[1],parse(binding[2]),parse(expr[3]))

    elseif expr[1] == :lambda
        return FuncDefNode( expr[2], parse(expr[3]) )

    else
        return FuncAppNode( parse(expr[1]), parse(expr[2]) )

    end

    throw(LispError("Unknown operator!"))
end

function parse( expr::Any )
  throw( LispError("Invalid type $expr") )
end

#
# ==================================================
#

function analyze( ast::NumNode )
    return ast
end

function analyze( ast::VarRefNode )
    return ast
end

function analyze( ast::PlusNode )
    alhs = analyze( ast.lhs )
    arhs = analyze( ast.rhs )

    if typeof(alhs) == NumNode && typeof(arhs) == NumNode
        return NumNode( alhs.n + arhs.n )
    end

    return PlusNode( alhs, arhs )
end

function analyze( ast::MinusNode )
    alhs = analyze( ast.lhs )
    arhs = analyze( ast.rhs )
    if typeof(alhs) == NumNode && typeof(arhs) == NumNode
        return NumNode( alhs.n - arhs.n )
    end

    return MinusNode( alhs, arhs )
end

function analyze( ast::WithNode )
    # transform from a with expression to application of a function
    fdn = FuncDefNode( ast.sym, analyze( ast.body ) )
    return FuncAppNode( fdn, analyze( ast.binding_expr ) )
end

function analyze( ast::If0Node )
    acond = analyze( ast.cond )

    if typeof( acond ) == NumNode
        if acond.n == 0
            return analyze( ast.zerobranch )
        else
            return analyze( ast.nzerobranch )
        end
    end

    azb = analyze( ast.zerobranch )
    anzb = analyze( ast.nzerobranch )
    return If0Node( acond, azb, anzb )
end

function analyze( ast::FuncDefNode )
    return FuncDefNode( ast.formal_parameter, analyze( ast.body ) )
end

function analyze( ast::FuncAppNode )
    return FuncAppNode( analyze( ast.fun_expr), analyze( ast.arg_expr ) )
end

#
# ==================================================
#

function calc( ast::NumNode, env::Environment )
    return NumVal( ast.n )
end

function calc( ast::PlusNode, env::Environment )
    lhs = calc( ast.lhs, env )
    rhs = calc( ast.rhs, env )
    return  NumVal( lhs.n + rhs.n )
end

function calc( ast::MinusNode, env::Environment )
    lhs = calc( ast.lhs, env )
    rhs = calc( ast.rhs, env )
    return  NumVal( lhs.n - rhs.n )
end

function calc( ast::If0Node, env::Environment )
    cond = calc( ast.cond, env )
    if cond.n == 0
        return calc( ast.zerobranch, env )
    else
        return calc( ast.nzerobranch, env )
    end
end

function calc( ast::WithNode, env::Environment )
    binding_val = calc( ast.binding_expr, env )
    ext_env = ExtendedEnv( ast.sym, binding_val, env )

    # make recursion work: tweak the closure (if applicable)
    # to reference the new environment
    if typeof( binding_val ) == ClosureVal
        binding_val.env = ext_env
    end

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

function calc( ast::FuncDefNode, env::Environment )
    return ClosureVal( ast.formal, ast.body , env )
end

function calc( ast::FuncAppNode, env::Environment )
    closure_val = calc( ast.fun_expr, env )
    actual_parameter = calc( ast.arg_expr, env )
    ext_env = ExtendedEnv( closure_val.formal,
                           actual_parameter,
                           closure_val.env )
    return calc( closure_val.body, ext_env )
end

function calc( ast::AE )
    return calc( ast, EmptyEnv() )
end

#
# ==================================================
#

function interp( cs::AbstractString )
    lxd = Lexer.lex( cs )
    ast = parse( lxd )
    revised_ast = analyze(ast)
    return calc( revised_ast, EmptyEnv() )
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
