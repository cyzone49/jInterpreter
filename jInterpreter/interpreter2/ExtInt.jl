#
# ExtInt
# Base interpreter with numbers, plus, and minus
#

module ExtInt
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
opArray = [:if0, :with, :lambda, :mod, :collatz, :id]

function symbol_is_valid( s::Symbol )
	# make sure arg does not match grammar symbols
	if haskey( opDict, s ) || ( s in opArray )
		return false
	else
		return true
	end
end

#
# ==================================================
#

abstract type AE
end

abstract type RetVal end

abstract type Environment end

struct NumVal <: RetVal
  n::Real
end

struct ClosureVal <: RetVal
  formal::Array{Symbol}
  body::AE
  env::Environment
end

struct EmptyEnv <: Environment
end

struct ExtendedEnv <: Environment
  sym::Symbol
  val::RetVal
  parent::Environment
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

struct If0Node <: AE
  condition::AE
  zero_branch::AE
  nonzero_branch::AE
end

struct WithNode <: AE
	param::Dict{Any, Any}
	body::AE
end

struct VarRefNode <: AE
  sym::Symbol
end

struct FunDefNode <: AE
  formal::Array{Any}
  fun_body::AE
end

struct FunAppNode <: AE
  fun_expr::AE
  arg_expr::Dict{Any, Any}
end




#
# ==================================================
#

function parse( expr::Number )
    return NumNode( expr )
end

function parse( expr::Symbol )
	if symbol_is_valid(expr)
		return VarRefNode( expr )
	else
		throw(LispError("Arguments of cannot match grammar symbols"))
	end

end

function parse( expr::Array{Any} )
	println("expr = ", expr, " with length = ", length(expr))

	# CASE 0: <AE> ::= id OR <AE> ::= (<AE>)
	if length( expr ) == 1
		return parse( expr[1] )
	end

	# CASE 1: op is defined in Dictionary opDict # From RudInt
	if ( haskey( opDict, expr[1] ))
		# Case: Collatz(collatz <AE><AE>) or Negate (:- <AE>)
		if ( length(expr) == 2 )
			if (expr[1] == (:-))
				return SoloNode( opDict[expr[1]], parse( expr[2] ) )
			elseif (expr[1] == (:collatz))
				return SoloNode( opDict[expr[1]], parse( expr[2] ) )
			else
				throw(LispError("Invalid operator!"))
			end

		# Case: arithmatic ops in opDict
		elseif ( length(expr) == 3 )
			if (expr[1] == (:collatz))
				throw(LispError("Invalid number of arguments! Collatz takes only 1 <AE>"))
			end
			return BinopNode( opDict[ expr[1] ], parse( expr[2] ), parse( expr[3] ) )
		else
			throw(LispError("Invalid argument numbers!"))
		end


	# CASE 2: including op from interpreter 2 [ :if0, :lambda, :with ]
	elseif ( expr[1] == :if0 ) || ( expr[1] == :with ) || ( expr[1] == :lambda )

		if (expr[1] == (:if0)) #if0 always has 4 arguments: :if0, condition, zerobranch ,nonzero_branch
			# println("\nParsing If0Node")
			return If0Node( parse(expr[2]), parse(expr[3]), parse(expr[4]) )

		elseif expr[1] == :with
			println("\nParsing WithNode")
			param_dict = Dict()
			for i in 1:(length(expr[2]))

				# make sure arg does not match grammar symbols
				# if haskey( opDict, expr[2][i][1] ) || ( expr[2][i][1] in opArray )
				if ( !symbol_is_valid( expr[2][i][1] ) )
					throw(LispError("Arguments of cannot match grammar symbols"))
				end

				println("\tsymbol is valid")

				# make sure arg has a unique name (not already in the list of args symbols)
				if haskey(param_dict, expr[2][i][1] )
					throw(LispError("Arguments of a multiple_args_with must have distinct names"))
				end
				println("\tsymbol is not repeated")

				param_dict[ parse( expr[2][i][1] ) ] = parse( expr[2][i][2] )
			end
			println("param_dict = $param_dict")
			return WithNode( param_dict, parse(expr[end]) )

		elseif expr[1] == :lambda
			println("Parsing FuncDefNode")

			#TODO: take into account (lambda (x y) (+ x z))

			param_array = []
			for i in 1:(length(expr[2]))
				# make sure arg does not match grammar symbols
				# if haskey( opDict, expr[2][i] ) || ( expr[2][i] in opArray )
				if ( !symbol_is_valid( expr[2][i] ) )
					throw(LispError("Arguments of cannot match grammar symbols"))
				end
				# make sure arg has a unique name (not already in the list of args symbols)
				if expr[2][i] in param_array
					throw(LispError("Arguments of a multiple_args_func must have distinct names"))
				end
				push!(param_array, expr[2][i])
			end
			println("param_array = $param_array")
			return FunDefNode( param_array, parse(expr[end]) )
		end

	# CASE 3: if expr[1] is not a grammar symbol =>> (FunAppNode or Invalid)
	else
		println("<AE> ::= ( <AE> <AE>+ )")
		println("printing expr:")
		for i in 1:length(expr)
			println("\texpr[$i]=",expr[i], " of type ", typeof(expr[i]))
		end
		fun_expr = parse( expr[1] )

		println("fun_expr = $fun_expr --- type: ", typeof(fun_expr))
		println("\n\texpr[1] = ", expr[1], " --- type: ", typeof(expr[1]))
		println("\n\texpr[1][1] = ", expr[1][1], " --- type: ", typeof(expr[1][1]))


		if typeof( fun_expr ) == FunDefNode
			println("********************\nParsing FunAppNode with expr = ", expr, "\n********************\n")

			# fun_expr = parse( expr[1] )

			# make sure number of formal_args ==  number of actual_args
			if length(fun_expr.formal) != ( length(expr)-1 )
				throw(LispError("FunAppNode Error: number of actual args does not match number of formal args"))
			end

			# create Dict to store list of (formal_arg: actual_arg)
			param_dict = Dict()
			index = 2
			for p in fun_expr.formal
				current_actual = parse( expr[index] ) # calculate actual_arg[i] =>> should return NumNode

				# make sure actual_args calculates to a number (type NumNode before calc)
				if ( typeof( current_actual ) != NumNode )
					throw(LispError("FunAppNode Error: Invalid Actual Param Arguments"))
				end
				param_dict[ parse(p) ] = current_actual
				index += 1
			end
			println("ABOUT to RETURN FunAppNode.\nparam_dict = $param_dict")
			return FunAppNode( fun_expr, param_dict )

		else
			println("\n\nNOT LAMBDA\n\texpr = $expr")
			param_dict = Dict()
			println("created param_dict = $param_dict\ngoing into loop")
			for i in 2:length(expr)
				println("\tparse( expr[$i] ) = ", parse(expr[i]))
				param_dict[ parse(i) ] = parse(expr[i])
			end
			println("\nParam_dict = $param_dict")
			return FunAppNode(fun_expr, param_dict)
			# throw(LispError("Invalid/Undefined operator!"))
		end
	end
end

function parse( expr::Any )
  throw( LispError("Invalid type $expr") )
end

#
# ==================================================
#

function calc( ast::NumNode, env::Environment )
    return NumVal( ast.n )
end

function calc( ast::BinopNode, env::Environment )
	# println("\nCalculating Binop\n\tAST = ", ast)

	lhs = calc( ast.lhs, env )
	rhs = calc( ast.rhs, env )

	if typeof( lhs) != NumVal || typeof( rhs ) != NumVal
		throw(LispError("Invalid arg type! Expecting a NumVal"))
	end

	if (ast.op == (/))
		if ( rhs.n == 0)
			throw( LispError("Cannot divide by 0") )
		end
	end

	return NumVal( ast.op( lhs.n, rhs.n ) )
end

function calc( ast::SoloNode, env::Environment )
	# println("\nCalculating Solo\n\tAST = ", ast)

	n = calc( ast.n, env )
	if typeof( n ) != NumVal
		throw(LispError("Invalid arg type! Expecting a NumVal"))
	end

	if ( ast.op == (-) )
		return NumVal( 0 - n.n )
	else
		if ( n.n < 1 )
			throw(LispError("Arg for collatz must be >= 1!"))
		end
		return NumVal( collatz( n.n ) )
	end
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

function calc( ast::If0Node, env::Environment )
    cond = calc( ast.condition, env )
    if cond.n == 0
        return calc( ast.zero_branch, env )
    else
        return calc( ast.nonzero_branch, env )
    end
end

function calc( ast::WithNode, env::Environment )
	# println("\nCalculating withNode\n\tAST=", ast)
	ext_env = env
	for (k,v) in ast.param
		binding_val = calc( v, ext_env )
		ext_env = ExtendedEnv( k.sym, binding_val, ext_env )
	end

	return calc( ast.body, ext_env )
end

function calc( ast::FunDefNode, env::Environment )
	if length( ast.formal ) == 0
		return calc( ast.fun_body )
	end
    return ClosureVal( ast.formal, ast.fun_body , env )
end

function calc( ast::FunAppNode, env::Environment )
	println("\nCalculating FunAppNode\n\tAST = ", ast)

    closure_val = calc( ast.fun_expr, env )

	if ( typeof(closure_val) != ClosureVal )
		throw( LispError("FunAppNode: fun_expr returns wrong type (not ClosureVal"))
	end

	ext_env = closure_val.env
	println("FunAppNode: ast.arg_expr is ", ast.arg_expr, " of type ", typeof(ast.arg_expr))

	for (k,v) in ast.arg_expr
		binding_val = calc( v, ext_env )
		ext_env = ExtendedEnv( k.sym, binding_val, ext_env )
	end

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
	println("\nDONE parsing\n\tast = $ast")
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
