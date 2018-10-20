#
# TransInt
#

module TransInt
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
opArray = [:if0, :with, :lambda, :mod, :collatz, :id, :and]

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
  formal::Array{Any}
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

struct PlusNode <: AE
	operands::Array{Any}
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

#(and <AE> <AE> <AE>*)
struct AndNode <: AE
	args_list::Array{Any}
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
			if ( expr[1] == :+ )
				println("it's plusNode. ", expr[2:end])
				if ( length(expr[2:end]) < 2 )
					throw(LispError("Invalid argument numbers!"))
				end
				pn_operands = []
				for operand in expr[2:end]
					push!( pn_operands, parse( operand ) )
				end
				println("PlusNode operands array = $pn_operands")
				return PlusNode( pn_operands )

			else # more than 2 args but not a Plus Op => Invalid
				throw(LispError("Invalid argument numbers!"))
			end

		end


	# CASE 2: including op from interpreter 2 [ :if0, :lambda, :with ]
	elseif ( expr[1] == :if0 ) || ( expr[1] == :with ) || ( expr[1] == :lambda ) || ( expr[1] == :and )

		if (expr[1] == (:if0)) #if0 always has 4 arguments: :if0, condition, zerobranch ,nonzero_branch
			# println("\nParsing If0Node")
			if (length(expr) != 4)
				throw(LispError("Invalid number of Arguments. If0 takes in 3 args"))
			end
			return If0Node( parse(expr[2]), parse(expr[3]), parse(expr[4]) )

		elseif expr[1] == :and
			if ( length( expr[2:end] ) < 2 )
				throw(LispError("Invalid number of Arguments. And takes at least 2 args <AE><AE><AE>*"))
			end
			and_param = []
			for p in expr[2:end]
				push!(and_param, parse( p ) )
			end
			println("\tand_param = $and_param")
			return AndNode(and_param)

		elseif expr[1] == :with
			# println("\nParsing WithNode")
			param_dict = Dict()
			# println(expr[2], " type = ", typeof(expr[2][1]))
			for i in 1:(length(expr[2]))
				# println(" $i type = ", typeof(expr[2][i]))

				#make sure binding is in correct syntax ((x 1)) instead of (x 1)
				if ( typeof( expr[2][i] ) != Array{Any,1} )
					throw(LispError("With: invalid representation of binding"))
				end

				# make sure arg does not match grammar symbols
				# if haskey( opDict, expr[2][i][1] ) || ( expr[2][i][1] in opArray )
				if ( !symbol_is_valid( expr[2][i][1] ) )
					throw(LispError("Arguments of cannot match grammar symbols"))
				end

				# make sure arg has a unique name (not already in the list of args symbols)
				if haskey(param_dict, expr[2][i][1] )
					throw(LispError("Arguments of a multiple_args_with must have distinct names"))
				end

				param_dict[ parse( expr[2][i][1] ) ] = parse( expr[2][i][2] )
			end
			return WithNode( param_dict, parse(expr[end]) )

		elseif expr[1] == :lambda
			println("Parsing FunDefNode")

			param_array = []

			#make sure Param is in correct syntax ( x ) instead of x
			if ( typeof( expr[2]) != Array{Any,1} )
				throw(LispError("FunDefNode -- lambda: invalid representation of param"))
			end

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
				push!(param_array, parse(expr[2][i]) )
			end
			println("PARSE: about to return FunDefNode")
			return FunDefNode( param_array, parse(expr[end]) )
		end

	# CASE 3: if expr[1] is not a grammar symbol =>> (FunAppNode or Invalid)
	else
		fun_expr = parse( expr[1] )

		if typeof( fun_expr ) == FunDefNode
			# make sure number of formal_args ==  number of actual_args
			if length(fun_expr.formal) != ( length(expr)-1 )
				throw(LispError("FunAppNode Error: number of actual args does not match number of formal args"))
			end

			# create Dict to store list of (formal_arg: actual_arg)
			param_dict = Dict()
			index = 2

			println("type of fun_expr.formal is $(typeof(fun_expr.formal))\n\tfun_expr.formal = $(fun_expr.formal)")
			for p in fun_expr.formal
				println()
				current_actual = parse( expr[index] ) # calculate actual_arg[i] =>> should return NumNode

				# make sure actual_args calculates to a number (type NumNode before calc)
				if ( typeof( current_actual ) != NumNode )
					throw(LispError("FunAppNode Error: Invalid Actual Param Arguments"))
				end
				println("\tcurrentactual = $current_actual of type $(typeof(current_actual))")
				param_dict[ p ] = current_actual
				index += 1
			end

			return FunAppNode( fun_expr, param_dict )

		else
			param_dict = Dict()
			for i in 2:length(expr)
				param_dict[ parse(i) ] = parse(expr[i])
			end

			return FunAppNode(fun_expr, param_dict)
		end
	end
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

function analyze( ast::SoloNode )
	aOperand = analyze( ast.n )

	if typeof(aOperand) == NumNode
		return NumNode( ast.op( aOperand.n ) )
	end
	return SoloNode( ast.op, aOperand )
end

function analyze( ast::BinopNode )
	println("Starting analyzing BinopNode : $ast")
    alhs = analyze( ast.lhs )
    arhs = analyze( ast.rhs )

    if typeof(alhs) == NumNode && typeof(arhs) == NumNode

		if ( ast.op == / ) #ast.op after parse is now a function, not symbol
			if (arhs == NumNode(0))
				throw( LispError("At Analyze: Cannot divide by 0") )
			end
		end

        return NumNode( ast.op( alhs.n, arhs.n ) )
    end

    return BinopNode( ast.op, alhs, arhs )
end

function analyze( ast::PlusNode )
	println("analyzing: plusnode = $ast")
	if ( length(ast.operands) == 2 )
		println("base case")
		return analyze( BinopNode( +, ast.operands[1], ast.operands[2] ) )
	else
		println("not done")
		return analyze( BinopNode( +, ast.operands[1], analyze( PlusNode( ast.operands[2:end] ) ) ) )
	end
end

function analyze( ast::If0Node )
	println("\nanalyzing: If0Node $ast")
    acond = analyze( ast.condition )
	println("\tacond = $acond")

    if typeof( acond ) == NumNode
        if acond.n == 0
			println("0 branch: $(ast.zero_branch)")
            return analyze( ast.zero_branch )
        else
			println("1 branch: $(ast.nonzero_branch)")
            return analyze( ast.nonzero_branch )
        end
    end

    azb = analyze( ast.zero_branch )
    anzb = analyze( ast.nonzero_branch )
    return If0Node( acond, azb, anzb )
end

function analyze( ast::AndNode )
	println("\nanalyzing: AndNode = $ast")
	if ( length(ast.args_list) == 1 )
		println("base case")
		println(" analyze( ast.args_list[1] = $( analyze( ast.args_list[1] ))")
		return analyze( If0Node( analyze( ast.args_list[1] ), NumNode(0), NumNode(1) ) )
	else
		println("not done")
		return analyze( If0Node( analyze( ast.args_list[1] ), NumNode(0), analyze( AndNode( ast.args_list[2:end] ) ) ) )
		# return analyze( BinopNode( +, ast.operands[1], analyze( PlusNode( ast.operands[2:end] ) ) ) )
	end
end

function analyze( ast::WithNode )
	println("Analyzing WithNode\n\t\t $ast")

	fdn_formal_array = []
	fan_arg_expr = Dict()
	for i in ast.param
		println("\t\t$(i[1]) => $(i[2])")
		push!(fdn_formal_array, i[1])
		fan_arg_expr[ i[1] ] = i[2]
	end
	fdn = FunDefNode( fdn_formal_array, analyze( ast.body ))
	println("\tfdn = $fdn")
	println("\tfan_arg_expr = $fan_arg_expr")
	# return ast
	return FunAppNode( fdn, fan_arg_expr )
end

function analyze( ast::FunDefNode )
	println("Analyzing FunDefNode\n\t\t $ast")
    return FunDefNode( ast.formal, analyze( ast.fun_body ) )
end
#
function analyze( ast::FunAppNode )
	println("Analyzing FunAppNode\n\t\t $ast")
	fan_arg_expr = Dict()
	for i in ast.arg_expr
		fan_arg_expr[ analyze( i[1] ) ] = analyze( i[2] )
	end
	# return ast
    return FunAppNode( analyze( ast.fun_expr), fan_arg_expr )
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
	closure_val = calc( ast.fun_expr, env )

	if ( typeof(closure_val) != ClosureVal )
		throw( LispError("FunAppNode: fun_expr returns wrong type (not ClosureVal"))
	end

	ext_env = closure_val.env
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
    revised_ast = analyze(ast)
	println("\nFinished Analyzing. revised_ast is $revised_ast")
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
