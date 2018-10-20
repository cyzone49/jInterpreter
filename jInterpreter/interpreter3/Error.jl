module Error

export LispError

struct LispError <: Exception
    msg::AbstractString
end

end #module
