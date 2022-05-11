

include("builtins_types.jl")
include("builtins_sensitivity.jl")
include("builtins_privacy.jl")

###########################################
# Internal use
function internal_expect_const(a)
    a
end

mutable struct Box
    internal_box_content
end

function new_box(m)
    Box(m)
end

function get_box(m)
    m.internal_box_content
end

function map_box!(f,m)
    m.internal_box_content = f(m.internal_box_content)
end


