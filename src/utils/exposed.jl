
function build_tc(t::DMTerm) :: TC
    d = Dict{Symbol,Array{DMTerm,1}}()
    @mdo TC begin
        r1m <- mcheck_sens(t, d)
        tau <- simplify_constraints_lose_generality()
        r <- apply_subs(r1m)
        return r
    end
end

function infer_sensitivity_from_string(s::String)
    t = string_to_dmterm(s)
    infer_sensitivity(t)
end

function infer_sensitivity_from_file(file::AbstractString)
    t = file_to_dmterm(file)
    infer_sensitivity(t)
end

function infer_sensitivity(t::DMTerm)
    d = Dict{Symbol,Array{DMTerm,1}}()
    m = build_tc(t)
    (c, τ) = run(m)
end
