"Make the input function DP by applying the gaussian mechanism."
function gaussian_mechanism(s::Real, ϵ::Real, δ::Real, f::Function) :: Function
    plusrand(y) = y + rand(Normal(0, (2 * log(1.25/δ) * s^2) / ϵ^2))
    (x...) -> plusrand.(f(x...)) # apply noise element-wise to make it work on matrix-valued f's too
end

"Clip the input matrix, that is, normalize all rows that have norm > 1."
function clip(l::Norm, m::Union{Matrix, Vector})

    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    # TODO julia is col-major, we should switch...
    mapslices(r -> norm(r,p) > 1 ? normalize(r,p) : r, m, dims = [ndims(v)])
end
