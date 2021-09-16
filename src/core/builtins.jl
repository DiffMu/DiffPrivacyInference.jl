Priv() = Any
Priv(T::DataType) = T

NoData() = Any
NoData(T::DataType) = T

"A wrapper for Flux.Params, so we can control mutation."
struct DMParams
   params :: Flux.Params
end

"A wrapper for Zygote.Grads, so we can control what you can do with gradients."
struct DMGrads
   grads :: Zygote.Grads
end


"Subtract the gradients from the parameters."
function subtract_gradient!(ps::DMParams, gs::DMGrads)
   ps.params .-= gs.grads
end


"Make the input function DP by applying the gaussian mechanism."
function gaussian_mechanism(s::Real, ϵ::Real, δ::Real, f)
   noise(ff) = ff + rand(Normal(0, (2 * log(1.25/δ) * s^2) / ϵ^2))
   map(ff -> noise.(ff), f) # apply noise element-wise to make it work on matrix-valued f's too
end

#=
"Clip the input matrix, that is, normalize all rows that have norm > 1."
function clip(l::Norm, m::Union{Matrix, Vector})

    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    # TODO julia is col-major, we should switch...
    mapslices(r -> norm(r,p) > 1 ? .   mul!(r, (1/norm(r,p))) : r, m, dims = [ndims(v)])
end
=#

function clip(l::Norm, m)

    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    n = norm(m, p)

    n > 1 ? (m .* (1/n)) : m
end


####################################################################
# julia interface

builtin_ops = Dict(
                   :ceil => (1, τs -> Unary(DMOpCeil(), τs...)),
                   :+ => (2, τs -> Binary(DMOpAdd(), τs...)),
                   :- => (2, τs -> Binary(DMOpSub(), τs...)),
                   :* => (2, τs -> Binary(DMOpMul(), τs...)),
                   :/ => (2, τs -> Binary(DMOpDiv(), τs...)),
                   :% => (2, τs -> Binary(DMOpMod(), τs...)),
                   :rem => (2, τs -> Binary(DMOpMod(), τs...)),
                   :(==) => (2, τs -> Binary(DMOpEq(), τs...)),
                  )

is_builtin_op(f::Symbol) = haskey(builtin_ops,f)
is_builtin(f::Symbol) = haskey(builtin_ops,f) || f in [:clip, :gaussian_mechanism, :subtract_gradient!]

"Get a map from some argument `DMType`s to the `DMTypeOp` corresponding to the input julia function."
getDMOp(f::Symbol) = is_builtin_op(f) ? builtin_ops[f] : error("Unsupported builtin op $f.")


