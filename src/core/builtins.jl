Priv() = Any
Priv(T::DataType) = T

NoData() = Any
NoData(T::DataType) = T

"A wrapper for Flux.Params, so we can control mutation."
mutable struct DMParams
   params :: Flux.Params
end

"A wrapper for Zygote.Grads, so we can control what you can do with gradients."
mutable struct DMGrads
   grads :: Zygote.Grads
end


"Subtract the gradients from the parameters."
function subtract_gradient!(ps::DMParams, gs::DMGrads)
   ps.params .-= gs.grads
end


"Make the input gradient DP by applying the gaussian mechanism."
function gaussian_mechanism!(s::Real, ϵ::Real, δ::Real, f::DMGrads)
   noise!(ff) = ff + rand(Normal(0, (2 * log(1.25/δ) * s^2) / ϵ^2))
   map!(ff -> noise!.(ff), f.grads, f.grads) # apply noise element-wise
end

"Clip the gradient, i.e. scale by 1/norm(g) if norm(g)>1."
function clip!(l::Norm, g::DMGrads)

    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    n = norm(g.grads, p)

    if n > 1
       g.grads .*= (1/n)
    end
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

builtin_mutations = Dict(
                         :gaussian_mechanism! => gauss,
                         :clip! => dmclip,
                         :subtract_gradient! => dmsubgrad
                        )

is_builtin_op(f::Symbol) = haskey(builtin_ops,f)
is_builtin_mutation(f::Symbol) = haskey(builtin_mutations,f)
is_builtin(f::Symbol) = is_builtin_op(f) || is_builtin_mutation(f)

"Get a map from some argument `DMType`s to the `DMTypeOp` corresponding to the input julia function."
getDMOp(f::Symbol) = is_builtin_op(f) ? builtin_ops[f] : error("Unsupported builtin op $f.")


