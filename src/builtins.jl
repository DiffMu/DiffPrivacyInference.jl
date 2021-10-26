
@data Norm begin
    L1
    L2
    L∞
end

@data Unbounded begin
    U
end

Clip = Union{Norm, Unbounded}


Priv() = Any
Priv(T::DataType) = T

NoData() = Any
NoData(T::DataType) = T

BlackBox() = Any
BlackBox(T::DataType) = T

"A wrapper for Flux.Params, so we can control mutation."
mutable struct DMModel
   model
   params :: Flux.Params
   DMModel(m) = new(m, Flux.params(m))
end

"A wrapper for Zygote.Grads, so we can control what you can do with gradients."
mutable struct DMGrads
   grads :: Zygote.Grads
end


"Subtract the gradients from the parameters."
function subtract_gradient!(ps::DMModel, gs::DMGrads)
   for p in ps.params
      p .-= gs.grads[p]
   end
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

