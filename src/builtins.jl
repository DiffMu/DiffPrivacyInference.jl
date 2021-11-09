
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

Robust() = Any
Robust(T::DataType) = T

convert(m) = m

"A wrapper for Flux.Params, so we can control mutation."
mutable struct DMModel
   model # a flux model
end

"A wrapper for Zygote.Grads, so we can control what you can do with gradients."
mutable struct DMGrads
   grads :: Zygote.Grads
end


"Subtract the gradients from the parameters."
function subtract_gradient(m::DMModel, gs::DMGrads) :: DMModel
   cm = deepcopy(m.model)
   cp = Flux.params(cm)
   p = Flux.params(m.model)
   for i in 1:length(Flux.params(m).order.data)
      cp[i] .-= gs.grads[p[i]]
   end
   return DMModel(cm)
end

copy_grad(g::DMGrads) :: DMGrads = DMGrads(Zygote.Grads(IdDict(deepcopy(g.grads.grads)), g.grads.params))

"Make the input gradient DP by applying the gaussian mechanism."
function gaussian_mechanism(s::Real, ϵ::Real, δ::Real, f::DMGrads) :: DMGrads
   cf = copy_grad(f)
   noise!(ff) = ff + rand(Normal(0, (2 * log(1.25/δ) * s^2) / ϵ^2))
   map!(ff -> noise!.(ff), cf.grads, cf.grads) # apply noise element-wise
   return cf
end

"Clip the gradient, i.e. scale by 1/norm(g) if norm(g)>1."
function clip(l::Norm, g::DMGrads) :: DMGrads

    p = @match l begin
        L1 => 1
        L2 => 2
        L∞ => Inf
    end

    cg = copy_grad(g)

    n = norm(cg.grads, p)

    if n > 1
       cg.grads .*= (1/n)
    end

    return cg
end

