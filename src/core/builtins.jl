"Make the input function DP by applying the gaussian mechanism."
function gaussian_mechanism(s::Real, ϵ::Real, δ::Real, f::Function)
    plusrand(y) = y + rand(Normal(0, (2 * log(1.25/δ) * s^2) / ϵ^2))
    (x...) -> plusrand.(f(x...)) # apply noise element-wise to make it work on matrix-valued f's too
end
