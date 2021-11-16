import Flux

function unbounded_gradient(model::DMModel, d::Vector, l) :: BlackBox()
   gs = Flux.gradient(Flux.params(model.model)) do
           loss(d,l,model)
        end
   return DMGrads(gs)
end

function init_model() :: BlackBox()
 DMModel(Flux.Chain(
         Flux.Dense(28*28,40, Flux.relu),
         Flux.Dense(40, 10),
         Flux.softmax))
end

loss(X, y, model) = Flux.crossentropy(model.model(X), y)

function train_dp(data, labels, eps::NoData(), del::NoData(), eta::NoData(), n::NoData()) :: Priv()
   model = init_model()
   dim = size(data)[1]
   aloss = 0
   for _ in 1:n
       for i in 1:dim
          d = data[i,:]
          l = labels[i]
          gs = unbounded_gradient(model, d, l)

          gs = clip(L2,gs)
          gs = gaussian_mechanism(1/n, eps, del, gs)
          model = subtract_gradient(model, scale_gradient(eta,gs))
          aloss += loss(d,l,model)/(n*dim)

       end
   end
   println("avg loss: $aloss")
   model
end

