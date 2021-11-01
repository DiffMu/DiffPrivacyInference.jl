import Flux

function unbounded_gradient(model::DMModel, d::Vector, l::Vector) :: BlackBox()
   gs = Flux.gradient(Flux.params(model.model)) do
           loss(d,l,model)
        end
   return DMGrads(gs)
end

function init_model() :: BlackBox()
   DMModel(Flux.Chain(Flux.Dense(20,100,Flux.σ),Flux.Dense(100,10),Flux.softmax))
end

loss(x,y,model) :: BlackBox() = Flux.mse(model.model(x),y)

function train_dp(data, labels, eps::NoData(), del::NoData(), eta::NoData()) :: Priv()
   model = init_model()
   (n,m) = size(data)
   for _ in 1:eta
       for i in 1:n
          d = data[i,:]
          l = labels[i]
          gs = unbounded_gradient(model, d, l)

          gs = clip(L2,gs)
          gs = gaussian_mechanism(1/n, eps, del, gs)
          model = subtract_gradient(model,gs)
       end
   end
   model
end


