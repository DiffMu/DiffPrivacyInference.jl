import Flux

function unbounded_gradient(loss, model::DMModel, d::Vector, l::Vector) :: BlackBox()
   gs = Flux.gradient(model.params) do
           loss(d,l)
        end
   return DMGrads(gs)
end

function train_dp!(loss::NoData(), model::NoData(DMModel), data, labels, eps::NoData(), del::NoData(), eta::NoData()) :: Priv()
   (n,) = size(data)
   for i in 1:n
      d = data[i,:]
      l = labels[i]
      gs = unbounded_gradient(loss, model, d, l)

      clip!(L2,gs)
      gaussian_mechanism!(1/n, eps, del, gs)
      subtract_gradient!(model,gs)
   end
end


model = DMModel(Flux.Chain(Flux.Dense(784,32,Flux.σ),Flux.Dense(32,10),Flux.softmax))
loss(x,y) = Flux.mse(model.model(x),y)
#data = rand(1000,784)
#labels = [ones(10) for _ in 1:1000]


(data, labels) -> train_dp!(loss, model, data, labels, 1, 1, 1)
