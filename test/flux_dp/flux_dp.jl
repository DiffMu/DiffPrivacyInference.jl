using Flux

function unbounded_gradient(loss, ps::DMParams, d::Vector, l::Vector) :: BlackBox()
   gs = gradient(ps.params) do
           loss(d,l)
        end
   return DMGrads(gs)
end

function train_dp!(loss::NoData(), ps::NoData(), data, labels, eps::NoData(), del::NoData(), eta::NoData()) :: Priv()
   (n,) = size(data)
   for j = 1:100
       for i in 1:n
          d = data[i,:]
          l = labels[i]
          gs = unbounded_gradient(loss, ps, d, l)

          clip!(L2,gs)
          gaussian_mechanism!(1/n, eps, del, gs)
          subtract_gradient!(ps,gs)
       end
   end
end

model = Chain(Dense(784,32,σ),Dense(32,10),softmax)
loss(x,y) = Flux.mse(model(x),y)
data = rand(1000,784)
labels = [ones(10) for _ in 1:1000]

train_dp!(loss, DMParams(Flux.params(model)), data, labels, 1, 1, 1)
