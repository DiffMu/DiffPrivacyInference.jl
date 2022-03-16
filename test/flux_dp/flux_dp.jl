
module FluxDP
using DiffPrivacyInference
# this code is checkable with our typechecker. the inference result will be the type of the last function
# in the file, containing the inferred privacy bound as well as constraints on the input variables.

# only imports are permitted, so you cannot use functions from other packages without qualifying them.
# qualified names cannot be used in functions whose body is supposed to be checked by us, but only
# in black-box functions that will be ignored by the type checker.
import Flux

# a black-box function using qualified names to call functions from Flux.
# the typechecker will just ignore the body of this function and assign infinite sensitivity to all
# arguments. note that if you mutate any of the arguments, the typechecking result will be invalid,
# but the typechecker will not warn you about it.
function unbounded_gradient(model::DMModel, d, l) :: BlackBox()
   gs = Flux.gradient(Flux.params(model.model)) do
           loss(d,l,model)
        end
   return DMGrads(gs)
end

# a black-box function initializing a Flux neural network. To make it work with typecheckable code,
# the model has to be wrapped in our `DMModel` struct.
function init_model() :: BlackBox()
 DMModel(Flux.Chain(
         Flux.Dense(28*28,40, Flux.relu),
         Flux.Dense(40, 10),
         Flux.softmax))
end

# the loss function for our training. using a function from Flux, so it's a black-box too.
loss(X, y, model) :: BlackBox() = Flux.crossentropy(model.model(X), y)


function train_dp(data::Matrix{<:Real}, labels::Matrix{<:Real}, eps::NoData(), del::NoData(), eta::NoData(), k::NoData(Integer), b::NoData(Integer)) :: Priv()
   # initialize a Flux model.
   n_params = 31810
   model = unbox(init_model(), DMModel, n_params)
   (dim, _) = size(data)
   for i in 1:k*(dim/b)
      D, L = sample(b, data, labels)
      G = zero_gradient(model)

      for j in 1:b
         # compute the gradient at the j-th data point
         d = D[j,:]
         l = L[j,:]
         gs = unbox(unbounded_gradient(model, d, l), DMGrads, n_params)

         # clip the gradient
         clip!(L2,gs)
         norm_convert!(gs)

         # aggregate sum of batch gradients
         G = sum_gradients(gs,G)
      end

      # apply the gaussian mechanism to the batch mean gradient.
      # scaling G bounds it's sensitivity to 2/dim, so the noise
      # required to make it DP stays reasonable.
      scale_gradient!(1/b, G)
      gaussian_mechanism!(2, eps, del, G)

      # update the model by subtracting the noised gradient scaled by the learning rate eta.
      scale_gradient!(eta, G)
      subtract_gradient!(model, G)
   end
   model
end

# we're only interested in the privacy of the `data` and `labels` inputs so all other parameters
# get a `NoData()` annotation. it's a privacy function, so we annotate it with `Priv()`.
# k specifies the number of times we iterate the whole dataset
# b specifies the minibatch size
# eta is the learning rate
# the version without minibatching
function train_dp_nobatch(data::Matrix{<:Real}, labels::Matrix{<:Real}, eps::NoData(), del::NoData(), eta::NoData()) :: Priv()
   # initialize a Flux model.
   n_params2 = 31810
   model2 = unbox(init_model(), DMModel, n_params2)
   (dim2, _) = size(data)
      for j2 in 1:dim2
         # compute the gradient at the j-th data point
         d = data[j2,:]
         l = labels[j2,:]
         gs2 = unbox(unbounded_gradient(model2, d, l), DMGrads, n_params2)
   
         # clip the gradient
         clip!(L2,gs2)
         norm_convert!(gs2)
   
         # apply the gaussian mechanism to the batch mean gradient.
         # scaling G bounds it's sensitivity to 2/dim, so the noise
         # required to make it DP stays reasonable.
         gaussian_mechanism!(2, eps, del, gs2)
   
         # update the model by subtracting the noised gradient scaled by the learning rate eta.
         # we also re-scale the gradient by `b` to make up for the scaling earlier.
         scale_gradient!(eta, gs2)
         subtract_gradient!(model2, gs2)
   end
   model2
end


# we're only interested in the privacy of the `data` and `labels` inputs so all other parameters
# get a `NoData()` annotation. it's a privacy function, so we annotate it with `Priv()`.
# k specifies the number of times we iterate the whole dataset
# b specifies the minibatch size
# eta is the learning rate
# the version without minibatching
function train_dp_noloop(data::Matrix{<:Real}, labels::Matrix{<:Real}, eps::NoData(), del::NoData(), eta::NoData(), k::NoData(Integer)) :: Priv()
   # initialize a Flux model.
   n_paramss2 = 31810
   model23 = unbox(init_model(), DMModel, n_paramss2)
   function body(d, l, model::NoData()) :: Priv()
      gs2 = unbox(unbounded_gradient(model, d, l), DMGrads, n_paramss2)
       # clip the gradient
      clip!(L2,gs2)
      norm_convert!(gs2)
 
      gaussian_mechanism!(2, eps, del, gs2)
      scale_gradient!(eta, gs2)
      subtract_gradient(model, gs2)
   end
   for _ in 1:k
      model23 = parallel_private_fold_rows(body, model23, data, labels)
   end
   model23
end

end
