
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




# we're only interested in the privacy of the `data` and `labels` inputs so all other parameters
# get a `Static()` annotation. it's a privacy function, so we annotate it with `Priv()`.
# k specifies the number of times we iterate the whole dataset
# eta is the learning rate
# the version without minibatching
# this version does not use a for loop to iterate the dataset, hence we can prove a better privacy bound
function train_dp_nobatch_noloop(data::Matrix{<:Data}, labels::Matrix{<:Data}, eps::Static(), del::Static(), eta::Static(), k::Static(Integer)) :: Priv()
   # initialize a Flux model.
   n_paramss2 = 31810
   model23 = unbox(init_model(), DMModel, n_paramss2)

   # the computation we do on each data row seperately. 
   function body!(d, l, model::Static()) :: Priv()
      # compute gradient for current model
      gs2 = unbox(unbounded_gradient(model, d, l), DMGrads, n_paramss2)

      # noise gradient
      clip!(L2,gs2)
      norm_convert!(gs2)
      gaussian_mechanism!(2, eps, del, gs2)

      # scale with learning rate and update model
      scale_gradient!(eta, gs2)
      subtract_gradient!(model, gs2)
      return
   end

   # run body on whole dataset once for each of the k epochs
   for _ in 1:k
      parallel_private_fold_rows!(body!, model23, data, labels)
   end

   model23
end

function train_dp(data::Matrix{<:Data}, labels::Matrix{<:Data}, eps::Static(), del::Static(), eta::Static(), k::Static(Integer), b::Static(Integer)) :: Priv()
   # initialize a Flux model.
   n_params = 31810
   model = unbox(init_model(), DMModel, n_params)
   for i in 1:k
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
      scale_gradient!(1/b, G)
      gaussian_mechanism!(2, eps, del, G)

      # update the model by subtracting the noised gradient scaled by the learning rate eta.
      scale_gradient!(eta, G)
      subtract_gradient!(model, G)
   end
   model
end


end
