# Learning MNIST, verified differentially private
This directory contains a toy example that trains a simple neural network modelled using the [Flux.jl machine learning library](https://github.com/FluxML/Flux.jl) to recognize handwritten digits. Our typechecker can verify that the function doing the gradient descent for training satisfies given differential privacy bounds. We walk through most of the code here.

## Noisy gradient descent, implemented in the [`flux_dp.jl`](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/test/flux_dp/flux_dp.jl) file
This file contains an implementation of noisy gradient descent, guided by the example in section 5.6 of the [duet paper](https://arxiv.org/abs/1909.02481).

First, we import the Flux library. Note that including modules means one has to qualify everything one uses from the model, like `Flux.gradient` to call the gradient function. This is necessary, as it enables us to discern between imported and homemade things in the code.
```
import Flux
```

Next, we define a function that initializes a small Flux neural network model. It uses stuff imported from the Flux module. As we cannot expect that code to be checkable (see [this paragraph](https://github.com/DiffMu/DiffPrivacyInference.jl#how-to-write-checkable-code) on what checkable code needs to look like), we declare this function a so-called *black box* and signify this with the `BlackBox()` annotation. This means the typechecker will ignore the code inside the function body and assume it hase infinite sensitivity in all it's arguments (of which this specimen has none).
Note that the Flux model is not returned by the function as-is, but wrapped in our `DMModel` type. It's really just a plain wrapper, but as you cannot access it's content in checkable code, this allows us to control what you do with your model in the part of the program that is relevant for analysis.
```
function init_model() :: BlackBox()
 DMModel(Flux.Chain(
         Flux.Dense(28*28,40, Flux.relu),
         Flux.Dense(40, 10),
         Flux.softmax))
end
```

The loss function for our training not onlu uses a function from Flux, but also accesses the Flux model wrapped in the `model` field of the input `DMModel`. Hence it's a black box too.
```
loss(X, y, m) :: BlackBox() = Flux.crossentropy(m.model(X), y)
```

The function computing the gradient from a model and data and label vectors is a black box, too. Note that just like models, gradients have to be wrapped in our `DMGrads` type.
```
function unbounded_gradient(m::DMModel, d::Vector, l) :: BlackBox()
   gs = Flux.gradient(Flux.params(m.model)) do
           loss(d,l,m.model)
        end
   return DMGrads(gs)
end
```

Now comes the only function whose body ist actually typechecked: the gradient descent training algorithm. There is a lot going on here:

- We're only interested in the privacy of the `data` and `labels` inputs, so all other parameters get a `Static()` annotation.
- It's supposed to be a differentially private function, so we annotate it with `Priv()`.
- It initializes the network and iterates over all data/label pairs, computing the gradient and making differentially private updates to the model.
- There is a few peculiarities concerning that last part:
   - Model updates and gradient operations (like scaling) can only be done using our very limited set of builtin functions for that purpose. See [here](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/src/builtins.jl) for the definitions of these.
   - Differential privacy is a property expressed using a notion of distance between inputs of a function. This means all vectors, matrices, gradients and models in our code carry a norm describing which notion of distance is used for which object (See [this pdf](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/docs/matrixnorms/matrixnorms.pdf) and section 4.2 of the [duet paper](https://arxiv.org/abs/1909.02481) for more on the topic). Here, we use the `norm_convert` builtin function to make the clipped gradient measured using the discrete norm into a gradient measured with the clipping norm (`L2`, here) instead. This is necessary as the gradient obtained from a black box computation lives in discrete-norm land, while the Gaussian machanism expects the input to live in L2-norm land (see the `mgauss` rule on page 43 of the [duet paper](https://arxiv.org/abs/1909.02481)).
```
function train_dp(data::Matrix{<:Real}, labels::Matrix{<:Real}, eps::Static(), del::Static(), eta::Static(), k::Static(Integer), b::Static(Integer)) :: Priv()
   # initialize a Flux model. as this is a black box, we have to use `unbox` and provide
   # return type and number of parameters of the returned model.
   n_params = 31810
   model = unbox(init_model(), DMModel, n_params)
   
   # loop for k epochs.
   for i in 1:k
      # sample a submatrix of `b` rows simultaneously from data and labels.
      D, L = sample(b, data, labels)
      G = zero_gradient(model)

      # iterate through all samples
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
```

## Typechecking this
To typecheck the file, make the following call in the julia REPL:
```
julia> typecheck_from_file("test/flux_dp/flux_dp.jl")

Type:
{
  -  Matrix<n: LInf, c: τ_24>[s_15 × s_10](Data[--])
      @ (4.0⋅s_22⋅s_73⋅(1 / s_15)⋅sqrt(2.0⋅ceil(s_64)⋅(∑∅ - ln(s_60))), s_73⋅ceil(s_64)⋅(1 / s_15)⋅s_23 + s_60)
  
  -  Matrix<n: LInf, c: τ_24>[s_15 × s_14](Data[--])
      @ (4.0⋅s_22⋅s_73⋅(1 / s_15)⋅sqrt(2.0⋅ceil(s_64)⋅(∑∅ - ln(s_60))), s_73⋅ceil(s_64)⋅(1 / s_15)⋅s_23 + s_60)
  
  -  τ_115[s_22 ©]
      @ (∑∅, ∑∅)
  
  -  τ_117[s_23 ©]
      @ (∑∅, ∑∅)
  
  -  τ_129[s_62 ©]
      @ (∑∅, ∑∅)
  
  -  Int[s_64 ©]
      @ (∑∅, ∑∅)
  
  -  Int[s_73 ©]
      @ (∑∅, ∑∅)
  --------------------------
   ->* DMModel[31810.0]

}
---------------------------------------------------------------------------
Constraints:
   - top:
constr_52 : IsLessEqual (2.0⋅ceil(s_73)⋅(1 / s_73),2.0)
  Restricting the variable:  D
  In the gauss call Gauss (2.0, gen_eps_uls_11, gen_del_uls_12, gen_G#_40_10)
  All variables which are *NOT* annotated as 'Static' and are used in the body gen_G#_40_10
  Have to have sensitivity <=  2.0
,
constr_21 : IsLess (∑∅,s_22)
  In test/flux_dp/flux_dp.jl: line 97
  In test/flux_dp/flux_dp.jl: line 97
  Gauss epsilon parameter must be > 0
,
constr_65 : IsLessEqual (s_60,1)
  In test/flux_dp/flux_dp.jl: line 77
  This variable can be chosen freely <= 1
,
constr_51 : IsLessEqual (2.0⋅ceil(s_73)⋅(1 / s_73),2.0)
  Restricting the variable:  L
  In the gauss call Gauss (2.0, gen_eps_uls_11, gen_del_uls_12, gen_G#_40_10)
  All variables which are *NOT* annotated as 'Static' and are used in the body gen_G#_40_10
  Have to have sensitivity <=  2.0
,
constr_22 : IsLess (∑∅,s_23)
  In test/flux_dp/flux_dp.jl: line 97
  In test/flux_dp/flux_dp.jl: line 97
  Gauss delta parameter must be > 0
,
constr_66 : IsLess (∑∅,s_60)
  In test/flux_dp/flux_dp.jl: line 77
  This variable can be chosen freely > 0
,
constr_20 : IsLess (s_23,1)
  In test/flux_dp/flux_dp.jl: line 97
  In test/flux_dp/flux_dp.jl: line 97
  Gauss delta parameter must be <= 1
,
constr_19 : IsLess (s_22,1)
  In test/flux_dp/flux_dp.jl: line 97
  In test/flux_dp/flux_dp.jl: line 97
  Gauss epsilon parameter must be <= 1

   - others:
[]
()
```
That's rather verbose at the moment. It says that given the constraints in the list hold, the function is `(4.0⋅s_22⋅s_73⋅(1 / s_15)⋅sqrt(2.0⋅ceil(s_64)⋅(∑∅ - ln(s_60))), s_73⋅ceil(s_64)⋅(1 / s_15)⋅s_23 + s_60)`-private in its first and second arguments (the data and labels matrices, whose dimensions are denoted `[s_15 × s_10]` and `[s_15 × s_14]`), and zero-private in the following (the `eps` and `del` parameters, whose values are denoted `s_22` and `s_23` in the result, the `eta` parameter, denoted `s_62` and the number of epochs `k` and batch size `b`, denoted `s_64` and `s_73`).

## Learning MNIST, implemented in [`mnist.jl`](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/test/flux_dp/mnist.jl)
To use the above algorithm, we need to call the `train_dp` function. The inferred differential privacy is a property of the algorithm, but we cannot typecheck the code that actually calls the function with some actual data that's loaded from somewhere. This has to happen in a seperate file where you can use the checked function, but bear the responsibility of using it correcly.

First, we load the MNIST dataset, containing loads of images of handwritten digits and the corresponding labels.
```
using Flux

# get MNIST dataset
images = Flux.Data.MNIST.images();
labels = Flux.Data.MNIST.labels();
```

We transform the data into an actual julia matrix whose rows contain the images and a julia matrix whose i-the row contains a one-hot encoding of the label corresponding to the image in the i-th row of the data matrix. We then split it into 80% training and 20% test data.
```
# preprocess data into float matrix and one-hot label matrix
X = transpose(hcat(float.(reshape.(images,:))...))
y = [i == label ? 1 : 0 for label in labels, i in 0:9]

# split into test and train data
split = Int(ceil(length(images) * 0.8))

X_train = X[1:split, :]
X_test = X[split+1:end,:]
y_train = y[1:split,:]
y_test = y[split+1:end,:]
```

Now we can include the file we tyepechecked and run it with some parameters! Training will take some time.
```
include("flux_dp.jl")

# train with DP-SGD for 1000 epochs with sample size of 2000, learning rate of 0.2, an (0.2,0.2)-privacy
m = FluxDP.train_dp(X_train,y_train,0.2,0.2,0.2,1000,2000)
```

To run the whole thing, simply include the file `mnist.jl` in your REPL. Let's see what it can learn!
```
julia> # prints mean error and accuracy
julia > result = include("test/flux_dp/mnist.jl")
0.39895068482227536
0.8880833333333333
DMModel(Chain(Dense(784, 40, relu), Dense(40, 10), softmax))

julia> Flux.onecold(result.model(X_test[1000,:]))
7

julia> Flux.onecold(y_test[1000,:])
7
```
