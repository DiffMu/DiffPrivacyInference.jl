
# [Learning MNIST using `Flux.jl`, verified differentially private](@id fluxdp)
We provide code for [a toy example](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/example/flux_dp/) that trains a simple neural network modelled using the [Flux.jl machine learning library](https://github.com/FluxML/Flux.jl) to recognize handwritten digits. Our typechecker can verify that the function doing the gradient descent for training satisfies given differential privacy bounds. We walk through most of the code here.

## Noisy gradient descent, implemented in the [`flux_dp.jl`](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/example/flux_dp/flux_dp.jl) file
This file contains an implementation of noisy gradient descent, guided by the example in section 5.6 of the [duet paper](https://arxiv.org/abs/1909.02481).

The file defines a module to ensure a seperate scope. Further, we `use` the `DiffPrivacyInference` module to have access to our [builtins](@ref) within this module.
```julia
module FluxDP
using DiffPrivacyInference
```

We import the Flux library. Note that including modules means one has to qualify everything one uses from the model, like `Flux.gradient` to call the gradient function. This is necessary, as it enables us to discern between imported and homemade things in the code.
```julia
import Flux
```

Next, we define a function that initializes a small `Flux` neural network model. It uses stuff imported from the `Flux` module. As we cannot expect that code to be checkable (see the [supported syntax](@ref syntax) on what checkable code needs to look like), we declare this function a so-called [*black box*](@ref blackbox) and signify this with the `BlackBox()` annotation. This means the typechecker will ignore the code inside the function body and assume it hase infinite sensitivity in all it's arguments (of which this specimen has none).
Note that the `Flux` model is not returned by the function as-is, but wrapped in our [`DMModel`](@ref) type. It's really just a plain wrapper, but as you cannot access it's content in checkable code, this allows us to control what you do with your model in the part of the program that is relevant for analysis.
```julia
function init_model() :: BlackBox()
 DMModel(Flux.Chain(
         Flux.Dense(28*28,40, Flux.relu),
         Flux.Dense(40, 10),
         Flux.softmax))
end
```

The loss function for our training not only uses a function from `Flux`, but also accesses the `Flux` model wrapped in the `model` field of the input `DMModel`. Hence it's a black box too.
```
loss(X, y, m) :: BlackBox() = Flux.crossentropy(m.model(X), y)
```

The function computing the gradient from a model and data and label vectors is a black box, too. Note that just like models, gradients have to be wrapped in our [`DMGrads`](@ref) type.
```
function unbounded_gradient(m::DMModel, data::Vector, label) :: BlackBox()
   gs = Flux.gradient(Flux.params(m.model)) do
           loss(data,label,m.model)
        end
   return DMGrads(gs)
end
```

Now comes the only function whose body is actually typechecked: the gradient descent training algorithm. There is a lot going on here, so we'll walk through it step by step in a bit.
```julia
function train_dp(data::Matrix{<:Data}, labels::Matrix{<:Data}, eps::Static(), del::Static(), eta::Static(), k::Static(Integer), b::Static(Integer)) :: Priv()
   # initialize a Flux model. as this is a black box, we have to use `unbox` and provide
   # return type and number of parameters of the returned model.
   n_params = 31810
   model = unbox(init_model(), DMModel, n_params)
   
   # loop for k epochs.
   for i in 1:k
      # sample a submatrix of `b` rows simultaneously from data and labels.
      D, L = sample(b, data, labels)

      # initialize all-zero gradient container
      G = zero_gradient(model)

      # iterate through all samples
      for j in 1:b
         # compute the gradient at the j-th data point
         # `d` and `l` are vectors of type `Data`, `gs` is gradient whose metric will
         # be inferred to be `(LInf, Data)` so the sensitivity in `d` and `l` is finite
         d = D[j,:]
         l = L[j,:]
         gs = unbox(unbounded_gradient(model, d, l), DMGrads, n_params) 

         # clip the gradient and convert to `Real` so we can use it as input to the Gaussian mechanism later
         # clipping is necessary because the conversion to `Real` would have infinite sensitivity otherwise
         clip!(L2,gs)
         undisc_container!(gs)

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

So here's what's going on:
- We're only interested in the privacy of the `data` and `labels` inputs, so all other parameters get a [`Static()`](@ref) annotation. We want the interesting inputs' privacy expressed w.r.t the [discrete metric], so we annotate them with ['Data'](@ref) as matrix element type. It's supposed to be a differentially private function, so we annotate it with [`Priv()`](@ref).
  ```julia
  function train_dp(data::Matrix{<:Data}, labels::Matrix{<:Data}, eps::Static(), del::Static(), eta::Static(), k::Static(Integer), b::Static(Integer)) :: Priv()
  ```

- It initializes the network using the previously defined [black box function](@ref blackbox) and the builtin [`unbox`](@ref) to tell the typechecker the model type and number of parameters.
  ```julia
     n_params = 31810
     model = unbox(init_model(), DMModel, n_params)
  ```

- Inside the epoch loop, we sample a batch of size `b` using the builtin [`sample`](@ref) function.
  ```julia
      D, L = sample(b, data, labels)
  ```

- We initialize an empty gradient object to aggregate the batch gradients in.
  ```julia
      G = zero_gradient(model)
  ```

- For each batch member, we compute the gradient using the `unbounded_gradient` black box function we defined earlier.
  ```julia
         d = D[j,:]
         l = L[j,:]
         gs = unbox(unbounded_gradient(model, d, l), DMGrads, n_params) 
  ```

- We want to noise the gradient using the Gaussian Mechanism, which expects a container type that has the standard euclidean `(L2,ℝ)`-metric assigned. However, the metric used to measure `gs` is the discrete `(LInf, 𝔻)`-metric (see the last section of the [black box documentation](@ref blackbox) to learn why). Hence, we have to convert `gs` from discrete to real metric using the [`undisc_container`](@ref) builtin. This however only works on containers with entries whose `(L2,ℝ)`-norm is bounded by 1, so we clip the gradient prior to converting.
  ```julia
         clip!(L2,gs)
         undisc_container!(gs)
  ```

- The batch gradients are aggregated in the `G` container using [`sum_gradients`](@ref).
  ```julia
         G = sum_gradients(gs,G)
  ```
- After the batch loop aggregated all the batches gradients, we scale the aggregate `G` to get the mean gradient by using the mutating builtin [`scale_gradient!`](@ref). Then the result is noised using the mutating [`gaussian_mechanism!`](@ref). The parameter `2` is passed to it, because the `G` variable is `2`-sensitive in the `data` and `labels` function inputs. If you don't believe that, feel free to write up a sub-function and infer their sensitivity yourself :)
  ```julia
      scale_gradient!(1/b, G)
      gaussian_mechanism!(2, eps, del, G)
  ```

- Now all that remains to be done is updating the model using the noised mean gradient. We scale it by the learning rate using [`scale_gradient!`](@ref), then subtract form the model parameters using [`subtract_gradient!`](@ref) which mutates the `model`.
  ```julia
      scale_gradient!(eta, G)
      subtract_gradient!(model, G)
  ```


## Typechecking this
To typecheck the file, make the following call in the julia REPL:
```
julia> typecheck_from_file("test/flux_dp/flux_dp.jl")

---------------------------------------------------------------------------
Type:
{
|   - Matrix<n: LInf, c: C₆>[n₁ × n₄]{Data}
|       @ (4.0⋅(1 / n₁)⋅b⋅eps⋅√(2.0⋅(0 - ln(s₂₈))⋅⌈k⌉), (1 / n₁)⋅b⋅del⋅⌈k⌉ + s₂₈)
|   
|   - Matrix<n: LInf, c: C₆>[n₁ × n₅]{Data}
|       @ (4.0⋅(1 / n₁)⋅b⋅eps⋅√(2.0⋅(0 - ln(s₂₈))⋅⌈k⌉), (1 / n₁)⋅b⋅del⋅⌈k⌉ + s₂₈)
|   
|   - τ₇₃[eps ©]@(0, 0)
|   
|   - τ₇₅[del ©]@(0, 0)
|   
|   - τ₈₄[eta ©]@(0, 0)
|   
|   - Integer[k ©]@(0, 0)
|   
|   - Integer[b ©]@(0, 0)
|   --------------------------
|    ->* DMModel[31810.0]
}
where
 - Variable s₂₈ can be chosen with type Real to be within (0,1]. Appeared in the privacy loop in test/flux_dp/flux_dp.jl: line 77

---------------------------------------------------------------------------
Constraints:
constr₁₄ : eps < 1,
constr₁₅ : del < 1,
constr₁₅₄ : Type τ₁₆₆ is the supremum of types τ₈₄ and Real,
constr₁₆ : 0 < eps,
constr₁₇ : 0 < del,
constr₄₃ : 2.0⋅(1 / b)⋅⌈(b - 1) + 1⌉ ≤ 2.0,
constr₅₆ : s₂₈ ≤ 1,
constr₅₇ : 0 < s₂₈,
constr₈₃ : 1 ≤ b
```

It says that given the constraints in the list hold for the variables occuring in the type, the function is `(4.0⋅(1 / n₁)⋅b⋅eps⋅√(2.0⋅(0 - ln(s₂₈))⋅⌈k⌉), (1 / n₁)⋅b⋅del⋅⌈k⌉ + s₂₈)`-private in its first and second arguments (the data and labels matrices, whose dimensions are denoted `[n₁ × n₄]` and `[n₁ × n₅]`), and zero-private in the following (the `eps` and `del` parameters, the `eta` parameter, and the number of epochs `k` and batch size `b`).

## Learning MNIST, implemented in [`mnist.jl`](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/example/flux_dp/mnist.jl)
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

## Run the trianing yourself!
To run the whole thing, simply include the file `mnist.jl` in your REPL. Let's see what it can learn! Training can take a while.
```
julia> # prints mean error and accuracy
julia > result = include("test/flux_dp/mnist.jl")
average loss: 0.407527023015877
accuracy: 0.8861666666666667
DMModel(Chain(Dense(784, 40, relu), Dense(40, 10), softmax))

julia> Flux.onecold(result.model(X_test[1000,:])) # model prediction for test example 1000
7

julia> Flux.onecold(y_test[1000,:]) # correct label for test example 1000
7
```

### A note on performance
Training a neural network using this differentially private implementation of stochastic gradient descent is much slower than training using the non-private version. The non-private version uses a trick, exploiting that the average of a batch's gradients is the gradient of the batch average, hence only needing to compute a single gradient per batch. For the differentially private version, however, we need to clip each batch member's gradient individually, so we need to compute each one individually.
