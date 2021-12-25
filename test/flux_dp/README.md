# Learning MNIST, verified differentially private
This directory contains a toy example that trains a simple neural network modelled using the [Flux.jl machine learning library](https://github.com/FluxML/Flux.jl) to recognize handwritten digits. Our typechecker can verify that the function doing the gradient descent for training satisfies given differential privacy bounds.

This is a proof of concept. It is not very efficient, partly because we do not yet support mutation of data structures and every model update requires making a copy of the whole model. Bear with us, we're working on it! The example is instructive still, as the inefficiencies happen within builtin functions not defined in this code, so what you see here will probably not change much in the future. Let's walk through it, then!

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

- We're only interested in the privacy of the `data` and `labels` inputs, so all other parameters get a `NoData()` annotation.
- It's supposed to be a differentially private function, so we annotate it with `Priv()`.
- It initializes the network and iterates over all data/label pairs, computing the gradient and making differentially private updates to the model.
- There is a few peculiarities concerning that last part:
   - Model updates and gradient operations (like scaling) can only be done using our very limited set of builtin functions for that purpose. See [here](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/src/builtins.jl) for the definitions of these.
   - Differential privacy is a property expressed using a notion of distance between inputs of a function. This means all vectors, matrices, gradients and models in our code carry a norm describing which notion of distance is used for which object (See [this pdf](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/docs/matrixnorms/matrixnorms.pdf) and section 4.2 of the [duet paper](https://arxiv.org/abs/1909.02481) for more on the topic). Here, we use the `norm_convert` builtin function to make the clipped gradient measured using the discrete norm into a gradient measured with the clipping norm (`L2`, here) instead. This is necessary as the gradient obtained from a black box computation lives in discrete-norm land, while the Gaussian machanism expects the input to live in L2-norm land (see the `mgauss` rule on page 43 of the [duet paper](https://arxiv.org/abs/1909.02481)).
   - Every assignment after the application of the Gaussian mechanism is annotated with `Robust()` to inform the typechecker that it should make use of the ["Robustness to post-processing"](https://en.wikipedia.org/wiki/Differential_privacy#Robustness_to_post-processing) property of differentially private variables.
```
function train_dp(data, labels, eps::NoData(), del::NoData(), eta::NoData()) :: Priv()
   # initialize a Flux model.
   model = init_model()
   (dim, _) = size(data)
   for i in 1:dim
      # compute the gradient at the i-th data point
      d = data[i,:]
      l = labels[i,:]
      gs = unbounded_gradient(model, d, l)

      # clip the gradient
      gs = norm_convert(clip(L2,gs))

      # apply the gaussian mechanism to the gradient.
      # we scale the gradient prior to this to bound it's sensitivity to 2/dim, so the noise
      # required to make it DP stays reasonable.
      # the returned variable is annotated to be `Robust()` to signify it is now DP and
      # hence it's privacy bounds are robust to post-processing.
      gs :: Robust() = gaussian_mechanism(2/dim, eps, del, scale_gradient(1/dim,gs))

      # update the model by subtracting the noised gradient scaled by the learning rate eta.
      # we also re-scale the gradient by `dim` to make up for the scaling earlier.
      model :: Robust() = subtract_gradient(model, scale_gradient(eta * dim, gs))
   end
   model
end
```

## Learning MNIST, implemented in [`mnist.jl`](https://github.com/DiffMu/DiffPrivacyInference.jl/blob/main/test/flux_dp/mnist.jl)
To use the above algorithm, we need to call the `train_dp` function. The inferred differential privacy is a property of the algorithm, but we cannot typecheck the code that actually calls the function with some actual data that's loaded from somewhere. This has to happen in a seperate file where you can use the checked function, but bear the responsibility of using it correcly.

First, we load the MNIST dataset, containing loads of images of handwritten digits and the corresponding labels.
```
using Flux

# get MNIST dataset
images = Flux.Data.MNIST.images();
labels = Flux.Data.MNIST.labels();
```

We transform the data into an actual julia matrix whose rows contain the images and a julia matrix whose i-the row contains a one-hot encoding of the label corresponding to the image in the i-th row of the data matrix.
```
X = transpose(hcat(float.(reshape.(images,:))...))
y = [i == label ? 1 : 0 for label in labels, i in 0:9]
```

Now we can include the file we tyepechecked and run it with some parameters! Training will take some time.
```
include("flux_dp.jl")
train_dp(X,y,0.9,0.2,1,1)
```
