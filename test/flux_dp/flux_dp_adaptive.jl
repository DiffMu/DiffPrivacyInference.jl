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
function unbounded_gradient(model::DMModel, dd) :: BlackBox()
   l = dd[end]
   d = dd[1:end-1]
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


# the only function that is actually typechecked: the gradient descent training algorithm.

# give a one-hot vector for rows that change when clipped (i.e. that have norm > 1)
function filter_box(b::Real, xs::Matrix) :: BlackBox()
   cxs = map(x -> clip(L2, b*x), eachrow(xs))
   clone([(rm == rn ? 1. : 0.) for (rm,rn) in zip(eachrow(xs), (cxs))])
end

# given a vector of clipping parameters, find the index of the one for which 90% of the samples
# remain unclipped. this is epsilon-sensitive in xs
function select_clipping_param(xs::Matrix{<:Real}, eps::Real, bs::Vector{<:Real})::Priv()
   # check how many samples would get clipped if the matrix was scaled by b
   function test_scale(b::Real, xs::Matrix{<:Real})
      (d,_) = size(xs)
      xxs = unbox(filter_box(b,xs),Vector{<:Real},d)
      1.0*count(x -> x==1., xxs) #(make it real...)
   end
   (dim, _) = size(xs)
   target = 0.9 * dim
   fs = map(b -> (xs -> test_scale(b,xs)), bs)
   above_threshold(fs, eps, xs, target)
end

function col_means(m, eps::NoData(), del::NoData(), bs::NoData()) :: Priv() 
   # compute dp mean of a 1-row matrix (basically a col vector...)
   function dp_col_mean(v) :: Priv()
     (nrows,_) = size(v)
     bp = select_clipping_param(v, eps/2, bs)
     b = bs[bp]
     clipped = map_rows(x -> clip(L1,b*x), v)
     norm_convert!(clipped)
     sm = fold((x,y)->x+y, 0., clipped) / nrows
     g = gaussian_mechanism(1/nrows, eps/2, del, sm)
     disc(g)
   end

   reduce_cols(dp_col_mean, m)
end

function center(mat::Matrix, means::Matrix)
   center_col(col::Vector, mean::Vector) = map(x -> x - mean[0], col)
   map_cols_binary(center_col, mat, means)
end

function col_scale_params(centered, eps::NoData(), del::NoData(), bs::NoData(Vector), means::Matrix) :: Priv()
   function select(col) :: Priv()
      select_clipping_param(col, eps, bs)
   end
   reduce_cols(select, centered)
end

function normalize(scales::Matrix, centered::Matrix)
   scale_col(col::Vector, scale::Vector) = map(x -> x / scale[0], col)
   map_cols_binary(scale_col, centered, scales)
end
   
function main(m, eps::NoData(), del::NoData(), bs::NoData(Vector), eta::NoData(), k::NoData(), b::NoData()) :: Priv()
   means = col_means(m, eps, del, bs)
   centered = center(m, vec_to_row(means))
   scales = col_scale_params(centered, eps, del, bs, vec_to_row(means))
   normalize(scales, centered)
   train_dp(m, eps, del, eta, k, b)
end


# we're only interested in the privacy of the `data` and `labels` inputs so all other parameters
# get a `NoData()` annotation. it's a privacy function, so we annotate it with `Priv()`.
function train_dp(data, eps::NoData(), del::NoData(), eta::NoData(), k::NoData(Integer), b::NoData(Integer)) :: Priv()
   # initialize a Flux model.
   n_params = 31810
   model = unbox(init_model(), DMModel, n_params)
   (dim, _) = size(data)
   for i in 1:k*(dim/b)
      D, _ = sample(b, data, data)
      G = zero_gradient(model)


      for j in 1:b
         # compute the gradient at the i-th data point
         d = D[j,:]
         l = L[j,:]
         gs = unbox(unbounded_gradient(model, d, l), DMGrads, n_params)

         # clip the gradient
         clip!(L2,gs)
         norm_convert!(gs)

         G = sum_gradients(gs,G)
      end

      # apply the gaussian mechanism to the gradient.
      # we scale the gradient prior to this to bound it's sensitivity to 2/dim, so the noise
      # required to make it DP stays reasonable.
      scale_gradient!(1/b, G)
      gaussian_mechanism!(2/b, eps, del, G)

      # update the model by subtracting the noised gradient scaled by the learning rate eta.
      # we also re-scale the gradient by `dim` to make up for the scaling earlier.
      scale_gradient!(eta, G)
      subtract_gradient!(model, G)
   end
   model
end

