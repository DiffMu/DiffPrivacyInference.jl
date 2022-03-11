module AdaptiveClipping

# this code is checkable with our typechecker. the inference result will be the type of the last function
# in the file, containing the inferred privacy bound as well as constraints on the input variables.

# give a one-hot vector for rows that change when clipped (i.e. that have norm > 1)
function filter_box(b::Real, xs::Matrix) :: BlackBox()
   cxs = map(x -> clip(L2, b*x), eachrow(xs))
   clone([(rm == rn ? 0. : 1.) for (rm,rn) in zip(eachrow(xs), (cxs))])
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
   (dm, _) = size(xs)
   target = 0.9 * dm
   fs = map(b -> (xs -> test_scale(b,xs)), bs)
   above_threshold(fs, eps, xs, target)
end
       
function col_means(m::Matrix{<:Real}, eps::NoData(), del::NoData(), bs::NoData(Vector{<:Real})) :: Priv() 
   # compute dp mean of a 1-row matrix (basically a col vector...)
   function dp_col_mean(v::Matrix{<:Real}) :: Priv()
     # find a scalar b s.t. 90% of rows of b*v remain unclipped
     bp = select_clipping_param(v, eps/2, bs)
     b = bs[bp]

     # scale and clip
     clipped = map_rows(x -> clip(L1,disc(b)*x), v)
     norm_convert!(clipped)

     # compute mean of clipped vector
     (nrows,_) = size(v)
     sm = fold((x,y)->x+y, 0., clipped) / nrows

     # add noise to mean
     g = gaussian_mechanism(1/nrows, eps/2, del, sm)
     # re-scale
     disc(1/b) * disc(g)
   end
   reduce_cols(dp_col_mean, m)
end

# subtract the mean (given as a 1-row matrix) of each column of mat from each entry in said column.
function center(mat::Matrix, means::Matrix)
   center_col(col::Vector, mean::Vector) = map(x -> x - mean[1], col)
   map_cols_binary(center_col, mat, means)
end

# get the vector of clipping parameters the SVT determines for each column of `centered`.
function col_scale_params(centered, eps::NoData(), del::NoData(), bs::NoData(Vector)) :: Priv()
   function select(col) :: Priv()
      select_clipping_param(col, eps, bs)
   end
   reduce_cols(select, centered)
end
# the only function that is actually typechecked: the gradient descent training algorithm.
# we're only interested in the privacy of the `data` and `labels` inputs so all other parameters
# get a `NoData()` annotation. it's a privacy function, so we annotate it with `Priv()`.
function train_dp_bounded_grad(data, eps::NoData(), del::NoData(), eta::NoData(), k::NoData(Integer), b::NoData(Integer), grad::NoData(Function), model::NoData(DMModel)) :: Priv()
   (dim, _) = size(data)
   for i in 1:k*(dim/b)
      #D, _ = sample(b, data, data)
      #G = zero_gradient(model)

      #for j in 1:b
         # compute the gradient at the i-th data point
         #da = D[j,:]
         da = data[i,:]
         G = grad(model, da)
         #gs = grad(model, da)

      #   G = sum_gradients(gs,G)
      #end

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
   return
end


# scale each column of `centered` by the corresponding scalar in `scales`
function normalize(scales::Matrix, centered::Matrix)
   scale_col(col::Vector, scale::Vector) = map(x -> x / scale[1], col)
   map_cols_binary(scale_col, centered, scales)
end
 
function main(m, eps::NoData(), del::NoData(), bs::NoData(Vector), eta::NoData(), k::NoData(), b::NoData(), grad::Function, model::NoData(DMModel)) :: Priv()
   means = col_means(m, eps, del, bs)
   centered = center(m, vec_to_row(means))
   scales = col_scale_params(centered, eps, del, bs)
#   n = normalize(vec_to_row(scales), centered)
#   (nrws, _) = size(m)

#   gaussian_mechanism(nrws, eps, del, n)# centered)
   #train_dp_bounded_grad(n, eps, del, eta, k, b, grad, model)
   #return
end


end
