module AdaptiveClipping



# one-hot vector saying whether row i of b*xs gets clipped.
function filter_box(b::Real, xs::Matrix) :: BlackBox()
   cxs = map(x -> clip(L2, b*x), eachrow(xs))
   [(rm == rn ? 1. : 0.) for (rm,rn) in zip(eachrow(xs), (cxs))]
end

# return the index of the first element b in bs s.t. 90% of the rows of b*xs do not get clipped.
function select_clipping_param(xs::Matrix{<:Real}, eps::NoData(Real), bs::Vector{<:Real})::Priv()
   function test_scale(b::Real, xs::Matrix{<:Real})
      (d,_) = size(xs)
      xxs = unbox(filter_box(b,xs),Vector{<:Real},d)
      1.0*count(x -> x==1., xxs)
   end
   (dim, _) = size(xs)
   target = 0.9 * dim
   fs = map(b -> (xs -> test_scale(b,xs)), bs)
   above_threshold(fs, eps, xs, target)
end

    
function col_means(m::Matrix{<:Real}, eps::NoData(), del::NoData(), bs::NoData(Vector{<:Real})) :: Priv() 
   # compute (eps,del)-dp mean of a 1-col matrix (basically a col vector...)
   function dp_col_mean(v::Matrix{<:Real}) :: Priv()
        # find a scalar b s.t. 90% of rows (i.e. entries of the col vector) of b*v remain unclipped
        bp = select_clipping_param(v, eps/2, bs)
        b = bs[bp]
   
        # scale each row (i.e. each entry of the col vector...) and clip
        clipped = map_rows(x -> clip(L1,disc(b)*x), v)
        norm_convert!(clipped)
   
        # compute mean of clipped col vector
        (nrows,_) = size(v)
        sm = fold((x,y)->x+y, 0., clipped) / nrows
   
        # add noise to mean
        g = gaussian_mechanism(2/nrows, eps/2, del, sm)
        # re-scale
        disc(1/b) * disc(g)
   end
   reduce_cols(dp_col_mean, m)
end

# the only function that is actually typechecked: the gradient descent training algorithm.
# we're only interested in the privacy of the `data` and `labels` inputs so all other parameters
# get a `NoData()` annotation. it's a privacy function, so we annotate it with `Priv()`.
function train_dp_bounded_grad(data, eps::NoData(), del::NoData(), eta::NoData(), k::NoData(Integer), grad::NoData(Function), model::NoData(DMModel)) :: Priv()

   # the computation we do on each data row seperately. 
   function body!(d, l, model::NoData()) :: Priv()
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

function main(m, eps::NoData(), del::NoData(), bs::NoData(Vector), eta::NoData(), k::NoData(), b::NoData(), grad::Function, model::NoData(DMModel)) :: Priv()
   means = col_means(m, eps, del, bs)
   centered = map_cols_binary((col::Vector, mean::Vector) -> map(x -> x - mean[1], col), m, vec_to_row(means))
   function select(col) :: Priv()
      select_clipping_param(col, eps, bs)
   end
   scales = reduce_cols(select, centered)
   n = map_cols_binary((col::Vector, scale::Vector) -> map(x -> x / scale[1], col), centered, vec_to_row(scales))
   train_dp_bounded_grad(centered, eps, del, eta, k, b, grad, model)
   return
end


end
