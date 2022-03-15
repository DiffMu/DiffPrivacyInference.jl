
# the only function that is actually typechecked: the gradient descent training algorithm.
module Fo


function sum(xs)
   s = fold((x,y)->x+y,0,xs)
   norm_convert!(s)
end



# compute a (epsilon,0)-DP version of the average of a vector
function auto_avg(xs::Vector{<:Real}, bs::NoData(Vector), epsilon::NoData(Real)) :: Priv()

   # the query we want to make   
   clipped_sum(m,b) = sum(map(x -> clip(x,b,0.), m))

   # find suitable clipping parameter using svt
   function create_query(b)
      m -> clipped_sum(m, b) - clipped_sum(m, b+1)
   end

   queries = map(create_query, bs)

   epsilon_svt = epsilon / 3
   at = above_threshold(queries, epsilon_svt, xs, 0)
   final_b = bs[at]

   # compute noisy sum
   epsilon_sum = epsilon / 3
   noisy_sum = laplacian_mechanism(final_b, epsilon_sum, clipped_sum(xs, final_b))

   # compute noisy number of entries
   epsilon_count = epsilon / 3
   noisy_count = laplacian_mechanism(1, epsilon_count, length(xs))
   
   noisy_sum/noisy_count
end


end
# we're only interested in the privacy of the `data` and `labels` inputs so all other parameters


#
#
#
## the only function that is actually typechecked: the gradient descent training algorithm.
#
## give a one-hot vector for rows that change when clipped (i.e. that have norm > 1)
#function filter_box(b::Real, xs::Matrix) :: BlackBox()
#   cxs = map(x -> clip(L2, b*x), eachrow(xs))
#   clone([(b*rm == rn ? 0. : 1.) for (rm,rn) in zip(eachrow(xs), (cxs))])
#end
#
## given a vector of clipping parameters, find the index of the one for which 90% of the samples
## remain unclipped. this is epsilon-sensitive in xs
#function select_clipping_param(xs::Matrix{<:Real}, eps::Real, bs::Vector{<:Real})::Priv()
#   # check how many samples would get clipped if the matrix was scaled by b
#   function test_scale(b::Real, xs::Matrix{<:Real})
#      (d,_) = size(xs)
#      xxs = unbox(filter_box(b,xs),Vector{<:Real},d)
#      1.0*count(x -> x==1., xxs) #(make it real...)
#   end
#   (dim, _) = size(xs)
#   target = 0.9 * dim
#   fs = map(b -> (xs -> test_scale(b,xs)), bs)
#   above_threshold(fs, eps, xs, target)
#end
#
# function col_means_nop(m::Matrix{<:Real}, eps::NoData(), del::NoData(), bs::NoData(Vector{<:Real})) :: Priv() 
#          # compute dp mean of a 1-row matrix (basically a col vector...)
#          function dp_col_mean(v::Matrix{<:Real}) :: Priv()
#            # find a scalar b s.t. 90% of rows of b*v remain unclipped
#            bp = select_clipping_param(v, eps/2, bs)
#            b = bs[bp]
#       
#            # scale and clip
#            clipped = map_rows(x -> clip(L1,disc(b)*x), v)
#            norm_convert!(clipped)
#       
#            # compute mean of clipped vector
#            (nrows,_) = size(v)
#            sm = fold((x,y)->x+y, 0., clipped) / nrows
#       
#            # add noise to mean
#            g = gaussian_mechanism(1/nrows, eps/2, del, sm)
#
#            # re-scale
#            disc(1/b) * disc(g)
#          end
#
#          reduce_cols(dp_col_mean, m)
#       end
#
#
##
##function dp_col_mean(v::Matrix{<:Real}, bs::NoData(Vector), eps::NoData(), del::NoData()) :: Priv()
##             bpb = select_clipping_param(v, eps/2, bs)
##            bb = bs[bpb]
##
##            (nrow,_) = size(v)
##  clippd = map_rows(x -> clip(L1,disc(bb)*x), v) 
##  norm_convert!(clippd)
##  smm = fold((x,y)->x+y, 0., clippd) / (2*nrow)
##            gg = gaussian_mechanism(1/(nrow), eps/2, del, smm)
##            disc(1/bb)*disc(gg)
##end



#
#
## given a vector of clipping parameters, find the index of the one for which 90% of the samples
## remain unclipped. this is epsilon-sensitive in xs
#function select_clipping_param(xs::Matrix{<:Real}, eps::Real, bs::Vector{<:Real})::Priv()
#   # check how many samples would get clipped if the matrix was scaled by b
#   function test_scale(b::Real, xs::Matrix{<:Real})
#      (d,_) = size(xs)
#      xxs = unbox(filter_box(b,xs),Vector{<:Real},d)
#      1.0*count(x -> x==1., xxs) #(make it real...)
#   end
#   (dim, _) = size(xs)
#   target = 0.9 * dim
#   fs = map(b -> (xs -> test_scale(b,xs)), bs)
#   above_threshold(fs, eps, xs, target)
#end
#
#       
#function col_means(m::Matrix{<:Real}, eps::NoData(), del::NoData(), bs::Vector{<:Real}) :: Priv() 
#   # compute dp mean of a 1-row matrix (basically a col vector...)
#   function dp_col_mean(v::Matrix{<:Real}) :: Priv()
#     # find a scalar b s.t. 90% of rows of b*v remain unclipped
#     bp = select_clipping_param(v, eps/2, bs)
#     b = bs[bp]
#
#     # scale and clip
#     clipped = map_rows(x -> clip(L1,disc(b)*x), v)
#     norm_convert!(clipped)
#
#     # compute mean of clipped vector
#     (nrows,_) = size(v)
#     sm = fold((x,y)->x+y, 0., clipped) / nrows
#
#     # add noise to mean
#     g = gaussian_mechanism(1/nrows, eps/2, del, sm)
#     # re-scale
#     disc(1/b) * disc(g)
#   end
#   reduce_cols(dp_col_mean, m)
#end
#
## subtract the mean (given as a 1-row matrix) of each column of mat from each entry in said column.
#function center(mat::Matrix, means::Matrix)
#   center_col(col::Vector, mean::Vector) = map(x -> x - mean[1], col)
#   map_cols_binary(center_col, mat, means)
#end
#
#function col_scale_params(centered, eps::NoData(), del::NoData(), bs::NoData(Vector), means::Matrix) :: Priv()
#   function select(col) :: Priv()
#      select_clipping_param(col, eps, bs)
#   end
#   reduce_cols(select, centered)
#end
#
#function normalize(scales::Matrix, centered::Matrix)
#   scale_col(col::Vector, scale::Vector) = map(x -> x / scale[1], col)
#   map_cols_binary(scale_col, centered, scales)
#end
#   
#function main(m, eps::NoData(), del::NoData(), bs::NoData(Vector), eta::NoData(), k::NoData(), b::NoData()) :: Priv()
#   means = vec_to_row(col_means(m, eps, del, bs))
#   centered = center(m, means)
#   scales = col_scale_params(centered, eps, del, bs, means)
#   normalize(scales, centered)
#   train_dp(m, eps, del, eta, k, b)
#end
#
#
