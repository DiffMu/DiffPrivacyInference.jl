
module PrivacyExamples

########################################################
# from https://github.com/uvm-plaid/programming-dp

##########
# chapter 4: counting query
# DP-count the number of rows of d that f maps to something non-zero
function count(f::NoData(Function), d::Matrix, eps::NoData(Real)) :: Priv()
   dd = count(f, d)
   counter = laplacian_mechanism(1,eps,dd)
   counter
end
  

##########
# chapter 10: DP summary statistics

# sum has sensitivity 1 (in L1 metric)
function sum(xs::Vector)
   fold((x,y) -> x+y, 0., vec_to_row(xs))
end

# compute a (epsilon,0)-DP version of the average of a vector
# TODO we cannot check this properly, see issue #227
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

# compute a (epsilon,0)-DP version of the variance of a vector
# TODO same as above
function auto_variance(xs, bs::NoData(), epsilon::NoData()) :: Priv()
   epsilon_avg = epsilon / 4
   mu = auto_avg(xs,bs,epsilon_avg)

   # the query we want to make (computing variance sum this time)
   clipped_sum(m,b) = sum(map(x -> clip((x-mu)*(x-mu),b,0.), m))

   # find suitable clipping parameter using svt
   function create_query(b)
      m -> clipped_sum(m, b) - clipped_sum(m, b+1)
   end

   vqueries = map(create_query, bs)

   vepsilon_svt = epsilon / 4
   vat = above_threshold(vqueries, vepsilon_svt, xs, 0)
   vfinal_b = bs[vat]
   
   # compute noisy sum
   vepsilon_sum = epsilon / 4
   vnoisy_sum = laplacian_mechanism(vfinal_b, vepsilon_sum, clipped_sum(xs, vfinal_b))

   # compute noisy number of entries
   vepsilon_count = epsilon / 4
   vnoisy_count = laplacian_mechanism(1, vepsilon_count, length(xs))
   
   vnoisy_sum/vnoisy_count
end



########################################################
# DP summary statistics

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

# compute (eps,del)-dp mean of a 1-col matrix (basically a col vector...)
function dp_col_mean(v::Matrix{<:Real}, eps::NoData(Real), del::NoData(Real), bs::NoData(Vector{<:Real})) :: Priv()

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

end
