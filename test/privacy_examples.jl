
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
# chapter 5: histogram
# TODO need parallel composition.

##########
# chapter 7
# TODO implement using loop
function avg_attack(query, epsilon, k) :: Priv()
   v = zeros(k)
   vv = map(x -> laplacian_mechanism(1,epsilon,query), v)
   sum(vv)/k
end
   

##########
# chapter 10: DP average computation

function sum(xs)
   s = 0.
   for i in 1:length(xs)
      s = s + xs[i]
   end
   s
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



########################################################3
# from the duet paper: for adaptive clipping.

function filter_box(b::Real, xs::Matrix) :: BlackBox()
   cxs = map(x -> clip(L2, b*x), eachrow(xs))
   println(cxs)
   clone([(rm == rn ? 1. : 0.) for (rm,rn) in zip(eachrow(xs), (cxs))])
end

function test_scale(b::Real, xs::Matrix{<:Real})
   (d,_) = size(xs)
   xxs = unbox(filter_box(b,xs),Vector{<:Real},d)
   count(x -> x==1., xxs)
end

function set_clipping_param(test_scale,xs::Matrix{<:Real}, eps::Real, bs::Vector{<:Real})::Priv()
   (dim, _) = size(xs)
   target = 0.9 * dim
   fs = map(b -> (xs -> test_scale(b,xs)), bs)
   above_threshold(fs, eps, xs, target)
end

