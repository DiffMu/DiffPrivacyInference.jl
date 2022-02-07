
########################################################3
# from https://github.com/uvm-plaid/programming-dp
# chapter 4
# DP-count the number of rows of d that f maps to something non-zero
function count(f:: Function, d::Matrix, eps::Real) :: Priv()
   (dim, _) = size(d)
   counter = 0
   for i in 1:dim
      dd = d[i,:]
      if f(dd)
         counter = counter + 1
      end
   end
   counter = laplacian_mechanism(1,eps,counter)
   counter
end


########################################################3
# from https://github.com/uvm-plaid/programming-dp
# chapter 10: DP average computation

function sum(xs)
   s = xs[1]
   for i in 2:length(xs)
      s = s + xs[i]
   end
   s
end

# compute a DP version of the average of a vector
function auto_avg(xs::AbstractVector, bs::AbstractVector, epsilon::Real)

   # the query we want to make   
   clipped_sum(m,b) = sum(map(x -> clip(x,b,0), m))

   # find suitable clipping parameter using svt
   function create_query(b)
      m -> clipped_sum(m, b) - clipped_sum(m, b+1)
   end

   queries = map(create_query, bs)

   epsilon_svt = epsilon / 3
   final_b = bs[above_threshold(queries, epsilon_svt, xs, 0)]

   # compute noisy sum
   epsilon_sum = epsilon / 3
   noisy_sum = laplacian_mechanism(final_b, epsilon_sum, clipped_sum(xs, final_b))

   # compute noisy number of entries
   epsilon_count = epsilon / 3
   noisy_count = laplacian_mechanism(1, epsilon_count, length(xs))
   
   noisy_sum/noisy_count
end

function auto_variance(xs, bs, epsilon)
   mu = auto_avg(xs,bs,epsilon)
   auto_avg(map(x -> (x-mu)*(x-mu), xs), bs, epsilon)
end



########################################################3
# from the duet paper: for adaptive clipping.

function test_scale(b, xs)
   (dim, _) = size(xs)
   count = 0
   for i in 1:dim
         x = b * xs[i,:]
         cx = clip(L2, x)
         if cx == x
             count = count + 1
         end
   end
   count * 0.5
end

function set_clipping_param(xs, eps, bs)
   (dim, _) = size(xs)
   target = 0.9 * dim
   fs = map(b -> (xs -> test_scale(b,xs)), bs)
   above_threshold(fs, eps, xs, target)
end
