using LinearAlgebra
using Random

### usage:
# using MLDatasets
# data = MNIST.traindata()
# network = [input_layer(28^2), softplus_layer(28^2, 500), softplus_layer(500,500), softplus_layer(500,500), softmax_layer(500,10)]
# train(network, [vec(data[1][:,:,k]) for k in 1:50000], vec(data[2][1:50000]))
# test(network, [vec(data[1][:,:,k]) for k in 50001:60000], vec(data[2][50001:60000]))


### network stuff

mutable struct Layer
 N::Int
 Nout::Int
 weights::Matrix
 bias::Vector
 activation::Function
 derivative::Function
end

rng = MersenneTwister(1234)

sigmoid(x) = 1.0./(1.0.+exp.(-x))
softplus(x) = log.(1.0.+exp.(x))
function softmax(x)
    shiftx = x .- maximum(x) # to avoid overflows
    exps = exp.(shiftx)
    return exps ./ sum(exps)
end
relu(x) = map(y->max(0,y),x)

dsigmoid(y) = sigmoid(y).*(1.0.-sigmoid(y))
dsoftplus(y) = 1.0.-exp.(-y)
#dsoftplus(y) = 1.0 ./ (1.0.+exp.(-y))
dsoftmax(y) = y.*(1.0.-y)
drelu(x) = map(y -> y<0 ? 1 : 0, x)


sigmoid_layer(N1, N2) = Layer(N1, N2, 0.1*randn(rng,N1, N2), 0.1*randn(rng,N2), sigmoid, dsigmoid)
softplus_layer(N1, N2) = Layer(N1, N2, 0.1*randn(rng,N1, N2), 0.1*randn(rng,N2), softplus, dsoftplus)
softmax_layer(N1, N2) = Layer(N1, N2, 0.1*randn(rng,N1, N2), 0.1*randn(rng,N2), softmax, dsoftmax)
relu_layer(N1, N2) = Layer(N1, N2, 0.1*randn(rng,N1, N2), 0.1*randn(rng,N2), relu, drelu)
input_layer(N1) = Layer(N1, N1, Matrix{Float64}(I, N1, N1), 0.1*randn(rng,N1), sigmoid, dsigmoid) # just bias and sigmoid activation



### computing gradient with backpropagation

function feedforward(network, x)
  activated_layer_output = [x]
  layer_output = []
  for l in network
      layer_output = [layer_output..., l.weights' * activated_layer_output[end] + l.bias]
      activated_layer_output = [activated_layer_output..., l.activation(layer_output[end])]
  end
  return (activated_layer_output, layer_output)
end

function gradient(network, x, y)
  # feedforward
  (activated_layer_output, layer_output) = feedforward(network, x)

  # backward pass
  # gradient updates for bias and weights
  nabla_b = [zeros(size(l.bias)) for l in network]
  nabla_w = [zeros(size(l.weights)) for l in network]

  delta = (y - activated_layer_output[end]) #.* network[end].derivative(layer_output[end]) # derivative of quadratic loss
  nabla_b[end] = delta
  nabla_w[end] = activated_layer_output[end-1] * delta'

  for l in 2:length(network)
      sp = network[end-l+1].derivative(activated_layer_output[end-l+1])
      delta = (network[end-l+2].weights * delta) .* sp

      nabla_b[end-l+1] = delta
      nabla_w[end-l+1] = (delta * activated_layer_output[end-l]')'
  end

  return (nabla_b, nabla_w, activated_layer_output[end])
end


### train a network

function train(network, features, labels; N_minibatch = 100, momentum = 0.75, alpha = 0.001, N_updates = round(length(labels)/N_minibatch)*500)

	# dataset size
	N_datapoints = length(labels)

   # accuracy for batch status output
	N_correct = 0.0
	N_tries = 0.0

   # gradients for bias and weights of all layers
	bias_gr = [zeros(size(layer.bias)) for layer in network]
	weight_gr = [zeros(size(layer.weights)) for layer in network]

	for i in 1:N_updates
		for j = 1:N_minibatch
			# pick random data point
			k = rand(rng,1:N_datapoints)
			input = 6 .* features[k] .- 3

         # one-hot label
			label = zeros(network[end].Nout)
	    	label[labels[k]+1] = 1.0

			# compute gradient for this feature and collect in this batches gradient
         (b_bias_gr, b_weight_gr, guess) = gradient(network, input, label)

         # update batch gradient
         for i in 1:length(network)
		      bias_gr[i] .+= b_bias_gr[i]
		      weight_gr[i] .+= b_weight_gr[i]
	   	end

			# update batch accuracy
			if findmax([guess...])[2] == labels[k]+1
				N_correct += 1.0
			end
			N_tries += 1.0

		end

		# update network parameters with learning rate alpha
		network[1].bias .+= alpha.*bias_gr[1] # don't update input layer weights
		for i in 2:length(network)
		   network[i].bias .+= alpha*bias_gr[i]
		   network[i].weights .+= alpha*weight_gr[i]
		end

		# decrease learning rate
		alpha *= (N_updates-i)/(N_updates-i+1)

		if i%10 == 0
			println("REPORT")
			println("  Batch = $i")
			println("  alpha = $alpha")
			println("  Correct = $(100.0*N_correct/N_tries)%")
			println("  gredient = $(bias_gr[end])")
			println("  bias = $(network[end].bias)")
			println("")

			# reset accuracy
			N_tries = 0.0
			N_correct = 0.0
		end

		# keep some of this iterations gradient
		for i in 1:length(network)
		   bias_gr[i] .*= momentum
		   weight_gr[i] .*= momentum
		end
	end

   network
end

function test(network, features, labels)
   # accuracy for batch status output
	N_correct = 0.0
	N_tries = 0.0

	for k in 1:length(features)
	   (layer_output, _) = feedforward(network, 6 .* features[k] .- 3)
   	if findmax([layer_output[end]...])[2] == labels[k]+1
   		N_correct += 1.0
   	end
   	N_tries += 1.0
   end
	# Print progress report.
	#
	println("SCORE")
	println("  Correct = $(100.0*N_correct/N_tries)%")
	println("")
end


