using Flux

# get MNIST dataset
images = Flux.Data.MNIST.images();
labels = Flux.Data.MNIST.labels();

# preprocess data into float matrix and one-hot label matrix
X = transpose(hcat(float.(reshape.(images,:))...))
y = [i == label ? 1 : 0 for label in labels, i in 0:9]

# split into test and train data
split = Int(ceil(length(images) * 0.8))

X_train = X[1:split, :]
X_test = X[split+1:end,:]
y_train = y[1:split,:]
y_test = y[split+1:end,:]

n_test = size(X_test)[1]

# train with DP-(S)GD
include("flux_dp.jl")

#m = FluxDP.train_dp(X_train,y_train,0.2,0.2,0.2,5,1000)
m = FluxDP.train_dp_nobatch_noloop(X_train,y_train,0.2,0.2,0.2,2)

# compute some stats
loss(x,y) = Flux.crossentropy(m.model(x), y)
avg_loss() = sum(loss(d,l) for (d,l) in zip(eachrow(X_test),eachrow(y_test))) / n_test
correct((d,l),) = (Flux.onecold(m.model(d)) == Flux.onecold(l))
accuracy() = sum([correct((X_test[i,:], y_test[i,:])) for i in 1:n_test]) / n_test

println(avg_loss())
println(accuracy())

m
