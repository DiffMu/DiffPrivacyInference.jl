using Flux

# get MNIST dataset
images = Flux.Data.MNIST.images();
labels = Flux.Data.MNIST.labels();

# preprocess data into float matrix and one-hot label matrix
X = transpose(hcat(float.(reshape.(images,:))...))
y = [i == label ? 1 : 0 for label in labels, i in 0:9]

# train with DP-GD
include("flux_dp.jl")

split = Int(ceil(length(images) * 0.8))

X_train = X[1:split, :]
X_test = X[split+1:end, :]
y_train = y[1:split,:]
y_test = y[split+1:end,:]

m = FluxDP.train_dp(X_train,y_train,0.9,0.2,12,10,100)

loss(x,y) = Flux.crossentropy(m.model(x), y)
accuracy((d, l,)) = sum(loss(d,l)) / length(d)
println(map(accuracy, zip(eachrow(X_test),eachrow(y_test))))
sum(map(accuracy, zip(eachrow(X_test),eachrow(y_test)))) / length(y_test)
