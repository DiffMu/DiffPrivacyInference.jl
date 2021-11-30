using Flux

# get MNIST dataset
images = Flux.Data.MNIST.images();
labels = Flux.Data.MNIST.labels();

#preprocess data into float matrix and one-hot label vectors
X = transpose(hcat(float.(reshape.(images,:))...))
y = [i == label ? 1 : 0 for label in labels, i in 0:9]

# train with DP-SGD
train_dp(X,y,2,0.5,1,60000)
