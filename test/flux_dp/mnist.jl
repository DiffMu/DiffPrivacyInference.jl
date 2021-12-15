using Flux

# get MNIST dataset
images = Flux.Data.MNIST.images();
labels = Flux.Data.MNIST.labels();

# preprocess data into float matrix and one-hot label matrix
X = transpose(hcat(float.(reshape.(images,:))...))
y = [i == label ? 1 : 0 for label in labels, i in 0:9]

# train with DP-GD
train_dp(X,y,0.9,0.2,1,1)
