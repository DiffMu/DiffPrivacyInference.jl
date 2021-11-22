using Flux
# get MNIST dataset
images = Flux.Data.MNIST.images();
labels = Flux.Data.MNIST.labels();
#preprocess data into float matrix and one-hot label vectors
X = transpose(hcat(float.(reshape.(images,:))...))
y = [onehot(y,0:9) for y in labels]
# train with DP-SGD
train_dp(X,y,1,0.9,0.9,1)
