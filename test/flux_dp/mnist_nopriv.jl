using Flux, Statistics
using Flux.Data: DataLoader
using Flux: onehotbatch, onecold, @epochs
using Flux.Losses: logitcrossentropy
using Base: @kwdef
using MLDatasets


function getdata(args, device)
    ENV["DATADEPS_ALWAYS_ACCEPT"] = "true"

    # Loading Dataset	
    xtrain, ytrain = MLDatasets.MNIST.traindata(Float32)
    xtest, ytest = MLDatasets.MNIST.testdata(Float32)
	
    # Reshape Data in order to flatten each image into a linear array
    xtrain = Flux.flatten(xtrain)
    xtest = Flux.flatten(xtest)

    # One-hot-encode the labels
    ytrain, ytest = onehotbatch(ytrain, 0:9), onehotbatch(ytest, 0:9)

    # Create DataLoaders (mini-batch iterators)
    train_loader = DataLoader((xtrain, ytrain), batchsize=args.batchsize, shuffle=true)
    test_loader = DataLoader((xtest, ytest), batchsize=args.batchsize)

    return train_loader, test_loader
end

function build_model(; imgsize=(28,28,1), nclasses=10)
    return Chain(
            Dense(prod(imgsize),40, relu),
            Dense(40, nclasses),
            softmax)
end

function loss_and_accuracy(data_loader, model, device)
    acc = 0
    ls = 0.0f0
    num = 0
    for (x, y) in data_loader
        x, y = device(x), device(y)
        ŷ = model(x)
        ls += logitcrossentropy(ŷ, y, agg=sum)
        acc += sum(onecold(ŷ) .== onecold(y))
        num +=  size(x)[end]
    end
    return ls / num, acc / num
end


@kwdef mutable struct Args
    η::Float64 = 3e-4       # learning rate
    batchsize::Int = 500    # batch size
    epochs::Int = 1        # number of epochs
end

function train(; kws...)
    args = Args(; kws...) # collect options in a struct for convenience

    @info "Training on CPU"
    device = cpu

    # Create test and train dataloaders
    train_loader, test_loader = getdata(args, device)

    # Construct model
    model = build_model() |> device
    ps = Flux.params(model) # model's trainable parameters
    
    ## Optimizer
    opt = Descent(args.η)
    
    ## Training
    for epoch in 1:args.epochs
        i = 1
        xs = 0
        for (X, Y) in train_loader
            # for the benchmark we compute per-sample gradient as we have to do that for DP
            for (x,y) in zip(eachcol(X), eachcol(Y))
               gs = gradient(() -> logitcrossentropy(model(x), y), ps) # compute gradient
               Flux.Optimise.update!(opt, ps, gs) # update parameters
               i += 1
               xs = size(x)
            end
        end
        
        # Report on train and test
        train_loss, train_acc = loss_and_accuracy(train_loader, model, device)
        test_loss, test_acc = loss_and_accuracy(test_loader, model, device)
        println("Epoch=$epoch, took $i iterations, batch size was $xs")
        println("  train_loss = $train_loss, train_accuracy = $train_acc")
        println("  test_loss = $test_loss, test_accuracy = $test_acc")
    end
end


function train_dp(; kws...)
    args = Args(; kws...) # collect options in a struct for convenience

    @info "Training on CPU"
    device = cpu

    # Create test and train dataloaders
    train_loader, test_loader = getdata(args, device)

    # Construct model
    model = build_model() |> device
    ps = Flux.params(model) # model's trainable parameters
    
    ## Optimizer
    opt = Descent(args.η)

    # zero gradient
    G = gradient(() -> 0, ps)
   
    ## Training
    for epoch in 1:args.epochs
        i = 1
        xs = 0
        for (X, Y) in train_loader
            for p in G.params
               G[p] = fill!(similar(p), 0)
            end
            # for the benchmark we compute per-sample gradient as we have to do that for DP
            for (x,y) in zip(eachcol(X), eachcol(Y))
               gs = gradient(() -> logitcrossentropy(model(x), y), ps) # compute gradient
               
               clip!(L2,DMGrads(gs))


               i += 1
               xs = size(x)

               G .+= gs
            end
            gaussian_mechanism!(2/500, 0.1, 0.1, DMGrads(G))
            Flux.Optimise.update!(opt, ps, G) # update parameters
        end
        
        # Report on train and test
        train_loss, train_acc = loss_and_accuracy(train_loader, model, device)
        test_loss, test_acc = loss_and_accuracy(test_loader, model, device)
        println("Epoch=$epoch, took $i iterations, batch size was $xs")
        println("  train_loss = $train_loss, train_accuracy = $train_acc")
        println("  test_loss = $test_loss, test_accuracy = $test_acc")
    end
end

### Run training 
if abspath(PROGRAM_FILE) == @__FILE__
    train()
end
# train(η=0.01) # can change hyperparameters
