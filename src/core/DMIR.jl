
TAsgmt = Tuple{Symbol, <:DataType}

# the terms that come out of the parser.
@data DMTerm begin
    ret :: DMTerm => DMTerm # just for testing privacy language.
    sng :: Number => DMTerm # singletons
    var :: (Symbol, DataType) => DMTerm
    arg :: (Symbol, DataType) => DMTerm
    op :: (Symbol, Vector{DMTerm}) => DMTerm # builtin operators, like + or *
    phi :: (DMTerm, DMTerm, DMTerm) => DMTerm # condition, true-path, false-path
    lam :: (Vector{<:TAsgmt}, DMTerm) => DMTerm
    lam_star :: (Vector{<:TAsgmt}, DMTerm) => DMTerm
    dphi :: Vector{lam} => DMTerm # multiple dispatch: the lam whose signature matches gets used.
    apply :: (DMTerm, Vector{DMTerm}) => DMTerm
    iter :: (DMTerm, DMTerm, DMTerm) => DMTerm # terms are iteration start, step size and end.
    flet :: (Symbol, Vector{<:DataType}, lam, DMTerm) => DMTerm
    abstr :: DMTerm => DMTerm
    # abstr :: (DMTerm) => DMTerm #TODO: Implement this => abstract over all new s/t variables inside
#    trttup :: Vector{DMTerm} => DMTerm                     # Transparent version of tuple
#    trtlet :: (Vector{TAsgmt}, DMTerm, DMTerm) => DMTerm   #                     and let
    tup :: Vector{DMTerm} => DMTerm                     # Paper version of tuple
    tlet :: (Vector{TAsgmt}, DMTerm, DMTerm) => DMTerm   #                     and let
    loop :: (iter, tup, lam) => DMTerm
    slet :: (TAsgmt, DMTerm, DMTerm) => DMTerm # let v = e1 in e2
    vcreate :: (DMTerm, lam) => DMTerm
    vect :: Vector{DMTerm} => DMTerm
    index :: (DMTerm, DMTerm) => DMTerm
    len :: DMTerm => DMTerm # length of a vector
    chce :: Dict{Vector{<:DataType}, DMTerm} => DMTerm
    gauss :: (Tuple{DMTerm, DMTerm, DMTerm}, lam) => DMTerm
end

function pretty_print(t::DMTerm) :: String
    @match t begin
        sng(v)               => string(v)
        var(v, _)            => string(v)
        op(f, vs)            => join(map(pretty_print, vs), " $(string(f)) ")
        phi(c, tr, f)        => "if { " * pretty_print(c) * " } then { " * pretty_print(tr) * " } else { " * pretty_print(f) * " }"
        ret(l)               => "return " * pretty_print(l)
        lam(vs, b)           => "λ (" * pretty_print(vs) * ").{ " * pretty_print(b) * " }"
        lam_star(vs, b)      => "λ* (" * pretty_print(vs) * ").{ " * pretty_print(b) * " }"
        apply(l, as)         => pretty_print(l) *"(" * pretty_print(as) * ")"
        iter(f, s, l)        => "range(" * pretty_print([f,s,l]) * ")"
        loop(it, cs, b)      => "loop { " * pretty_print(b) * " } for " * pretty_print(it) * " on " * pretty_print(cs)
        tup(ts)              => "tup(" * pretty_print(ts) * ")"
        tlet(xs, tu, t)      => "tlet " * pretty_print(xs) * " = " * pretty_print(tu) * " in { " * pretty_print(t) *" }"
        slet(x, v, t)        => "let " * pretty_print(x) * " = " * pretty_print(v) * " in { " * pretty_print(t) *" }"
        flet(f, s, l, t)        => "flet " * pretty_print(f) * " = " * pretty_print(l) * " in { " * pretty_print(t) *" }"
#        vcreate(s, l)        => 
        vect(vs)             => "[" * pretty_print(vs) * "]"
        index(v, i)          => pretty_print(v) * "[" * pretty_print(i) * "]"
        gauss(ps, b)      => "gauss [ " * pretty_print(ps) * " ] { " *pretty_print(b) *  " }"
        #        len(v)               => 
        t                    => error("no match evaluating $t :: $(typeof(t))")
    end
end

pretty_print(s::Symbol) = string(s)
pretty_print((a,t)::TAsgmt) = string(a) * ((t == Any) ? "" : ("::"*string(t)))
pretty_print(ts::Vector{<:TAsgmt}) = join(map(pretty_print, ts), ", ")
pretty_print(ts::Vector{DMTerm}) = join(map(pretty_print, ts), ", ")


# turn a DMTerm into a julia Expr
# that means you have to call eval on the result to actually evaluate ;)
function evaluate(t::DMTerm) :: Union{Number, Symbol, Expr}
    @match t begin
        sng(v)               => v
        var(v, _)            => v
        op(f, vs)            => :($(f)($(map(evaluate, vs)...)))
        phi(c, tr, f)        => :($(evaluate(c)) ? $(evaluate(tr)) : $(evaluate(f)))
        ret(l)               => eval(evaluate(l))
        lam(vs, b)           => :($(Expr(:tuple, map(evaluate,vs)...)) -> $(evaluate(b)))
        lam_star(vs, b)      => :($(Expr(:tuple, map(evaluate,vs)...)) -> $(evaluate(b)))
        apply(l, as)         => Expr(:call, evaluate(l), map(evaluate, as)...)
        iter(f, s, l)        => Expr(:call, :(:), map(evaluate, [f, s, l])...)
        loop(it, cs, b)      => Expr(:call, :forloop, evaluate(b), evaluate(it), evaluate(cs))
#        trttup(ts)           => Expr(:tuple, map(evaluate,ts)...)
#        trtlet(xs, tu, t)    => Expr(:let, :($(Expr(:tuple, map(evaluate,xs)...)) = $(evaluate(tu))), evaluate(t))
        tup(ts)              => Expr(:tuple, map(evaluate,ts)...)
        tlet(xs, tu, t)      => Expr(:let, :($(Expr(:tuple, map(evaluate,xs)...)) = $(evaluate(tu))), evaluate(t))
        slet(x, v, t)        => Expr(:let, :($(evaluate(x)) = $(evaluate(v))), evaluate(t))
        flet(f, s, lam(vs,b), t)=> Expr(:block, Expr(:(=), Expr(:call, f, fsig(vs)...), evaluate(b)), evaluate(t))
        vcreate(s, l)        => Expr(:vect, [evaluate(apply(l, [sng(i)])) for i in 1:evaluate(s)]...)
        vect(vs)             => Expr(:vect,  map(evaluate,ts)...)
        index(v, i)          => :($(evaluate(v))[$(evaluate(i))])
        len(v)               => :(length($(evaluate(v))))
        gauss((s,ϵ,δ),f)   => :(gaussian_mechanism($(evaluate(f)), $(evaluate(δ)), $(evaluate(s)), $(evaluate(ϵ))))
        t                    => error("no match evaluating $t :: $(typeof(t))")
    end
end

evaluate(t::TAsgmt) = t[1]

function forloop(body, iter, captures::Tuple)
    # body is assumed to be a function that takes an iteration variable
    # and a tuple containing captured values from the previous iteration or, in the first step, the outer scope.
    # the returned l takes an iterator and a tuple of those values captured from outer scope, and loops.
    for i in iter
        captures = body(i, captures)
    end
    return captures
end

"Make the input function DP by applying the gaussian mechanism."
function gaussian_mechanism(s::Real, ϵ::Real, δ::Real, f::Function)
    (x...) -> f(x...) + rand(Normal(0, (2 * log(1.25/δ) * s^2) / ϵ^2))
end

function fsig(vs :: Vector{<:TAsgmt}) :: Vector
    args = []
    for (dv,dt) in vs
        if  dt == Any
            push!(args, dv)
        else
            push!(args, :($dv::$dt))
        end
    end
    return args
end


function Base.isequal(τ1::DMType, τ2::DMType)
    @match (τ1, τ2) begin
        (DMInt(), DMInt()) => true;
        (DMReal(), DMReal()) => true;
        (Constant(X, c), Constant(Y, d)) => isequal(X, Y) && isequal(c, d);
        (DMTup(Xs), DMTup(Ys)) => isequal(Xs, Ys);
        (DMVec(s, X), DMVec(t, Y)) => isequal(s, t) && isequal(X, Y);
        (TVar(s), TVar(t)) => isequal(s, t);
        (Arr(v, s), Arr(w, t)) => isequal(v, w) && isequal(s, t);
        (ArrStar(v, s), ArrStar(w, t)) => isequal(v, w) && isequal(s, t);
        (_, _) => false;
    end
end

function pretty_print(v::Vector, print_fn)
    @match v begin
        [] => "()"
        [x] => "(" * print_fn(x) * ")"
        [x,xs...] =>
        let
            s = "(" * print_fn(x)
            for y in xs
                s *=  ", " * print_fn(y)
            end
            s * ")"
        end
    end
end

pretty_print(x) = string(x)

function pretty_print(t::DMType)
    @match t begin
        DMInt() => "Int"
        DMReal() => "Real"
        Constant(ty, te) => pretty_print(ty) * "[" * pretty_print(te) * "]"
        DMTup(tys) => pretty_print(tys, pretty_print)
        DMVec(len, ty) => "Vec(" * pretty_print(ty) * ", " * pretty_print(len) * ")"
        TVar(symb) =>  "tvar." * pretty_print(symb)
        Arr(args, ret) =>
            let
                pretty_print(args, ((sens,ty),)-> pretty_print(ty) * " @(" * pretty_print(sens) * ")") * " ==> " * pretty_print(ret)
            end
            ArrStar(args, ret) =>
            let
                pretty_print(args, ((sens,ty),)-> pretty_print(ty) * " @(" * pretty_print(sens) * ")") * " *=*=>* " * pretty_print(ret)
            end
    end
end

