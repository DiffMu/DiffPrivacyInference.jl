######################################################
## special context operations


# NOTE: `Small` *is* allowed to not be a subset of `Big`
function diffNames(Big :: NameCtx, Small :: NameCtx) :: Names
    begin
        lostNames = setdiff(Small.names, Big.names)
        println("+ minus: The following names disappeared: $lostNames")
    end

    ΔNames = setdiff(Big.names, Small.names)
    # newSmall = NameCtx(Small.names, Big.current_ctr)
    ΔNames #, newSmall
end

function isGlobal((ΔS, ΔT) :: DeltaNames)
    function p(c) :: Bool
        commonTs = intersect(free_TVars(c), ΔT)
        commonSs = intersect(free_SVars(c), ΔS)
        length(commonTs) == 0 && length(commonSs) == 0
    end
    # p = c -> begin
    #     commonTs = intersect(free_TVars(c), ΔT)
    #     commonSs = intersect(free_SVars(c), ΔS)
    #     commonTs == [] && commonSs == []
    # end
    p
end

####################################################
## Splitting substitutions

@data SplitSubResult{A} begin
    Global{A}   :: (Symbol, A)       => SplitSubResult{A}

    # (x,a,v) means x ∈ Δ, a ∉ Δ, and a = "v"
    #         and we have to do x := v
    #         and then re-add `a` to the names
    ToFix{A}   :: (Symbol, Symbol, A)  => SplitSubResult{A}

    Local{A} :: (Symbol , A)      => SplitSubResult{A}

    # (x,y) means that x ∉ Δ, and y contains a symbol which is in Δ
    ErrorEscape{A} :: (Symbol, A) => SplitSubResult{A}
end

struct SplitSubstitutionsResult
    Global  :: Substitutions
    Local   :: Substitutions
    Fixes   :: Substitutions
    GeneratedConstraints :: Constraints
    LocalSymbolsRemoved :: DeltaNames
    GlobalSymbolsAdded  :: DeltaNames
end

function splitSub((ΔS, ΔT) :: DeltaNames, (x, τ) :: AnySSub) :: SplitSubResult{<:Union{DMType,Sensitivity}}
    symbolGlobal = x ∉ ΔT
    valueGlobal  = isGlobal((ΔS, ΔT))(τ)
    @match (symbolGlobal, valueGlobal) begin
        (false, _)    => Local(x, τ)
        (true, true)  => Global(x, τ)
        (true, false) => begin
            if τ isa DMType
                @match τ begin
                    TVar(y) => ToFix(y,x, TVar(x))
                    _       => ErrorEscape(x, τ)
                end
            else
                val = try_destructure_Sensitivity(τ)
                if val isa Symbol
                    ToFix(val,x,symbols(x))
                elseif val isa Nothing
                    ErrorEscape(x, τ)
                else
                    error("INTERNAL ERROR: Classified $τ as a tainted (local) value, but it cannot be.")
                end
            end
        end
    end
end


function makeSingleSSub((x,xv) :: Tuple{Symbol, Symbol}) :: SSSub
    x , symbols(sv)
end

function makeSingleTSub((x,xv) :: Tuple{Symbol, Symbol}) :: TSSub
    x , TVar(xv)
end

function apply_SensFix((x, ξ) :: TSSub, v :: Tuple{Symbol,Symbol}) :: TSSub
    ξ = singleSSub(ξ, makeSingleSSub(v))
    (x, ξ)
end

function apply_TypeFix((x, ξ) :: TSSub, (y,yv) :: Tuple{Symbol,Symbol}) :: TSSub
    if x == y
        x = yv
    end

    ξ = singleTSub(ξ, makeSingleTSub((y,yv)))
    (x, ξ)
end

function apply_SensFix((x, ξ) :: SSSub, (y,yv) :: Tuple{Symbol,Symbol}) :: SSSub
    if x == y
        x = yv
    end

    ξ = singleSSub(ξ, makeSingleSSub((y,yv)))
    (x, ξ)
end

function apply_TypeFix(σ :: SSSub, v :: Tuple{Symbol,Symbol}) :: SSSub
    σ
end

function apply_TypeFixes(σ :: AnySSub, v :: Vector{Tuple{Symbol,Symbol}}) :: AnySSub
    for s in v
        σ = apply_TypeFix(σ, s)
    end
    σ
end

function apply_SensFixes(σ :: AnySSub, v :: Vector{Tuple{Symbol,Symbol}}) :: AnySSub
    for s in v
        σ = apply_SensFix(σ, s)
    end
    σ
end

function splitSub(Δ :: DeltaNames, σs :: Substitutions) :: SplitSubstitutionsResult
    Global   = []
    Local    = []
    # Fixes    = []
    SensFixes = Vector{Tuple{Symbol,Symbol}}()
    TypeFixes = Vector{Tuple{Symbol,Symbol}}()
    GeneratedConstraints  = Constraints()
    S_LocalSymbolsRemoved = []
    S_GlobalSymbolsAdded  = []
    T_LocalSymbolsRemoved = []
    T_GlobalSymbolsAdded  = []
    for σ in σs
        σ = apply_TypeFixes(σ, TypeFixes)
        σ = apply_SensFixes(σ, SensFixes)
        @match splitSub(Δ, σ) begin
            Global(x,v) => push!(Global, (x,v))
            Local(x,v) => push!(Local, (x,v))
            ToFix(x,a,v::Sensitivity) => begin
                push!(S_LocalSymbolsRemoved, x)
                push!(S_GlobalSymbolsAdded, a)
                push!(SensFixes, (x,a))
            end
            ToFix(x,a,v::DMType) => begin
                push!(T_LocalSymbolsRemoved, x)
                push!(T_GlobalSymbolsAdded, a)
                push!(TypeFixes, (x,a))
            end

            ErrorEscape(x,v) => begin
                println("Found a substitution where a global variable is replaced by a value containing a local one, thus making the local one escape its scope.\n When trying: $x := $v\nWhile the local names are:\n  $Δ\nThus, generating a constraint.")
                if v isa Sensitivity
                    push!(GeneratedConstraints,isEqual(symbols(x),v))
                elseif v isa DMType
                    push!(GeneratedConstraints,isEqualType(TVar(x),v))
                else
                    error("INTERNAL ERROR: Expected $v to be either a sensitivity or a type.")
                end

            end
        end
    end
    Fixes = [map(makeSingleSSub, SensFixes) ; map(makeSingleTSub, TypeFixes)]

    SplitSubstitutionsResult(Global,Local,Fixes,GeneratedConstraints,
                             (Set(S_LocalSymbolsRemoved), Set(T_LocalSymbolsRemoved)),
                             (Set(S_GlobalSymbolsAdded),  Set(T_GlobalSymbolsAdded)))
end

#####################################################
## Splitting contexts by names (sensitivity and type variable deltas)

## helper
## TODO: Is there a proper, more performant way, than filtering twice?
function splitPredicate(list, fn)
    list1 = filter((a -> fn(a)), list)
    list2 = filter((a -> !fn(a)), list)
    list1, list2
end

function splitByIsGlobal((ΔS, ΔT) :: DeltaNames, a)
    function p(c) :: Bool
        commonTs = intersect(free_TVars(c), ΔT)
        commonSs = intersect(free_SVars(c), ΔS)
        # commonTs == [] && commonSs == []
        length(commonTs) == 0 && length(commonSs) == 0
    end
    splitPredicate(a, p)
end

function splitByNames(Δ :: DeltaNames, cs :: Constraints) :: Tuple{Constraints, Constraints}
    splitByIsGlobal(Δ, cs)
    # splitPredicate(cs, isGlobal(Δ))
end

function splitByNames(Δ :: DeltaNames, Σ :: SCtx) :: Tuple{SCtx, SCtx}
    splitByIsGlobal(Δ, Σ)
    # splitPredicate(SCtx, isGlobal(Δ))
end

function splitByNames((ΔS, ΔT) :: DeltaNames, (S,T,C,Σ) :: Full{SCtx}) :: Tuple{Full{SCtx}, Full{SCtx}}
    S_global = NameCtx(setdiff(S.names, ΔS), S.current_ctr)
    S_local  = NameCtx(ΔS, S.current_ctr)
    T_global = NameCtx(setdiff(T.names, ΔT), T.current_ctr)
    T_local  = NameCtx(ΔT, T.current_ctr)
    (C_global, C_local) = splitByNames((ΔS, ΔT), C)
    (Σ_global, Σ_local) = splitByNames((ΔS, ΔT), Σ)

    (S_global, T_global, C_global, Σ_global) , (S_local, T_local, C_local, Σ_local)
end

function applyReorientationFixes(res :: SplitSubstitutionsResult, (S,T,C,Σ) :: Full{SCtx}) :: Full{SCtx}
    S = NameCtx(union(S.names, res.GlobalSymbolsAdded[1]), S.current_ctr)
    T = NameCtx(union(T.names, res.GlobalSymbolsAdded[2]), T.current_ctr)
    # NOTE: We apply the substitutions only to C, ...
    C = apply_subs(C, res.Fixes)
    #       ... not to the generated constraints in this line:
    C = [C ; res.GeneratedConstraints]
    Σ = apply_subs(Σ, res.Fixes)
    (S,T,C,Σ)
end

function applyReorientationFixes(res :: SplitSubstitutionsResult, C :: Constraints) :: Constraints
    C = [C ; res.GeneratedConstraints]
    apply_subs(C, res.Fixes)
end

function applyReorientationFixes(res :: SplitSubstitutionsResult, (ΔS, ΔT) :: DeltaNames) :: DeltaNames
    setdiff(ΔS, res.LocalSymbolsRemoved[1]), setdiff(ΔT, res.LocalSymbolsRemoved[2])
end


# This returns:
# (newΔS, newΔT) , σs-global, σs-local, A-global, A-local
function splitByNames_reorientSubstitutions(Δ :: DeltaNames, σs :: Substitutions, a :: A, ) :: Tuple{DeltaNames,Substitutions, Substitutions, A, A} where {A}
    subres = splitSub(Δ, σs)
    a = applyReorientationFixes(subres, a)
    Δ = applyReorientationFixes(subres, Δ)
    (a_global, a_local) = splitByNames(Δ, a)
    Δ, subres.Global, [subres.Fixes ; subres.Local], a_global, a_local
end


## Computing the difference between contexts
function diff(F :: Full{SCtx}, σs :: Substitutions, prevNames :: Tuple{NameCtx,NameCtx}) :: Tuple{Full{SCtx}, Substitutions, DeltaCtx}
    ΔS = diffNames(F[1], prevNames[1])
    ΔT = diffNames(F[2], prevNames[2])
    Δ = (ΔS, ΔT)

    # reorient substitutions & split full scontext
    Δ, σs_global, σs_local, F_global, (S_local, T_local, C_local, Σ_local) = splitByNames_reorientSubstitutions(Δ, σs, F)

    # NOTE: We assume that the substitutions were already applied, thus we can
    # forget about `σs_local`
    # TODO: Implement check for this condition <<here>>
    println("=> local substitutions to forget:\n$σs_local\n")

    # NOTE: We do not allow to have local typing judgements, if some are left, we error out
    if length(Σ_local) > 0
        error("INTERNAL ERROR: Expected Σ_local to be empty when computing context difference for local abstraction. But Σ_local = $Σ_local")
    end

    # return computed global context, and local delta-context
    F_global, σs_global, ((S_local.names, T_local.names), C_local)
end


