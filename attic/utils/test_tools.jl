"Test if two DMTypes are equal except for differently named variables."
function equal_except_varnames(t1::DMType, t2::DMType)
    m = @mdo TC begin
        t <- unify(t1,t2)
        t <- msimplify_constraints()
        C <- extract_Cs()
        return (isempty(C) ? true : false)
    end
    try
        run(m)[2]
    catch UnificationError
        false
    end
end

