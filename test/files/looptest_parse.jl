function looptest(a::Vector)
    return a
end

function looptest(a::Int64)
    for j in 2:4, i in 1:2:5
        g(x) = j + x + x + 5
        a += j + i
        it = 1:10
        for k in it #[1,3,i,j]
            if i+j+k == 4
                a += g(k)
            else
                a += g(k) + i
            end
        end
    end
    return a
end

