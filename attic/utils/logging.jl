
using MLStyle

@data LogCategory begin
    Log_TypecheckPhases :: () => LogCategory
    Log_SubstitutionDetails :: () => LogCategory
    Log_UnificationPhases :: () => LogCategory
    Log_ResolveCaptures :: () => LogCategory
    Log_ResolveCapturesSubstitutions :: () => LogCategory
end

global global_LogCategories = Set([])

#################
# Logging
function printdebug(c :: LogCategory, s :: String)
    if c ∈ global_LogCategories
        println(s)
    end
end
