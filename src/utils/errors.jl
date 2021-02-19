"An error to throw upon finding a constraint that is violated."
abstract type ConstraintViolation <: Exception end


struct ArithmeticsError <: ConstraintViolation
msg::String
end

struct WrongNoOfArgs <: ConstraintViolation
msg::String
end

struct NotNumeric <: ConstraintViolation
msg::String
end

struct NoChoiceFound <: ConstraintViolation
msg::String
end

struct NotSubtype <: ConstraintViolation
msg::String
end

struct NotSupremum <: ConstraintViolation
msg::String
end

struct UnificationError <: ConstraintViolation
msg::String
end

"An error to throw upon encountering a variable that was never defined."
struct NotInScope <: Exception
msg::String
end
