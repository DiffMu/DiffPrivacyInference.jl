"An error to throw upon finding a constraint that is violated."
abstract type ConstraintViolation <: Exception end

"An error to throw upon invalid arithmetic operations."
struct ArithmeticsError <: ConstraintViolation
msg::String
end

"An error to throw upon calling a function with the wrong number of arguments."
struct WrongNoOfArgs <: ConstraintViolation
msg::String
end

"An error to throw upon using a non-numeric value in a numeric context."
struct NotNumeric <: ConstraintViolation
msg::String
end

"An error to throw upon absence of a matching method in multiple dispatch."
struct NoChoiceFound <: ConstraintViolation
msg::String
end

"An error to throw upon vioaltion of a sunbype constraint."
struct NotSubtype <: ConstraintViolation
msg::String
end

"An error to throw upon violation of a supremum constraint."
struct NotSupremum <: ConstraintViolation
msg::String
end

"An error to throw upon a failed type or sensitivity unification attempt."
struct UnificationError <: ConstraintViolation
msg::String
end

"An error to throw upon encountering a variable that was never defined."
struct NotInScope <: Exception
msg::String
end
