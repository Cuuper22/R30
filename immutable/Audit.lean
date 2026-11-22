import Solution

open OpenProblem

example : Claim ∨ ¬ Claim := by
  first
    | exact Or.inl answer
    | exact Or.inr answer
#print axioms answer
