namespace OpenProblem

/-- The local update: the new value of a cell from its left neighbour `a`, itself `b`,
and its right neighbour `c`. It is `a XOR (b OR c)`. -/
def rule (a b c : Bool) : Bool := xor a (b || c)

/-- The grid. Row `0` has a single `true` cell, at position `0`. Each later row comes from the
row above by applying `rule` at every position. `cell t p` is the value at row `t`, position `p`. -/
def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

/-- The center column: the value at position `0` in row `t`. -/
def center (t : Nat) : Bool := cell t 0

/-- A sequence is eventually periodic: from some row `T` on it repeats with some period `P > 0`. -/
def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

/-- The claim: the center column is not eventually periodic. -/
def Claim : Prop := ¬ EventuallyPeriodic center

end OpenProblem
