import Statement

namespace OpenProblem.AncestryBlueprint

abbrev Trace := Nat → Bool

/-- Driven half-line. At time zero the wall is the unique allowed mark;
all strict eastern entries start white. Spatial index zero is the wall. -/
def east (c : Trace) : Nat → Nat → Bool
  | 0, 0 => c 0
  | 0, _+1 => false
  | t+1, 0 => c (t+1)
  | t+1, j+1 => rule (east c t j) (east c t (j+1)) (east c t (j+2))

/-- Invert the local gate sideways, with the two eastern traces in hand. -/
def unleft (mid right : Trace) : Trace := fun t =>
  xor (mid (t+1)) (mid t || right t)

def pair (c : Trace) : Nat → Trace × Trace
  | 0 => (c, fun t => east c t 1)
  | d+1 => let h := pair c d; (unleft h.1 h.2, h.1)

/-- The unknown west seed reconstructed from a proposed wall, one bit per depth. -/
def origin (c : Trace) (d : Nat) : Bool := (pair c d).1 0

/-- Finite data agreement, excluding the right endpoint. -/
def agree (a b : Trace) (n : Nat) : Prop := ∀ i, i < n → a i = b i

/-- Every putative periodic wall can be specified by a finite onset/period word.
This is a sequence on TIME, never a spatial periodicization of a genuine age row. -/
def repeatWord (c : Trace) (T P i : Nat) : Bool :=
  if i < T then c i else c (T + (i-T) % P)

theorem L1 (c : Trace) (hmark : c 0 = true) (T P : Nat) (hp : 0 < P)
    (seedPrefix : ∀ j, 0 < j → j < T+P → origin (repeatWord c T P) j = false) :
    ∃ j, T+P ≤ j ∧ origin (repeatWord c T P) j = true := by
  -- Finite power obstruction: once one full word passed the exact blank-west
  -- prefix test, a later finite power must create a WEST mark at row zero.
  -- No return of either half-row or of the sideways map's sections is assumed.
  sorry

theorem east_actual (t j : Nat) : east center t j = cell t (j:Int) := by
  induction t generalizing j with
  | zero =>
    cases j with
    | zero => rfl
    | succ j => simp [east, cell]; omega
  | succ t ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [east, ih, cell]
      congr 1 <;> congr 1 <;> omega

theorem inverse_actual (t : Nat) (x : Int) :
    xor (cell (t+1) x) (cell t x || cell t (x+1)) = cell t (x-1) := by
  rw [cell]
  generalize cell t (x-1) = a
  generalize cell t x = b
  generalize cell t (x+1) = c
  cases a <;> cases b <;> cases c <;> rfl

theorem pair_actual (d t : Nat) :
    (pair center d).1 t = cell t (-(d:Int)) ∧
    (pair center d).2 t = cell t (-(d:Int)+1) := by
  induction d generalizing t with
  | zero => exact ⟨rfl, east_actual t 1⟩
  | succ d ih =>
    constructor
    · change xor ((pair center d).1 (t+1)) ((pair center d).1 t || (pair center d).2 t) = _
      rw [(ih (t+1)).1, (ih t).1, (ih t).2, inverse_actual]
      congr 1 <;> omega
    · change (pair center d).1 t = _
      rw [(ih t).1]
      congr 1 <;> omega

theorem actual_origin (d : Nat) (hd : 0 < d) : origin center d = false := by
  change (pair center d).1 0 = _
  rw [(pair_actual d 0).1,cell]
  exact decide_eq_false (by omega)

theorem repeat_eq {c : Trace} {T P : Nat} (hp : 0 < P)
    (period : ∀ t, T ≤ t → c (t+P) = c t) : repeatWord c T P = c := by
  funext i
  unfold repeatWord
  split
  · rfl
  · rename_i hi
    have mult (n k : Nat) : c (T+k+P*n) = c (T+k) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.mul_succ, ←Nat.add_assoc, period _ (by omega), ih]
    have idn := Nat.mod_add_div (i-T) P
    have e := mult ((i-T)/P) ((i-T)%P)
    rw [show T + (i-T)%P + P*((i-T)/P) = i by omega] at e
    exact e.symm

theorem close_step4 (hcenter : EventuallyPeriodic center) : False := by
  obtain ⟨T,P,hp,h⟩ := hcenter
  have same := repeat_eq hp h
  have init : ∀ j, 0 < j → j < T+P → origin (repeatWord center T P) j = false := by
    intro j hj _
    rw [same]
    exact actual_origin j hj
  obtain ⟨j,hj,hit⟩ := L1 center (by decide) T P hp init
  rw [same, actual_origin j (by omega)] at hit
  contradiction

end OpenProblem.AncestryBlueprint

#print axioms OpenProblem.AncestryBlueprint.close_step4
