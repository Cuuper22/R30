import Statement

/-! Route A. Laurent coefficients are represented by their integer exponent.
Multiplication by z + z⁻¹ is the linear Rule 90 propagator. Rule 30 injects
one unit at each right endpoint of a black run. Separate the unique outer
endpoint from all interior endpoints, at EVERY genuine singleton row. -/
namespace OpenProblem.BoundsBlueprint

def interiorSource (t : Nat) (x : Int) : Bool :=
  (cell t x && !(cell t (x + 1))) && decide (x ≠ (t : Int))

/-- Parity of all paths from genuine interior black-run endpoints to (t,x). -/
def interior : Nat → Int → Bool
  | 0, _ => false
  | t + 1, x => xor (xor (interior t (x-1)) (interior t (x+1))) (interiorSource t x)

/-- Hard arithmetic link. On one sufficiently late dyadic shell, a Mersenne
coefficient and a non-Mersenne odd multiple have the SAME interior parity.
The multiple may be chosen after the shell; no periodicity or recurrence
of a guessed finite-state source is assumed. -/
theorem L1 (P N : Nat) (hP : 0 < P) :
    ∃ k j : Nat, 0 < j ∧ N < 2^k ∧
      interior (2^k - 1) 0 = interior ((2 * (P*j) + 1) * 2^k - 1) 0 := by
  sorry

def wave : Nat → Int → Bool
  | 0, x => decide (x = 0)
  | t + 1, x => xor (wave t (x-1)) (wave t (x+1))

/-- (1+z)(z+z⁻¹)^t + z^(t+1), including the initial singleton. -/
def fringe (t : Nat) (x : Int) : Bool :=
  xor (xor (wave t x) (wave t (x-1))) (decide (x = (t : Int) + 1))

private theorem rightVac (t : Nat) (x : Int) (h : (t : Int) < x) : cell t x = false := by
  induction t generalizing x with
  | zero => simp [cell]; omega
  | succ t ih =>
    simp only [cell, rule]
    rw [ih (x-1) (by omega), ih x (by omega), ih (x+1) (by omega)]
    rfl

private theorem rightMark (t : Nat) : cell t (t : Int) = true := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [cell, rule]
    rw [show ((t+1 : Nat) : Int)-1 = (t : Int) by omega, ih,
      rightVac t _ (by omega), rightVac t _ (by omega)]
    rfl

private theorem source_split (t : Nat) (x : Int) :
    (cell t x && !(cell t (x+1))) =
      xor (decide (x=(t:Int))) (interiorSource t x) := by
  by_cases h : x = (t:Int)
  · subst x
    simp [interiorSource, rightMark, rightVac t ((t:Int)+1) (by omega)]
  · simp [interiorSource, h]

private theorem local_split (a b c : Bool) :
    rule a b c = xor (xor a c) (b && !c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem fringe_step (t : Nat) (x : Int) :
    fringe (t+1) x = xor (xor (fringe t (x-1)) (fringe t (x+1))) (decide (x=(t:Int))) := by
  unfold fringe
  simp only [wave]
  rw [show x-1+1=x by omega, show x+1-1=x by omega]
  have h₁ : (x-1=(t:Int)+1) ↔ (x=((t+1:Nat):Int)+1) := by omega
  have h₂ : (x+1=(t:Int)+1) ↔ (x=(t:Int)) := by omega
  simp only [h₁,h₂]
  generalize wave t (x-1)=a; generalize wave t (x+1)=b
  generalize wave t (x-1-1)=c; generalize wave t x=d
  generalize decide (x=((t+1:Nat):Int)+1)=e; generalize decide (x=(t:Int))=f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

/-- Exact whole-row Laurent decomposition, with no periodicity assumption. -/
theorem row_split (t : Nat) (x : Int) :
    cell t x = xor (fringe t x) (interior t x) := by
  induction t generalizing x with
  | zero =>
    simp only [cell, interior, fringe, wave, Bool.xor_false]
    have h : (x-1=0) ↔ (x=(0:Nat)+1) := by omega
    simp only [h]
    generalize decide (x=0)=a
    generalize decide (x=(0:Nat)+1)=b
    cases a <;> cases b <;> rfl
  | succ t ih =>
    simp only [cell, local_split, interior, fringe_step]
    rw [source_split, ih (x-1), ih (x+1)]
    generalize fringe t (x-1)=a; generalize fringe t (x+1)=b
    generalize interior t (x-1)=c; generalize interior t (x+1)=d
    generalize decide (x=(t:Int))=e; generalize interiorSource t x=f
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

private theorem wave_two (t : Nat) (x : Int) :
    wave (t+2) x = xor (wave t (x-2)) (wave t (x+2)) := by
  simp only [wave]
  rw [show x-1-1=x-2 by omega, show x-1+1=x by omega,
      show x+1-1=x by omega, show x+1+1=x+2 by omega]
  generalize wave t (x-2)=a; generalize wave t x=b; generalize wave t (x+2)=c
  cases a <;> cases b <;> cases c <;> rfl

private theorem wave_double (n : Nat) : ∀ x : Int,
    wave (2*n) (2*x)=wave n x ∧ wave (2*n) (2*x+1)=false := by
  induction n with
  | zero =>
    intro x
    simp only [wave]
    constructor
    · congr 1; apply propext; omega
    · simp; omega
  | succ n ih =>
    intro x
    rw [show 2*(n+1)=2*n+2 by omega, wave_two, wave_two]
    rw [show 2*x-2=2*(x-1) by omega, show 2*x+2=2*(x+1) by omega,
      show 2*x+1-2=2*(x-1)+1 by omega, show 2*x+1+2=2*(x+1)+1 by omega,
      (ih (x-1)).1, (ih (x+1)).1, (ih (x-1)).2, (ih (x+1)).2]
    exact ⟨rfl,rfl⟩

private theorem wave_reflect (n : Nat) (x : Int) : wave n (-x) = wave n x := by
  induction n generalizing x with
  | zero => simp [wave]
  | succ n ih =>
    simp only [wave]
    rw [show -x-1= -(x+1) by omega, show -x+1= -(x-1) by omega, ih, ih]
    exact Bool.xor_comm _ _

private theorem wave_center (n : Nat) : wave (n+1) 0=false := by
  change xor (wave n (-1)) (wave n 1) = false
  rw [wave_reflect n 1]; simp

private theorem central_fringe (n : Nat) :
    fringe n 0 = xor (wave n 0) (wave n (-1)) := by
  unfold fringe
  have h : ¬(0=(n:Int)+1) := by omega
  simp [h]

private theorem fringe_even (d : Nat) (hd : 0<d) : fringe (2*d) 0=false := by
  rw [central_fringe]
  have ha : wave (2*d) 0 = wave d 0 := (wave_double d 0).1
  have hb : wave (2*d) (-1) = false := by
    have z := (wave_double d (-1)).2
    rwa [show (2*(-1)+1:Int) = -1 by decide] at z
  rw [ha,hb]
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hd)
  simp [wave_center]

private theorem fringe_odd (d : Nat) : fringe (2*d+1) 0 = fringe d 0 := by
  rw [central_fringe,central_fringe,wave_center]
  change xor false (xor (wave (2*d) (-2)) (wave (2*d) 0)) = _
  have ha : wave (2*d) (-2) = wave d (-1) := by
    have z := (wave_double d (-1)).1
    rwa [show (2*(-1):Int) = -2 by decide] at z
  have hb : wave (2*d) 0 = wave d 0 := (wave_double d 0).1
  rw [ha,hb,Bool.false_xor,Bool.xor_comm]

private theorem strip_ones (m k : Nat) (hm : 0<m) :
    fringe (m*2^k-1) 0 = fringe (m-1) 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0<m*2^k := Nat.mul_pos hm (Nat.pow_pos (by decide))
    rw [Nat.pow_succ, ← Nat.mul_assoc, show m*2^k*2-1=2*(m*2^k-1)+1 by omega,
      fringe_odd, ih]

/-- The Laurent fringe is precisely the Mersenne spike train (including age
zero). In particular it flips between 2^k−1 and any nontrivial odd multiple
of 2^k minus one. -/
theorem L2 (k d : Nat) (hd : 0 < d) :
    fringe (2^k - 1) 0 = true ∧ fringe ((2*d+1) * 2^k - 1) 0 = false := by
  constructor
  · have z : fringe 0 0 = true := rfl
    simpa [z] using strip_ones 1 k (by decide)
  · rw [strip_ones (2*d+1) k (by omega), show 2*d+1-1=2*d by omega]
    exact fringe_even d hd

private theorem repeat_add {f : Nat → Bool} {T P : Nat}
    (h : ∀ t, T ≤ t → f (t+P)=f t) (t : Nat) (ht : T≤t) (m : Nat) :
    f (t + P*m) = f t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, h (t+P*m) (by omega), ih]

theorem close_step4 (hcenter : EventuallyPeriodic center) : False := by
  obtain ⟨T,P,hP,period⟩ := hcenter
  obtain ⟨k,j,hj,ht,he⟩ := L1 P T hP
  have hpow : 0 < 2^k := Nat.pow_pos (by decide)
  have hd : 0 < P*j := Nat.mul_pos hP hj
  obtain ⟨h₁,h₂⟩ := L2 k (P*j) hd
  have halg : (2*(P*j)+1)*2^k = P*((2*j)*2^k) + 2^k := by
    rw [Nat.add_mul, Nat.one_mul]
    congr 1
    ac_rfl
  have hindex : (2^k - 1) + P*((2*j)*2^k) = (2*(P*j)+1)*2^k - 1 := by
    rw [halg]; omega
  have htime := repeat_add period (2^k-1) (by omega) ((2*j)*2^k)
  rw [hindex] at htime
  unfold center at htime
  rw [row_split _ 0, row_split (2^k-1) 0, h₁, h₂, ← he] at htime
  cases hh : interior (2^k-1) 0 <;> simp [hh] at htime

end OpenProblem.BoundsBlueprint
