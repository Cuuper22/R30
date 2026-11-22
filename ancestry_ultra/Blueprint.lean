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

private theorem agree_weaken {a b : Trace} {m n : Nat} (h : agree a b n) (hm : m ≤ n) :
    agree a b m := fun i hi => h i (by omega)

theorem east_prefix {a b : Trace} (t j : Nat) (h : agree a b t) :
    east a t (j+1) = east b t (j+1) := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    have h' := agree_weaken h (Nat.le_succ t)
    change rule (east a t j) (east a t (j+1)) (east a t (j+2)) =
      rule (east b t j) (east b t (j+1)) (east b t (j+2))
    rw [ih j h',ih (j+1) h']
    congr 1
    cases j with
    | zero =>
      cases t with
      | zero => exact h 0 (by omega)
      | succ t => exact h (t+1) (by omega)
    | succ j => exact ih j h'

private theorem bx0 {a b : Bool} (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem bxCancel (x y k : Bool) : xor (xor x k) (xor y k) = xor x y := by
  cases x <;> cases y <;> cases k <;> rfl

/-- The extreme wall coefficient occurs precisely once in every sideways diagonal.
The entire nonlinear correction depends strictly on earlier wall letters. -/
theorem diagonal {a b : Trace} (d t : Nat) (h : agree a b (t+d)) :
    xor ((pair a d).1 t) ((pair b d).1 t) = xor (a (t+d)) (b (t+d)) ∧
    (pair a d).2 t = (pair b d).2 t := by
  induction d generalizing t with
  | zero =>
    exact ⟨rfl,east_prefix t 0 h⟩
  | succ d ih =>
    have hd := ih t (agree_weaken h (by omega))
    have mid : (pair a d).1 t = (pair b d).1 t := by
      apply bx0
      rw [hd.1,h (t+d) (by omega)]
      simp
    have hh := ih (t+1) (agree_weaken h (by omega))
    refine ⟨?_,mid⟩
    change xor (xor ((pair a d).1 (t+1)) ((pair a d).1 t || (pair a d).2 t))
      (xor ((pair b d).1 (t+1)) ((pair b d).1 t || (pair b d).2 t)) = _
    rw [mid,hd.2,bxCancel,hh.1,show t+1+d=t+(d+1) by omega]

theorem origin_diagonal {a b : Trace} (n : Nat) (h : agree a b n) :
    xor (origin a n) (origin b n) = xor (a n) (b n) := by
  simpa [origin] using (diagonal n 0 (a:=a) (b:=b) (by simpa using h)).1

theorem east_outside (c : Trace) (t j : Nat) (ht : t < j) : east c t j = false := by
  induction t generalizing j with
  | zero => cases j <;> simp_all [east]
  | succ t ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    change rule (east c t k) (east c t (k+1)) (east c t (k+2)) = false
    rw [ih k (by omega),ih (k+1) (by omega),ih (k+2) (by omega)]
    rfl

theorem east_mark (c : Trace) (hc : c 0 = true) (t : Nat) : east c t t = true := by
  induction t with
  | zero => exact hc
  | succ t ih =>
    change rule (east c t t) (east c t (t+1)) (east c t (t+2)) = true
    rw [ih,east_outside _ _ _ (by omega),east_outside _ _ _ (by omega)]
    rfl

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

theorem west_outside_actual (t : Nat) (x : Int) (hx : x < -(t:Int)) :
    cell t x = false := by
  induction t generalizing x with
  | zero => exact decide_eq_false (by omega)
  | succ t ih =>
    rw [cell,ih (x-1) (by omega),ih x (by omega),ih (x+1) (by omega)]
    rfl

theorem west_mark_actual (t : Nat) : cell t (-(t:Int)) = true := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [cell,west_outside_actual t _ (by omega),west_outside_actual t _ (by omega),
        show -(↑(t+1):Int)+1 = -(t:Int) by omega, ih]
    rfl

/-- Exact finite-cylinder conjugacy: agreement up to n is equivalent to recovering
the singleton's west seed through depth n-1. No recurrence assumption. -/
theorem finite_seed_iff (c : Trace) (hm : c 0 = true) (n : Nat) :
    (∀ d, 0 < d → d < n → origin c d = false) ↔ agree c center n := by
  constructor
  · intro seed
    have get (d : Nat) (hd : d < n) : c d = center d := by
      induction d using Nat.strongRecOn with
      | ind d ih =>
        by_cases zero : d=0
        · subst d; exact hm
        · have e := origin_diagonal d (a:=c) (b:=center) (fun j hj => ih j hj (by omega))
          rw [seed d (by omega) hd,actual_origin d (by omega)] at e
          exact bx0 e.symm
    exact get
  · intro h d hd hn
    have e := origin_diagonal d (a:=c) (b:=center) (agree_weaken h (by omega))
    rw [h d hn,actual_origin d hd] at e
    simpa using e

/-- Both entire marked light cones, expressed in the same two coordinates used
by the finite test. The west statement is an output of sideways decoding, not
a replacement initialization assumption. -/
theorem actual_rims (t : Nat) :
    (pair center t).1 t = true ∧ east center t t = true ∧
    ∀ j, t < j → (pair center j).1 t = false ∧ east center t j = false := by
  refine ⟨(pair_actual t t).1.trans (west_mark_actual t),east_mark _ rfl t,?_⟩
  intro j hj
  exact ⟨(pair_actual j t).1.trans (west_outside_actual _ _ (by omega)),
    east_outside _ _ _ hj⟩

theorem repeat_eq {c : Trace} {T P : Nat} (_hp : 0 < P)
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
