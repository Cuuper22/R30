import Statement
import FixedColumnPair
import MaskedRightRigidity

-- Research draft. This is outside the audit target until the Step 4 hole is closed.
namespace OpenProblem

theorem answer : Claim := by
  intro hcenter
  have nonconstant (b : Bool) : ¬ ∃ T, ∀ t ≥ T, center t = b := by
    rintro ⟨T, h⟩
    cases b
    · -- On a white-center tail, R can rise from 0 to 1 but cannot fall.
      have latch (t : Nat) (ht : T ≤ t) (rise : cell t 1 = true) :
          cell (t+1) 1 = true := by
        have c : cell t 0 = false := h t ht
        rw [cell]
        change rule (cell t 0) (cell t 1) (cell t 2) = true
        simp [c, rise, rule]
      have rightPeriod : EventuallyPeriodic (fun t => cell t 1) := by
        by_cases hit : ∃ s ≥ T, cell s 1 = true
        · obtain ⟨s, hs, one⟩ := hit
          have keep (n : Nat) : cell (s+n) 1 = true := by
            induction n with
            | zero => simpa using one
            | succ n ih => exact latch (s+n) (by omega) ih
          exact ⟨s, 1, by decide, fun t ht => by
            have a := keep (t-s)
            have b := keep (t+1-s)
            rw [show s+(t-s)=t by omega] at a
            rw [show s+(t+1-s)=t+1 by omega] at b
            exact b.trans a.symm
          ⟩
        · have zero (s : Nat) (hs : T ≤ s) : cell s 1 = false := by
            cases e : cell s 1
            · rfl
            · exact False.elim (hit ⟨s, hs, e⟩)
          exact ⟨T, 1, by decide, fun t ht => by
            change cell (t+1) 1 = cell t 1
            rw [zero _ (by omega), zero _ ht]⟩
      exact FixedColumnPair.at_most_one 0 1 (by decide) hcenter rightPeriod
    · -- On a black-center tail, the left bit must be zero at every tick.
      have leftZero (t : Nat) (ht : T ≤ t) : cell t (-1) = false := by
        have c : cell t 0 = true := h t ht
        have n : cell (t+1) 0 = true := h (t+1) (by omega)
        rw [cell] at n
        change rule (cell t (-1)) (cell t 0) (cell t 1) = true at n
        cases e : cell t (-1) <;> simp_all [rule]
      have leftPeriod : EventuallyPeriodic (fun t => cell t (-1)) :=
        ⟨T, 1, by decide, fun t ht => by
          change cell (t+1) (-1) = cell t (-1)
          rw [leftZero _ (by omega), leftZero _ ht]⟩
      exact FixedColumnPair.at_most_one (-1) 0 (by decide) leftPeriod hcenter
  have step4_mixed_right_filter : EventuallyPeriodic MaskedRightRigidity.maskedRight := by
    -- Given the genuine singleton orbit, a periodic center and both bits
    -- recurring, force the white-tick R readout to have a common return.
    -- This is the single unresolved mathematical subgoal.
    sorry
  exact MaskedRightRigidity.claim_of_periodic_mask step4_mixed_right_filter hcenter

end OpenProblem
