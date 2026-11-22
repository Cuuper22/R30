import Statement
import FixedColumnPair
import MaskedRightRigidity

-- Research draft. This is outside the audit target until the Step 4 hole is closed.
namespace OpenProblem

-- Six eastern cells and the mixed macro clocks A=01100000001, B=10000001.
-- Each transition quantifies over both possible fresh eastern bits. The finite
-- certificates below are reduced by the kernel. No statement assumes a lock.
private abbrev abBit (m : Nat) (a b c d e f : Bool) : Bool :=
  m.testBit (a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat + 16*e.toNat + 32*f.toNat)
private def abIn (m t : Nat) : Prop := abBit m (cell t 1) (cell t 2) (cell t 3)
  (cell t 4) (cell t 5) (cell t 6) = true
private abbrev abCheck (m n : Nat) (v : Bool) (tag : Option Bool) : Prop :=
  ∀ a b c d e f g : Bool, abBit m a b c d e f = true →
  abBit n (rule v a b) (rule a b c) (rule b c d) (rule c d e) (rule d e f) (rule e f g) = true ∧
  (tag = none ∨ tag = some (a && !v))
private theorem abTick {m n t : Nat} {v : Bool} {tag : Option Bool}
    (ok : abCheck m n v tag) (hin : abIn m t) (hc : center t = v) :
    abIn n (t+1) ∧ (tag = none ∨ tag = some (MaskedRightRigidity.maskedRight t)) := by
  subst v
  exact ok _ _ _ _ _ _ (cell t 7) hin
private theorem abAll (t : Nat) : abIn 0xffffffffffffffff t := by
  have yes : ∀ a b c d e f : Bool, abBit 0xffffffffffffffff a b c d e f = true := by decide
  exact yes _ _ _ _ _ _
private def abPredict (t : Nat) : Bool :=
  !center t && !(center (t-1) && (center (t+1) || !center (t+6)))

private def abA (t : Nat) : Prop :=
  center (t+0) = false ∧ center (t+1) = true ∧ center (t+2) = true ∧ center (t+3) = false ∧ center (t+4) = false ∧ center (t+5) = false ∧ center (t+6) = false ∧ center (t+7) = false ∧ center (t+8) = false ∧ center (t+9) = false ∧ center (t+10) = true ∧ True

private def abB (t : Nat) : Prop :=
  center (t+0) = true ∧ center (t+1) = false ∧ center (t+2) = false ∧ center (t+3) = false ∧ center (t+4) = false ∧ center (t+5) = false ∧ center (t+6) = false ∧ center (t+7) = true ∧ True

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab0A (t : Nat) (h : abA t) (m0 : abIn 0xffffffffffffffff t) :
    abIn 0x1014111510101115 (t+11) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,_⟩ := h
  have e0 := abTick (m := 0xffffffffffffffff) (n := 0xfbebfaebbb6afaeb) (t := t+0) (tag := none) (by decide) m0 c0
  have m1 : abIn 0xfbebfaebbb6afaeb (t+1) := e0.1
  have e1 := abTick (m := 0xfbebfaebbb6afaeb) (n := 0x5597759757957597) (t := t+1) (tag := none) (by decide) m1 c1
  have m2 : abIn 0x5597759757957597 (t+2) := e1.1
  have e2 := abTick (m := 0x5597759757957597) (n := 0xe7d7e5d66695e5c6) (t := t+2) (tag := none) (by decide) m2 c2
  have m3 : abIn 0xe7d7e5d66695e5c6 (t+3) := e2.1
  have e3 := abTick (m := 0xe7d7e5d66695e5c6) (n := 0xdbea9aaa996a9aaa) (t := t+3) (tag := none) (by decide) m3 c3
  have m4 : abIn 0xdbea9aaa996a9aaa (t+4) := e3.1
  have e4 := abTick (m := 0xdbea9aaa996a9aaa) (n := 0xaa6ab26aaa6ab26a) (t := t+4) (tag := none) (by decide) m4 c4
  have m5 : abIn 0xaa6ab26aaa6ab26a (t+5) := e4.1
  have e5 := abTick (m := 0xaa6ab26aaa6ab26a) (n := 0xa86aaa6aa86aaa2a) (t := t+5) (tag := none) (by decide) m5 c5
  have m6 : abIn 0xa86aaa6aa86aaa2a (t+6) := e5.1
  have e6 := abTick (m := 0xa86aaa6aa86aaa2a) (n := 0xaa2aa22aaa2a222a) (t := t+6) (tag := none) (by decide) m6 c6
  have m7 : abIn 0xaa2aa22aaa2a222a (t+7) := e6.1
  have e7 := abTick (m := 0xaa2aa22aaa2a222a) (n := 0xa828a22aa820a22a) (t := t+7) (tag := none) (by decide) m7 c7
  have m8 : abIn 0xa828a22aa820a22a (t+8) := e7.1
  have e8 := abTick (m := 0xa828a22aa820a22a) (n := 0xa02aa22aa022222a) (t := t+8) (tag := none) (by decide) m8 c8
  have m9 : abIn 0xa02aa22aa022222a (t+9) := e8.1
  have e9 := abTick (m := 0xa02aa22aa022222a) (n := 0xa828a02aa820202a) (t := t+9) (tag := none) (by decide) m9 c9
  have m10 : abIn 0xa828a02aa820202a (t+10) := e9.1
  have e10 := abTick (m := 0xa828a02aa820202a) (n := 0x1014111510101115) (t := t+10) (tag := none) (by decide) m10 c10
  have m11 : abIn 0x1014111510101115 (t+11) := e10.1
  exact m11

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab1B (t : Nat) (h : abB t) (m0 : abIn 0x1014111510101115 t) :
    abIn 0x5014501550101015 (t+8) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,_⟩ := h
  have e0 := abTick (m := 0x1014111510101115) (n := 0xa0c2a0c2608080c2) (t := t+0) (tag := none) (by decide) m0 c0
  have m1 : abIn 0xa0c2a0c2608080c2 (t+1) := e0.1
  have e1 := abTick (m := 0xa0c2a0c2608080c2) (n := 0xa0a0a2a080a0a2a) (t := t+1) (tag := none) (by decide) m1 c1
  have m2 : abIn 0xa0a0a2a080a0a2a (t+2) := e1.1
  have e2 := abTick (m := 0xa0a0a2a080a0a2a) (n := 0xaa28a228aa00a228) (t := t+2) (tag := none) (by decide) m2 c2
  have m3 : abIn 0xaa28a228aa00a228 (t+3) := e2.1
  have e3 := abTick (m := 0xaa28a228aa00a228) (n := 0xa022a222a022a222) (t := t+3) (tag := none) (by decide) m3 c3
  have m4 : abIn 0xa022a222a022a222 (t+4) := e3.1
  have e4 := abTick (m := 0xa022a222a022a222) (n := 0xa82aa02a8822202a) (t := t+4) (tag := none) (by decide) m4 c4
  have m5 : abIn 0xa82aa02a8822202a (t+5) := e4.1
  have e5 := abTick (m := 0xa82aa02a8822202a) (n := 0x2828222a2820222a) (t := t+5) (tag := none) (by decide) m5 c5
  have m6 : abIn 0x2828222a2820222a (t+6) := e5.1
  have e6 := abTick (m := 0x2828222a2820222a) (n := 0xa028a228a0202228) (t := t+6) (tag := none) (by decide) m6 c6
  have m7 : abIn 0xa028a228a0202228 (t+7) := e6.1
  have e7 := abTick (m := 0xa028a228a0202228) (n := 0x5014501550101015) (t := t+7) (tag := none) (by decide) m7 c7
  have m8 : abIn 0x5014501550101015 (t+8) := e7.1
  exact m8

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab2B (t : Nat) (h : abB t) (m0 : abIn 0x5014501550101015 t) :
    abIn 0x5014501550101015 (t+8) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,_⟩ := h
  have e0 := abTick (m := 0x5014501550101015) (n := 0x80c280c6408080c6) (t := t+0) (tag := none) (by decide) m0 c0
  have m1 : abIn 0x80c280c6408080c6 (t+1) := e0.1
  have e1 := abTick (m := 0x80c280c6408080c6) (n := 0xa8a0a8a080a0a8a) (t := t+1) (tag := none) (by decide) m1 c1
  have m2 : abIn 0xa8a0a8a080a0a8a (t+2) := e1.1
  have e2 := abTick (m := 0xa8a0a8a080a0a8a) (n := 0xaa288228aa028228) (t := t+2) (tag := none) (by decide) m2 c2
  have m3 : abIn 0xaa288228aa028228 (t+3) := e2.1
  have e3 := abTick (m := 0xaa288228aa028228) (n := 0xa822a222a822a222) (t := t+3) (tag := none) (by decide) m3 c3
  have m4 : abIn 0xa822a222a822a222 (t+4) := e3.1
  have e4 := abTick (m := 0xa822a222a822a222) (n := 0xa82aa22a8822222a) (t := t+4) (tag := none) (by decide) m4 c4
  have m5 : abIn 0xa82aa22a8822222a (t+5) := e4.1
  have e5 := abTick (m := 0xa82aa22a8822222a) (n := 0xa828a22aa820222a) (t := t+5) (tag := none) (by decide) m5 c5
  have m6 : abIn 0xa828a22aa820222a (t+6) := e5.1
  have e6 := abTick (m := 0xa828a22aa820222a) (n := 0xa028a22aa020222a) (t := t+6) (tag := none) (by decide) m6 c6
  have m7 : abIn 0xa028a22aa020222a (t+7) := e6.1
  have e7 := abTick (m := 0xa028a22aa020222a) (n := 0x5014501550101015) (t := t+7) (tag := none) (by decide) m7 c7
  have m8 : abIn 0x5014501550101015 (t+8) := e7.1
  exact m8

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab2A (t : Nat) (h : abA t) (m0 : abIn 0x5014501550101015 t) :
    abIn 0x1010101110101011 (t+11) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,_⟩ := h
  have e0 := abTick (m := 0x5014501550101015) (n := 0x40c140c9804040c9) (t := t+0) (tag := none) (by decide) m0 c0
  have m1 : abIn 0x40c140c9804040c9 (t+1) := e0.1
  have e1 := abTick (m := 0x40c140c9804040c9) (n := 0x516051702050517) (t := t+1) (tag := none) (by decide) m1 c1
  have m2 : abIn 0x516051702050517 (t+2) := e1.1
  have e2 := abTick (m := 0x516051702050517) (n := 0xe646e4466680e446) (t := t+2) (tag := none) (by decide) m2 c2
  have m3 : abIn 0xe646e4466680e446 (t+3) := e2.1
  have e3 := abTick (m := 0xe646e4466680e446) (n := 0x8aa88aa882a88aa) (t := t+3) (tag := none) (by decide) m3 c3
  have m4 : abIn 0x8aa88aa882a88aa (t+4) := e3.1
  have e4 := abTick (m := 0x8aa88aa882a88aa) (n := 0x2a2a222a2a22222a) (t := t+4) (tag := none) (by decide) m4 c4
  have m5 : abIn 0x2a2a222a2a22222a (t+5) := e4.1
  have e5 := abTick (m := 0x2a2a222a2a22222a) (n := 0xa828a228a820a228) (t := t+5) (tag := none) (by decide) m5 c5
  have m6 : abIn 0xa828a228a820a228 (t+6) := e5.1
  have e6 := abTick (m := 0xa828a228a820a228) (n := 0xa022a222a0222222) (t := t+6) (tag := none) (by decide) m6 c6
  have m7 : abIn 0xa022a222a0222222 (t+7) := e6.1
  have e7 := abTick (m := 0xa022a222a0222222) (n := 0xa828a02a8820202a) (t := t+7) (tag := none) (by decide) m7 c7
  have m8 : abIn 0xa828a02a8820202a (t+8) := e7.1
  have e8 := abTick (m := 0xa828a02a8820202a) (n := 0x2028222a2020222a) (t := t+8) (tag := none) (by decide) m8 c8
  have m9 : abIn 0x2028222a2020222a (t+9) := e8.1
  have e9 := abTick (m := 0x2028222a2020222a) (n := 0xa028a028a0202028) (t := t+9) (tag := none) (by decide) m9 c9
  have m10 : abIn 0xa028a028a0202028 (t+10) := e9.1
  have e10 := abTick (m := 0xa028a028a0202028) (n := 0x1010101110101011) (t := t+10) (tag := none) (by decide) m10 c10
  have m11 : abIn 0x1010101110101011 (t+11) := e10.1
  exact m11

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3A (t : Nat) (h : abA t) (m0 : abIn 0x1010101110101011 t) (hp : 0 < t) (prev : center (t-1) = true) :
    abIn 0x1010101110101011 (t+11) ∧ (∀ i, i < 11 → MaskedRightRigidity.maskedRight (t+i) = abPredict (t+i)) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,_⟩ := h
  have e0 := abTick (m := 0x1010101110101011) (n := 0x4041404100404041) (t := t+0) (tag := (some false)) (by decide) m0 c0
  have m1 : abIn 0x4041404100404041 (t+1) := e0.1
  have q0 : MaskedRightRigidity.maskedRight (t+0) = false := (Option.some.inj (e0.2.resolve_left (by intro h; cases h))).symm
  have e1 := abTick (m := 0x4041404100404041) (n := 0x406040602040406) (t := t+1) (tag := (some false)) (by decide) m1 c1
  have m2 : abIn 0x406040602040406 (t+2) := e1.1
  have q1 : MaskedRightRigidity.maskedRight (t+1) = false := (Option.some.inj (e1.2.resolve_left (by intro h; cases h))).symm
  have e2 := abTick (m := 0x406040602040406) (n := 0x4444444444004444) (t := t+2) (tag := (some false)) (by decide) m2 c2
  have m3 : abIn 0x4444444444004444 (t+3) := e2.1
  have q2 : MaskedRightRigidity.maskedRight (t+2) = false := (Option.some.inj (e2.2.resolve_left (by intro h; cases h))).symm
  have e3 := abTick (m := 0x4444444444004444) (n := 0x888088888080888) (t := t+3) (tag := (some false)) (by decide) m3 c3
  have m4 : abIn 0x888088888080888 (t+4) := e3.1
  have q3 : MaskedRightRigidity.maskedRight (t+3) = false := (Option.some.inj (e3.2.resolve_left (by intro h; cases h))).symm
  have e4 := abTick (m := 0x888088888080888) (n := 0x2220022222020222) (t := t+4) (tag := (some true)) (by decide) m4 c4
  have m5 : abIn 0x2220022222020222 (t+5) := e4.1
  have q4 : MaskedRightRigidity.maskedRight (t+4) = true := (Option.some.inj (e4.2.resolve_left (by intro h; cases h))).symm
  have e5 := abTick (m := 0x2220022222020222) (n := 0xa808a0288820a028) (t := t+5) (tag := (some true)) (by decide) m5 c5
  have m6 : abIn 0xa808a0288820a028 (t+6) := e5.1
  have q5 : MaskedRightRigidity.maskedRight (t+5) = true := (Option.some.inj (e5.2.resolve_left (by intro h; cases h))).symm
  have e6 := abTick (m := 0xa808a0288820a028) (n := 0x2022222220222222) (t := t+6) (tag := (some true)) (by decide) m6 c6
  have m7 : abIn 0x2022222220222222 (t+7) := e6.1
  have q6 : MaskedRightRigidity.maskedRight (t+6) = true := (Option.some.inj (e6.2.resolve_left (by intro h; cases h))).symm
  have e7 := abTick (m := 0x2022222220222222) (n := 0xa828a02888202028) (t := t+7) (tag := (some true)) (by decide) m7 c7
  have m8 : abIn 0xa828a02888202028 (t+8) := e7.1
  have q7 : MaskedRightRigidity.maskedRight (t+7) = true := (Option.some.inj (e7.2.resolve_left (by intro h; cases h))).symm
  have e8 := abTick (m := 0xa828a02888202028) (n := 0x2020222220202222) (t := t+8) (tag := (some true)) (by decide) m8 c8
  have m9 : abIn 0x2020222220202222 (t+9) := e8.1
  have q8 : MaskedRightRigidity.maskedRight (t+8) = true := (Option.some.inj (e8.2.resolve_left (by intro h; cases h))).symm
  have e9 := abTick (m := 0x2020222220202222) (n := 0xa028a02880202028) (t := t+9) (tag := (some true)) (by decide) m9 c9
  have m10 : abIn 0xa028a02880202028 (t+10) := e9.1
  have q9 : MaskedRightRigidity.maskedRight (t+9) = true := (Option.some.inj (e9.2.resolve_left (by intro h; cases h))).symm
  have e10 := abTick (m := 0xa028a02880202028) (n := 0x1010101110101011) (t := t+10) (tag := (some false)) (by decide) m10 c10
  have m11 : abIn 0x1010101110101011 (t+11) := e10.1
  have q10 : MaskedRightRigidity.maskedRight (t+10) = false := (Option.some.inj (e10.2.resolve_left (by intro h; cases h))).symm
  refine ⟨m11, ?_⟩
  intro i hi
  have e : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [q0]; simp at c0; simp [show t+0+1 = t+1 by omega, show t+0+6 = t+6 by omega, abPredict, q0, c0, Nat.add_zero, prev, c1, c6]
  · rw [q1]; simp at c0; simp [show t+1-1 = t+0 by omega, show t+1+1 = t+2 by omega, show t+1+6 = t+7 by omega, abPredict, q1, c1, c0, c2, c7]
  · rw [q2]; simp at c0; simp [show t+2-1 = t+1 by omega, show t+2+1 = t+3 by omega, show t+2+6 = t+8 by omega, abPredict, q2, c2, c1, c3, c8]
  · rw [q3]; simp at c0; simp [show t+3-1 = t+2 by omega, show t+3+1 = t+4 by omega, show t+3+6 = t+9 by omega, abPredict, q3, c3, c2, c4, c9]
  · rw [q4]; simp at c0; simp [show t+4-1 = t+3 by omega, show t+4+1 = t+5 by omega, show t+4+6 = t+10 by omega, abPredict, q4, c4, c3, c5, c10]
  · rw [q5]; simp at c0; simp [show t+5-1 = t+4 by omega, show t+5+1 = t+6 by omega, abPredict, q5, c5, c4, c6]
  · rw [q6]; simp at c0; simp [show t+6-1 = t+5 by omega, show t+6+1 = t+7 by omega, abPredict, q6, c6, c5, c7]
  · rw [q7]; simp at c0; simp [show t+7-1 = t+6 by omega, show t+7+1 = t+8 by omega, abPredict, q7, c7, c6, c8]
  · rw [q8]; simp at c0; simp [show t+8-1 = t+7 by omega, show t+8+1 = t+9 by omega, abPredict, q8, c8, c7, c9]
  · rw [q9]; simp at c0; simp [show t+9-1 = t+8 by omega, show t+9+1 = t+10 by omega, abPredict, q9, c9, c8, c10]
  · rw [q10]; simp at c0; simp [show t+10-1 = t+9 by omega, abPredict, q10, c10, c9]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem ab3B (t : Nat) (h : abB t) (m0 : abIn 0x1010101110101011 t) (hp : 0 < t) (prev : center (t-1) = true) :
    abIn 0x1010101110101011 (t+8) ∧ (∀ i, i < 8 → MaskedRightRigidity.maskedRight (t+i) = abPredict (t+i)) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,_⟩ := h
  have e0 := abTick (m := 0x1010101110101011) (n := 0x8082808200808082) (t := t+0) (tag := (some false)) (by decide) m0 c0
  have m1 : abIn 0x8082808200808082 (t+1) := e0.1
  have q0 : MaskedRightRigidity.maskedRight (t+0) = false := (Option.some.inj (e0.2.resolve_left (by intro h; cases h))).symm
  have e1 := abTick (m := 0x8082808200808082) (n := 0x20a020a0802020a) (t := t+1) (tag := (some true)) (by decide) m1 c1
  have m2 : abIn 0x20a020a0802020a (t+2) := e1.1
  have q1 : MaskedRightRigidity.maskedRight (t+1) = true := (Option.some.inj (e1.2.resolve_left (by intro h; cases h))).symm
  have e2 := abTick (m := 0x20a020a0802020a) (n := 0x88288228a8008228) (t := t+2) (tag := (some true)) (by decide) m2 c2
  have m3 : abIn 0x88288228a8008228 (t+3) := e2.1
  have q2 : MaskedRightRigidity.maskedRight (t+2) = true := (Option.some.inj (e2.2.resolve_left (by intro h; cases h))).symm
  have e3 := abTick (m := 0x88288228a8008228) (n := 0xa022a222a0222222) (t := t+3) (tag := (some true)) (by decide) m3 c3
  have m4 : abIn 0xa022a222a0222222 (t+4) := e3.1
  have q3 : MaskedRightRigidity.maskedRight (t+3) = true := (Option.some.inj (e3.2.resolve_left (by intro h; cases h))).symm
  have e4 := abTick (m := 0xa022a222a0222222) (n := 0xa828a02a8820202a) (t := t+4) (tag := (some true)) (by decide) m4 c4
  have m5 : abIn 0xa828a02a8820202a (t+5) := e4.1
  have q4 : MaskedRightRigidity.maskedRight (t+4) = true := (Option.some.inj (e4.2.resolve_left (by intro h; cases h))).symm
  have e5 := abTick (m := 0xa828a02a8820202a) (n := 0x2028222a2020222a) (t := t+5) (tag := (some true)) (by decide) m5 c5
  have m6 : abIn 0x2028222a2020222a (t+6) := e5.1
  have q5 : MaskedRightRigidity.maskedRight (t+5) = true := (Option.some.inj (e5.2.resolve_left (by intro h; cases h))).symm
  have e6 := abTick (m := 0x2028222a2020222a) (n := 0xa028a028a0202028) (t := t+6) (tag := (some true)) (by decide) m6 c6
  have m7 : abIn 0xa028a028a0202028 (t+7) := e6.1
  have q6 : MaskedRightRigidity.maskedRight (t+6) = true := (Option.some.inj (e6.2.resolve_left (by intro h; cases h))).symm
  have e7 := abTick (m := 0xa028a028a0202028) (n := 0x1010101110101011) (t := t+7) (tag := (some false)) (by decide) m7 c7
  have m8 : abIn 0x1010101110101011 (t+8) := e7.1
  have q7 : MaskedRightRigidity.maskedRight (t+7) = false := (Option.some.inj (e7.2.resolve_left (by intro h; cases h))).symm
  refine ⟨m8, ?_⟩
  intro i hi
  have e : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [q0]; simp at c0; simp [show t+0+1 = t+1 by omega, show t+0+6 = t+6 by omega, abPredict, q0, c0, Nat.add_zero, prev, c1, c6]
  · rw [q1]; simp at c0; simp [show t+1-1 = t+0 by omega, show t+1+1 = t+2 by omega, show t+1+6 = t+7 by omega, abPredict, q1, c1, c0, c2, c7]
  · rw [q2]; simp at c0; simp [show t+2-1 = t+1 by omega, show t+2+1 = t+3 by omega, abPredict, q2, c2, c1, c3]
  · rw [q3]; simp at c0; simp [show t+3-1 = t+2 by omega, show t+3+1 = t+4 by omega, abPredict, q3, c3, c2, c4]
  · rw [q4]; simp at c0; simp [show t+4-1 = t+3 by omega, show t+4+1 = t+5 by omega, abPredict, q4, c4, c3, c5]
  · rw [q5]; simp at c0; simp [show t+5-1 = t+4 by omega, show t+5+1 = t+6 by omega, abPredict, q5, c5, c4, c6]
  · rw [q6]; simp at c0; simp [show t+6-1 = t+5 by omega, show t+6+1 = t+7 by omega, abPredict, q6, c6, c5, c7]
  · rw [q7]; simp at c0; simp [show t+7-1 = t+6 by omega, abPredict, q7, c7, c6]

-- A B followed by any number of further B's, then A, resets the entire
-- six-cell input. The suffix may use A and B in an arbitrary order.
private def abMosaic : Prop := ∃ (u m : Nat) (cut : Nat → Nat) (kind : Nat → Bool),
  abA u ∧ abB (u+11) ∧ (∀ j, j < m → abB (u+19+8*j)) ∧ abA (u+19+8*m) ∧
  cut 0 = u+30+8*m ∧ (∀ j, if kind j then
    (abB (cut j) ∧ cut (j+1) = cut j+8) else (abA (cut j) ∧ cut (j+1) = cut j+11))
private theorem abMaskPeriod (hc : EventuallyPeriodic center) (hm : abMosaic) :
    EventuallyPeriodic MaskedRightRigidity.maskedRight := by
  obtain ⟨u,m,cut,K,ha,hb,rep,last,start,tiles⟩ := hm
  have h1 := ab0A u ha (abAll u)
  have h2 := ab1B (u+11) hb h1
  have mid : ∀ j, j ≤ m → abIn 0x5014501550101015 (u+19+8*j) := by
    intro j; induction j with
    | zero => intro _; simpa using h2
    | succ j ih =>
      intro hj
      have h := ab2B (u+19+8*j) (rep j (by omega)) (ih (by omega))
      rw [show u+19+8*(j+1) = u+19+8*j+8 by omega]; exact h
  have st := ab2A _ last (mid m (Nat.le_refl _))
  have endA (n : Nat) (a : abA n) : center (n+10) = true := a.2.2.2.2.2.2.2.2.2.2.1
  have endB (n : Nat) (a : abB n) : center (n+7) = true := a.2.2.2.2.2.2.2.1
  have inv (j : Nat) : abIn 0x1010101110101011 (cut j) ∧ 0 < cut j ∧ center (cut j-1) = true := by
    induction j with
    | zero =>
      rw [start]
      have e := endA _ last
      refine ⟨?_, by omega, ?_⟩
      · rw [show u+30+8*m = u+19+8*m+11 by omega]; exact st
      · rw [show u+30+8*m-1 = u+19+8*m+10 by omega]; exact e
    | succ j ih =>
      have h := tiles j
      cases eq : K j <;> simp [eq] at h
      · rw [h.2]
        exact ⟨(ab3A _ h.1 ih.1 ih.2.1 ih.2.2).1, by omega, by simpa using endA _ h.1⟩
      · rw [h.2]
        exact ⟨(ab3B _ h.1 ih.1 ih.2.1 ih.2.2).1, by omega, by simpa using endB _ h.1⟩
  let width := fun j => if K j then 8 else 11
  have span (j : Nat) : cut (j+1) = cut j+width j := by
    have h := tiles j
    cases e : K j <;> simp [e,width] at h ⊢ <;> exact h.2
  have pos (j : Nat) : 0 < width j := by dsimp [width]; split <;> decide
  have cover (n : Nat) : ∃ j i, i < width j ∧ cut j+i = cut 0+n := by
    induction n with
    | zero => exact ⟨0,0,pos 0,rfl⟩
    | succ n ih =>
      obtain ⟨j,i,hi,eq⟩ := ih
      by_cases short : i+1 < width j
      · exact ⟨j,i+1,short,by omega⟩
      · exact ⟨j+1,0,pos _,by have e := span j; omega⟩
  have localRule (n : Nat) (hn : cut 0 ≤ n) : MaskedRightRigidity.maskedRight n = abPredict n := by
    obtain ⟨j,i,hi,atN⟩ := cover (n-cut 0)
    have e : cut j+i = n := by omega
    rw [← e]
    have h := tiles j; have v := inv j
    cases eq : K j <;> simp [width,eq] at hi h
    · exact (ab3A _ h.1 v.1 v.2.1 v.2.2).2 i hi
    · exact (ab3B _ h.1 v.1 v.2.1 v.2.2).2 i hi
  obtain ⟨T,P,p,per⟩ := hc
  refine ⟨max (cut 0) (T+1),P,p,?_⟩
  intro n hn
  rw [localRule (n+P) (by omega),localRule n (by omega)]
  unfold abPredict
  rw [show n+P-1=(n-1)+P by omega, show n+P+1=(n+1)+P by omega,
      show n+P+6=(n+6)+P by omega, per n (by omega), per (n-1) (by omega),
      per (n+1) (by omega),per (n+6) (by omega)]

#print axioms abMaskPeriod

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
    by_cases hab : abMosaic
    · exact abMaskPeriod hcenter hab
    · -- Remaining mixed clocks do not have an A B⁺ A reset followed by an A/B mosaic.
      sorry
  exact MaskedRightRigidity.claim_of_periodic_mask step4_mixed_right_filter hcenter

end OpenProblem
