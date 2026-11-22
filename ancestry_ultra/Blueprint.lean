Warning: truncated output (original token count: 35312)
Total output lines: 2932

import Statement
import MaskedRightRigidity
import QuantifiedSplit

namespace OpenProblem.AncestryBlueprint

abbrev Trace := Nat → Bool

/-- The two simulations share only their imposed wall; every strict
coordinate starts white. Their boundary tests are independent. -/
def east (c : Trace) : Nat → Nat → Bool
  | 0, 0 => c 0
  | 0, _+1 => false
  | t+1, 0 => c (t+1)
  | t+1, j+1 => rule (east c t j) (east c t (j+1)) (east c t (j+2))

def west (c : Trace) : Nat → Nat → Bool
  | 0, 0 => c 0
  | 0, _+1 => false
  | t+1, 0 => c (t+1)
  | t+1, j+1 => rule (west c t (j+2)) (west c t (j+1)) (west c t j)

def need (c : Trace) (t : Nat) : Bool := xor (west c t 1) (c (t+1))
def whiteNeed (c : Trace) (t : Nat) : Bool := !c t && need c t
def BlackLock (c : Trace) : Prop := ∀ t, c t=true → west c t 1= !c (t+1)
def Joined (c : Trace) : Prop := ∀ t, c t=false → need c t=east c t 1
def Prefix (c : Trace) (T : Nat) : Prop := ∀ t, t<T → c t=false → need c t=east c t 1
def Mixed (c : Trace) : Prop := ∀ N (b : Bool), ∃ t, N≤t ∧ c t=b

private theorem west0 (c : Trace) (t : Nat) : west c t 0=c t := by cases t <;> rfl
private theorem east0 (c : Trace) (t : Nat) : east c t 0=c t := by cases t <;> rfl

private theorem vacuum (c : Trace) (t d : Nat) (away : t<d) : west c t d=false := by
  induction t generalizing d with
  | zero => cases d <;> simp_all [west]
  | succ t ih =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
    change rule (west c t (j+2)) (west c t (j+1)) (west c t j)=false
    rw [ih (j+2) (by omega),ih (j+1) (by omega),ih j (by omega)]
    rfl

private theorem tip (c : Trace) (mark : c 0=true) (t : Nat) : west c t t=true := by
  induction t with
  | zero => exact mark
  | succ t ih =>
    change rule (west c t (t+2)) (west c t (t+1)) (west c t t)=true
    rw [vacuum _ _ _ (by omega),vacuum _ _ _ (by omega),ih]
    rfl

private theorem period_mul (f : Trace) (T P : Nat) (h : ∀ t,T≤t → f (t+P)=f t)
    (k t : Nat) (late : T≤t) : f (t+P*k)=f t := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ,←Nat.add_assoc,h _ (by omega),ih]

private theorem left_inv (a b d : Bool) : xor (rule a b d) (b || d)=a := by
  cases a <;> cases b <;> cases d <;> rfl

/-- The black slots alone cannot supply an unmarked periodic head.
If the complementary white requests also had a period, two complete
western columns would share it and the marked west tip would be lost.
This argument never looks at the east, including its first cell. -/
theorem west_rich (c : Trace) (mark : c 0=true) (period : EventuallyPeriodic c)
    (black : BlackLock c) : ¬EventuallyPeriodic (whiteNeed c) := by
  rintro ⟨U,q,hq,perQ⟩
  obtain ⟨T,p,hp,perP⟩ := period
  let A := T+U
  let K := p*q
  have pc (t : Nat) (ht : A≤t) : c (t+K)=c t := period_mul c T p perP q t (by dsimp [A] at ht;omega)
  have pq (t : Nat) (ht : A≤t) : whiteNeed c (t+K)=whiteNeed c t := by
    rw [show K=q*p by exact Nat.mul_comm _ _]
    exact period_mul _ U q perQ p t (by dsimp [A] at ht;omega)
  have decode (t : Nat) : west c t 1=xor (c (t+1)) (c t || whiteNeed c t) := by
    cases ct : c t with
    | false => cases a : west c t 1 <;> cases b : c (t+1) <;> simp_all [whiteNeed,need]
    | true => rw [black t ct]; cases c (t+1) <;> rfl
  have flow (d t : Nat) (ht : A≤t) : west c (t+K) d=west c t d := by
    induction d using Nat.strongRecOn generalizing t with
    | ind d ih =>
      rcases d with _|d
      · simpa only [west0] using pc t ht
      rcases d with _|d
      · rw [decode,decode t,show t+K+1=t+1+K by omega,pc (t+1) (by omega),pc t ht,pq t ht]
      · have prev (u : Nat) : west c u (d+2)=xor (west c (u+1) (d+1)) (west c u (d+1) || west c u d) :=
          (left_inv _ _ _).symm
        rw [prev,prev t,show t+K+1=t+1+K by omega,ih (d+1) (by omega) (t+1) (by omega),
          ih (d+1) (by omega) t ht,ih d (by omega) t ht]
  have endbit := flow (A+K) A (by omega)
  have pos : 0<K := Nat.mul_pos hp hq
  rw [tip c mark,vacuum c A (A+K) (by omega)] at endbit
  contradiction

structure Seven where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
  g : Bool
deriving DecidableEq

def seven (c : Trace) (t : Nat) : Seven :=
  ⟨east c t 1,east c t 2,east c t 3,east c t 4,east c t 5,east c t 6,east c t 7⟩

def code (w : Seven) : Nat := w.a.toNat+2*w.b.toNat+4*w.c.toNat+8*w.d.toNat+
  16*w.e.toNat+32*w.f.toNat+64*w.g.toNat

abbrev Mem := Bool × Bool
def read (y : Bool) (s : Mem) : Mem := (s.2,xor y (s.1 || s.2))

def scan (w : Seven) (z : Bool) (s : Mem) : Mem :=
  read w.a (read w.b (read w.c (read w.d (read w.e (read w.f (read w.g (read z s)))))))

def reset (w : Seven) (z : Bool) : Bool :=
  let v := scan w z (false,false)
  v==scan w z (false,true) && v==scan w z (true,false) && v==scan w z (true,true)

def capable (w : Seven) : Bool := reset w false || reset w true
def permits (w : Seven) (z b : Bool) : Bool :=
  let v := (b,false)
  scan w z (false,false)==v || scan w z (false,true)==v ||
  scan w z (true,false)==v || scan w z (true,true)==v

def exceptional (w : Seven) : Bool := let v := code w; v==67 || v==91 || v==95 || v==123
def guess (w : Seven) : Bool :=
  if exceptional w then code w==91 else permits w false true || permits w true true

private theorem undo (l m r : Bool) : read (rule l m r) (r,m)=(m,l) := by
  cases l <;> cases m <;> cases r <;> rfl

/-- This equality uses all eight actual eastern Rule-30 updates, not a
supplied eight-bit observation stream. The last input state comes from
the initialized half itself. Output coordinates are (old head,old wall). -/
theorem physical_scan (c : Trace) (t : Nat) :
    scan (seven c (t+1)) (east c (t+1) 8) (east c t 9,east c t 8)=(east c t 1,c t) := by
  simp only [seven,scan,east,undo,east0]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
private theorem decoder_cert : ∀ a b d e f g h z x y : Bool,
    let w : Seven := ⟨a,b,d,e,f,g,h⟩
    capable w=true → (scan w z (x,y)).2=false → (scan w z (x,y)).1≠guess w →
      exceptional w=true ∧ z=true ∧ reset w z=false := by decide

/-- Exact finite exception: on a previous white wall, a reset-capable
seven-word decodes the old head unless it is one of four specified
words followed by a HIGH eighth bit that does not reset. -/
theorem decoder_bound (c : Trace) (t : Nat) (white : c t=false)
    (capableHere : capable (seven c (t+1))=true)
    (wrong : east c t 1≠guess (seven c (t+1))) :
    exceptional (seven c (t+1))=true ∧ east c (t+1) 8=true ∧
      reset (seven c (t+1)) (east c (t+1) 8)=false := by
  let w := seven c (t+1)
  have e := decoder_cert w.a w.b w.c w.d w.e w.f w.g (east c (t+1) 8)
    (east c t 9) (east c t 8)
  have old := physical_scan c t
  change scan w _ _ = _ at old
  exact e capableHere (by rw [old];exact white) (by rw [old];exact wrong)

/-- Read all older interior cells of the same inverse scan. The end
state supplied by the real east half includes the older eighth bit. -/
def rewind (w : Seven) (z : Bool) (s : Mem) : Seven :=
  let h := read z s
  let g := read w.g h
  let f := read w.f g
  let e := read w.e f
  let d := read w.d e
  let b := read w.c d
  let a := read w.b b
  ⟨a.2,b.2,d.2,e.2,f.2,g.2,h.2⟩

theorem physical_rewind (c : Trace) (t : Nat) :
    rewind (seven c (t+1)) (east c (t+1) 8) (east c t 9,east c t 8)=seven c t := by
  simp only [rewind,seven,east,undo]

private def escapeClass (w : Seven) (past : Mem) : Prop :=
  (past=(true,false) ∧ (code w=67 ∨ code w=95 ∨ code w=123)) ∨
  (past=(false,true) ∧ (code w=67 ∨ code w=91))

set_option synthInstance.maxSize 2800 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 15000 in
private theorem older_cert : ∀ a b d e f g h z x y X Y : Bool,
    let w : Seven := ⟨a,b,d,e,f,g,h⟩
    exceptional w=true → (scan w z (x,y)).2=false → (scan w z (x,y)).1≠guess w →
      ((scan (rewind w z (x,y)) y (X,Y)=(true,false) ∧ (code w=67 ∨ code w=95 ∨ code w=123)) ∨
       (scan (rewind w z (x,y)) y (X,Y)=(false,true) ∧ (code w=67 ∨ code w=91))) := by decide

private theorem older_escape (c : Trace) (t : Nat) (w : Seven) (word : seven c (t+2)=w)
    (white : c (t+1)=false) (special : exceptional w=true) (bad : east c (t+1) 1≠guess w) :
    escapeClass w (east c t 1,c t) := by
  subst w
  let w := seven c (t+2)
  let z := east c (t+2) 8
  let x := (east c (t+1) 9,east c (t+1) 8)
  let y := (east c t 9,east c t 8)
  have now : scan w z x=(east c (t+1) 1,c (t+1)) := physical_scan c (t+1)
  have old : scan (rewind w z x) x.2 y=(east c t 1,c t) := by
    rw [show rewind w z x=seven c (t+1) by exact physical_rewind c (t+1)]
    exact physical_scan c t
  have hv := older_cert w.a w.b w.c w.d w.e w.f w.g z x.1 x.2 y.1 y.2 special
    (by rw [now];exact white) (by rw [now];exact bad)
  change escapeClass w (scan (rewind w z x) x.2 y) at hv
  rw [old] at hv
  exact hv

/-- The earlier black cut is an absolute source fixture, not an
unconstrained eighth-bit transfer. In the 67 case the OLD ninth cell is
specified because it was the true input to the eighth update. -/
def BlackCut (c : Trace) (t : Nat) (w : Seven) : Prop :=
  (code w=67 ∧ code (seven c t)=0 ∧ east c t 8=false ∧ east c t 9=true) ∨
  (code w=91 ∧ east c t 2=true ∧
    let v := code (seven c t) + 128*(east c t 8).toNat
    v=6 ∨ v=122 ∨ v=186)

set_option synthInstance.maxSize 2800 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 15000 in
private theorem cut_cert : ∀ a b d e f g h z x y X Y : Bool,
    let w : Seven := ⟨a,b,d,e,f,g,h⟩
    let v := rewind w z (x,y)
    let k := rewind v y (X,Y)
    (code w=67 ∨ code w=91) → (scan w z (x,y)).2=false → (scan w z (x,y)).1≠guess w →
      scan v y (X,Y)=(false,true) →
      ((code w=67 ∧ code k=0 ∧ Y=false ∧ X=true) ∨ (code w=91 ∧ k.b=true ∧
        let v := code k+128*Y.toNat
        v=6 ∨ v=122 ∨ v=186)) := by decide

private theorem physical_cut (c : Trace) (t : Nat) (w : Seven) (word : seven c (t+2)=w)
    (white : c (t+1)=false) (special : code w=67 ∨ code w=91)
    (bad : east c (t+1) 1≠guess w) (back : (east c t 1,c t)=(false,true)) :
    BlackCut c t w := by
  subst w
  let w := seven c (t+2)
  let z := east c (t+2) 8
  let x := (east c (t+1) 9,east c (t+1) 8)
  let y := (east c t 9,east c t 8)
  have now : scan w z x=(east c (t+1) 1,c (t+1)) := physical_scan c (t+1)
  have old : rewind w z x=seven c (t+1) := physical_rewind c (t+1)
  have prev : scan (rewind w z x) x.2 y=(false,true) := by
    rw [old]; exact (physical_scan c t).trans back
  have readback : rewind (rewind w z x) x.2 y=seven c t := by rw [old];exact physical_rewind c t
  have H := cut_cert w.a w.b w.c w.d w.e w.f w.g z x.1 x.2 y.1 y.2 special
    (by rw [now];exact white) (by rw [now];exact bad) prev
  change (code w=67 ∧ code (rewind (rewind w z x) x.2 y)=0 ∧ y.2=false ∧ y.1=true) ∨
    (code w=91 ∧ (rewind (rewind w z x) x.2 y).b=true ∧
    let v := code (rewind (rewind w z x) x.2 y)+128*y.2.toNat
    v=6 ∨ v=122 ∨ v=186) at H
  rw [readback] at H
  exact H

private theorem mirrored (c : Trace) (t : Nat) (bw : c t=true) (white : c (t+1)=false)
    (zero : east c t 1=false) (join : Joined c) :
    xor (west c t 2) (east c t 2)=c (t+2) := by
  have q := join (t+1) white
  change xor (rule (west c t 2) (west c t 1) (west c t 0)) (c (t+2)) =
    rule (east c t 0) (east c t 1) (east c t 2) at q
  rw [west0,east0,bw,zero] at q
  cases u : west c t 2 <;> cases v : east c t 2 <;> cases b : c (t+2) <;> simp_all [rule]

-- The condensation-rank certificate from the shared Step 4, now
-- applied to the actual initialized eastern half of an imposed clock.
private def r8bad (a b c d e f g h : Bool) := !reset ⟨a,b,c,d,e,f,g⟩ h
private def r8code (a b c d e f g h : Bool) := code ⟨a,b,c,d,e,f,g⟩ + 128*h.toNat
def noreset (c : Trace) (t : Nat) := !reset (seven c t) (east c t 8)
private def emask (c : Trace) (t : Nat) := east c t 1 && !c t
private def r8state (c : Trace) (t : Nat) := code (seven c t) + 128*(east c t 8).toNat
private def r8rank (s : Nat) : Nat := (0xb201001100001111000000005100012200000000000000003501000000000728a200001100006412000000000000000032050011000000000000000000000189b201000000005412000000006100017300000000000000000000000000000000980000520000111100000000000000000000000000000000000000000000012a >>> (4*s)) % 16
private def r8next : Nat → Nat
  | 57 => 206 | 206 => 115 | 115 => 156 | 156 => 231 | 231 => 57 | _ => 0
private def r8read (s : Nat) : Bool := decide (s = 231)
private def r8turn (s : Nat) : Nat := r8next (r8next (r8next (r8next (r8next s))))
private abbrev r8edge (x y : Nat) (q : Bool) : Prop :=
  r8rank y ≤ r8rank x ∧ (r8rank y = r8rank x →
    y = r8next x ∧ q = r8read x ∧ r8turn x = x)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem r8cert : ∀ a b c d e f g h k v : Bool,
    r8bad a b c d e f g h = true → r8bad (rule v a b) (rule a b c) (rule b c d) (rule c d e) (rule d e f) (rule e f g) (rule f g h) (rule g h k) = true →
    r8edge (r8code a b c d e f g h) (r8code (rule v a b) (rule a b c) (rule b c d) (rule c d e) (rule d e f) (rule e f g) (rule f g h) (rule g h k)) (a && !v) := by decide
private theorem r8local (c : Trace) (t : Nat) (a : noreset c t = true) (b : noreset c (t+1) = true) :
    r8edge (r8state c t) (r8state c (t+1)) (emask c t) := by
  have cert := r8cert (east c t 1) (east c t 2) (east c t 3) (east c t 4)
    (east c t 5) (east c t 6) (east c t 7) (east c t 8) (east c t 9) (east c t 0)
  simpa only [emask,r8state,r8code,seven,east,east0] using cert a b
private theorem r8steady (f : Nat → Nat) (T : Nat)
    (mono : ∀ t, T ≤ t → f (t+1) ≤ f t) :
    ∃ s, T ≤ s ∧ ∀ t, s ≤ t → f (t+1) = f t := by
  have later (a b : Nat) (ha : T ≤ a) (hab : a ≤ b) : f b ≤ f a := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hab
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih => exact Nat.le_trans (mono (a+d) (by omega)) (ih (by omega))
  have down (m : Nat) : ∀ a, T ≤ a → f a = m →
      ∃ s, T ≤ s ∧ ∀ t, s ≤ t → f (t+1) = f t := by
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro a ha val
      by_cases drop : ∃ b, a ≤ b ∧ f (b+1) < f b
      · obtain ⟨b,hb,hv⟩ := drop
        have le := later a b ha hb
        exact ih (f (b+1)) (by omega) (b+1) (by omega) rfl
      · refine ⟨a,ha,?_⟩
        intro b hb
        have no : ¬ f (b+1) < f b := fun y => drop ⟨b,hb,y⟩
        have low := mono b (by omega)
        omega
  exact down (f T) T (Nat.le_refl _) rfl
private theorem r8maskPeriod (c : Trace) (T : Nat) (h : ∀ t, T ≤ t → noreset c t = true) :
    EventuallyPeriodic (emask c) := by
  have path (t : Nat) (ht : T ≤ t) := r8local c t (h t ht) (h (t+1) (by omega))
  obtain ⟨s,hs,eq⟩ := r8steady (fun t => r8rank (r8state c t)) T
    (fun t ht => (path t ht).1)
  have step (t : Nat) (ht : s ≤ t) := (path t (by omega)).2 (eq t ht)
  refine ⟨s,5,by decide,?_⟩
  intro t ht
  have e0 := step t ht
  have e1 := step (t+1) (by omega)
  have e2 := step (t+2) (by omega)
  have e3 := step (t+3) (by omega)
  have e4 := step (t+4) (by omega)
  have e5 := step (t+5) (by omega)
  have ret : r8state c (t+5) = r8state c t := by
    calc r8state c (t+5) = r8next (r8state c (t+4)) := e4.1
         _ = r8next (r8next (r8state c (t+3))) := by rw [e3.1]
         _ = r8next (r8next (r8next (r8state c (t+2)))) := by rw [e2.1]
         _ = r8next (r8next (r8next (r8next (r8state c (t+1))))) := by rw [e1.1]
         _ = r8turn (r8state c t) := by rw [e0.1]; rfl
         _ = r8state c t := e0.2.2
  rw [e5.2.1,ret,← e0.2.1]

private theorem next_reset_of_dead (c : Trace) (t : Nat) (nr : noreset c t=true)
    (floor : r8rank (r8state c t)=0) (dead : r8turn (r8state c t)≠r8state c t) :
    noreset c (t+1)=false := by
  cases next : noreset c (t+1)
  · rfl
  · have edge := r8local c t nr next
    exact False.elim (dead ((edge.2 (Nat.le_antisymm edge.1 (by omega))).2.2))

private def next8 (v a b d e f g h z k : Bool) :=
  r8code (rule v a b) (rule a b d) (rule b d e) (rule d e f)
    (rule e f g) (rule f g h) (rule g h z) (rule h z k)

set_option maxRecDepth 5000 in
private theorem zero_pre_cert : ∀ v a b d e f g h z k : Bool,
    let old := r8code a b d e f g h z
    let new := next8 v a b d e f g h z k
    (new=0 → (v=false → old=0) ∧ (v=true → old=127 ∨ old=255)) ∧
      ((new=127 ∨ new=255) → r8bad a b d e f g h z=false) := by decide

private theorem zero_pre (c : Trace) (i : Nat) :
    (r8state c (i+1)=0 → (c i=false → r8state c i=0) ∧
      (c i=true → r8state c i=127 ∨ r8state c i=255)) ∧
    ((r8state c (i+1)=127 ∨ r8state c (i+1)=255) → noreset c i=false) := by
  have h := zero_pre_cert (east c i 0) (east c i 1) (east c i 2) (east c i 3)
    (east c i 4) (east c i 5) (east c i 6) (east c i 7) (east c i 8) (east c i 9)
  simpa only [r8state,r8code,next8,r8bad,noreset,seven,east,east0] using h

private def WestFront (c : Trace) (i L : Nat) :=
  (∀d,d<L → west c i d=false) ∧ west c i L=true

/-- Unfold an entire incoming western pulse, not an independent
bit test at the final black. Both halves fix the initial head. -/
private theorem inverse_front (c : Trace) (i L : Nat)
    (head : west c i 1=xor (c (i+1)) (c i)) (front : WestFront c (i+1) L) :
    (∀ d,d≤L → west c i d=c i) ∧ west c i (L+1)= !c i := by
  have ribbon (d : Nat) (dl : d≤L) : west c i d=c i ∧
      west c i (d+1)=xor (west c (i+1) d) (c i) := by
    induction d with
    | zero => exact ⟨west0 c i,by rwa [west0]⟩
    | succ d ih =>
      obtain ⟨ls,rs⟩ := ih (by omega)
      rw [front.1 d (by omega)] at rs
      simp only [Bool.false_xor] at rs
      have inv : west c i (d+2)=xor (west c (i+1) (d+1)) (west c i (d+1) || west c i d) :=
        (left_inv _ _ _).symm
      exact ⟨rs,by rw [inv,rs,ls,Bool.or_self]⟩
  refine ⟨fun d dl => (ribbon d dl).1,?_⟩
  rw [(ribbon L (Nat.le_refl _)).2,front.2]
  cases c i <;> rfl

/-- The point of this run-level statistic is its third trailing bit.
Its index moves with the ENTIRE intervening run, but the value has no
residual dependence on the parity of the run length. -/
structure PulseAt (c : Trace) (P t j L : Nat) : Prop where
  date : j+1+L=t
  gap : t≤j+P
  black : c j=true
  whites : ∀i,j<i → i<t → c i=false
  westBlack : ∀d,d≤L → west c j d=true
  westEdge : west c j (L+1)=false
  carried : west c j (L+3)=west c t 2

private theorem pulse_riders (c : Trace) (t L : Nat) (length : L≤t)
    (wf : ∀ n,n≤L → WestFront c (t-n) n) :
    xor (west c (t-L) (L+1)) (west c (t-L) (L+2))=xor (west c t 1) (west c t 2) := by
  have ride (n : Nat) (nl : n≤L) :
      xor (west c (t-n) (n+1)) (west c (t-n) (n+2))=xor (west c t 1) (west c t 2) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      let i:=t-(n+1)
      have f := wf (n+1) nl
      have w1 : west c i (n+1)=true := f.2
      have w0 : west c i n=false := f.1 n (by omega)
      have a : west c (i+1) (n+1)= !west c i (n+2) := by
        change rule _ _ _=_
        rw [w1,w0];cases west c i (n+2) <;> rfl
      have b : west c (i+1) (n+2)= !west c i (n+3) := by
        change rule _ _ _=_
        rw [w1];cases west c i (n+2) <;> cases west c i (n+3) <;> rfl
      have day : t-n=i+1 := by dsimp [i];omega
      have old := ih (by omega)
      rw [day,a,b] at old
      exact (by cases west c i (n+2) <;> cases west c i (n+3) <;> rfl :
        xor (west c i (n+2)) (west c i (n+3))=xor (!west c i (n+2)) (!west c i (n+3))) |>.trans old
  exact ride L (Nat.le_refl _)

private theorem actual_pulse (c : Trace) (T P t : Nat) (hp : 0<P)
    (period : ∀i,T≤i → c (i+P)=c i) (late : T+P+1≤t)
    (black : BlackLock c) (join : Joined c) (bt : c t=true) (nextW : c (t+1)=false)
    (head0 : east c t 1=false) : ∃ j L,PulseAt c P t j L := by
  let a:=t-P
  have atA : c a=true := by rw [←period a (by dsimp [a];omega),show a+P=t by dsimp [a];omega,bt]
  have last (n : Nat) : ∃j,a≤j ∧ j≤a+n ∧ c j=true ∧ ∀i,j<i → i≤a+n → c i=false := by
    induction n with
    | zero => exact ⟨a,Nat.le_refl _,by omega,atA,fun _ _ _ => by omega⟩
    | succ n ih =>
      cases h : c (a+n+1)
      · obtain ⟨j,aj,jb,cj,clear⟩ := ih
        exact ⟨j,aj,by omega,cj,fun i ji ib => by
          by_cases e : i=a+n+1
          · rwa [e]
          · exact clear i ji (by omega)⟩
      · exact ⟨a+n+1,by omega,by omega,h,fun _ _ _ => by omega⟩
  obtain ⟨j,aj,jt,bj,all⟩ := last (P-1)
  have jb : j<t := by dsimp [a] at jt;omega
  have whites (i : Nat) (ji : j<i) (it : i<t) : c i=false := all i ji (by dsimp [a];omega)
  let L := t-j-1
  have eq : j+1+L=t := by dsimp [L];omega
  have head (n : Nat) (nl : n≤L) : east c (t-n) 1=false := by
    induction n with
    | zero => exact head0
    | succ n ih =>
      let i:=t-(n+1)
      have day : t-n=i+1 := by dsimp [i];omega
      have old:=ih (by omega)
      rw [day] at old
      change rule (east c i 0) (east c i 1) (east c i 2)=false at old
      rw [east0,whites i (by dsimp [i];omega) (by dsimp [i];omega)] at old
      cases v : east c i 1
      · rfl
      · rw [v] at old;contradiction
  have wf (n : Nat) (lim : n≤L) : WestFront c (t-n) n := by
    induction n with
    | zero => exact ⟨fun _ h => by omega,by simpa only [Nat.sub_zero,west0] using bt⟩
    | succ n ih =>
      let i:=t-(n+1)
      have wi := whites i (by dsimp [i];omega) (by dsimp [i];omega)
      have z : east c i 1=false := head (n+1) lim
      have q := join i wi
      have H : west c i 1=xor (c (i+1)) (c i) := by
        cases x : west c i 1 <;> cases y : c (i+1) <;> simp_all [need]
      have step := inverse_front c i n H (by rw [show i+1=t-n by dsimp [i];omega];exact ih (by omega))
      exact ⟨fun d dl => (step.1 d (by omega)).trans wi,by rw [step.2,wi];rfl⟩
  have before := inverse_front c j L (by rw [black j bj,bj];cases c (j+1) <;> rfl)
    (by simpa only [show t-L=j+1 by omega] using wf L (Nat.le_refl _))
  have wb : west c j L=true := (before.1 L (Nat.le_refl _)).trans bj
  have we : west c j (L+1)=false := by rw [before.2,bj];rfl
  have h := pulse_riders c t L (by omega) wf
  rw [show t-L=j+1 by omega,black t bt,nextW] at h
  change xor (rule _ _ _) (rule _ _ _)=xor true (west c t 2) at h
  rw [we,wb] at h
  have carried : west c j (L+3)=west c t 2 := by
    cases x : west c j (L+2) <;> cases y : west c j (L+3) <;> cases z : west c t 2 <;> simp_all [rule]
  exact ⟨j,L,eq,by dsimp [a] at aj;omega,bj,whites,fun d dl => (before.1 d dl).trans bj,we,carried⟩

/-- The full clock-relative 67 reset episode, including its signed
western founder. -/
def ClockCut67 (c : Trace) (P t : Nat) : Prop :=
  ∃ j L,PulseAt c P t j L ∧ noreset c (j-1)=false ∧
    (r8state c j=127 ∨ r8state c j=255) ∧ (∀ i,j<i → i≤t → r8state c i=0)

private theorem full_zero_run (c : Trace) (P t j L : Nat) (late : P+1≤t)
    (pulse : PulseAt c P t j L) (zero : r8state c t=0) : ClockCut67 c P t := by
  have gap := pulse.gap
  have date := pulse.date
  have back (n : Nat) (lt : j+n<t) : r8state c (t-n)=0 := by
    induction n with
    | zero => simpa using zero
    | succ n ih =>
      let i := t-(n+1)
      have next : r8state c (i+1)=0 := by rw [show i+1=t-n by dsimp [i];omega];exact ih (by omega)
      exact ((zero_pre c i).1 next).1 (pulse.whites i (by dsimp [i];omega) (by dsimp [i];omega))
  have clear (i : Nat) (ji : j<i) (it : i≤t) : r8state c i=0 := by
    simpa only [show t-(t-i)=i by omega] using back (t-i) (by omega)
  have atJ := ((zero_pre c j).1 (clear (j+1) (by omega) (by omega))).2 pulse.black
  have prior := (zero_pre c (j-1)).2 (by rwa [show j-1+1=j by omega])
  exact ⟨j,L,pulse,prior,atJ,clear⟩

/-- The two possible wrong arms occupy short gaps BETWEEN actual
resets, with an exact post-reset one tick after their exceptional
eight-bit state. For 91 the prior reset is at one of two named ticks. -/
def Bracket (c : Trace) (P t : Nat) (w : Seven) : Prop :=
  noreset c (t+3)=false ∧
    (code w=67 → ClockCut67 c P t) ∧
    (code w=91 → (∃j L,PulseAt c P t j L) ∧ (noreset c t=false ∨ noreset c (t+1)=false))

private theorem actual_bracket (c : Trace) (T P t : Nat) (hp : 0<P)
    (period : ∀i,T≤i → c (i+P)=c i) (late : T+P+1≤t) (locks : BlackLock c) (join : Joined c) (black : c t=true)
    (nextW : c (t+1)=false) (head0 : east c t 1=false)
    (w : Seven) (word : seven c (t+2)=w) (cut : BlackCut c t w)
    (bit : east c (t+2) 8=true) (unsync : reset w (east c (t+2) 8)=false) : Bracket c P t w := by
  have nr : noreset c (t+2)=true := by simp only [noreset,word,unsync,Bool.not_false]
  have st : r8state c (t+2)=code w+128 := by simp [r8state,word,bit]
  obtain ⟨j,L,pulse⟩ := actual_pulse c T P t hp period late locks join black nextW head0
  rcases cut with ⟨id,old,old8,_⟩|⟨id,_,prior⟩
  · rw [id] at st
    have after := next_reset_of_dead c (t+2) nr (by rw [st];decide) (by rw [st];decide)
    have zero : r8state c t=0 := by simp [r8state,old,old8]
    exact ⟨after,fun _ => full_zero_run c P t j L (by omega) pulse zero,fun h => by omega⟩
  · rw [id] at st
    have after := next_reset_of_dead c (t+2) nr (by rw [st];decide) (by rw [st];decide)
    refine ⟨after,fun h => by omega,fun _ => ⟨⟨j,L,pulse⟩,?_⟩⟩
    cases h : noreset c t
    · exact Or.inl rfl
    · apply Or.inr
      change r8state c t=6 ∨ r8state c t=122 ∨ r8state c t=186 at prior
      rcases prior with s|s|s <;> exact next_reset_of_dead c t h (by rw [s];decide) (by rw [s];decide)

private theorem cofinal_resets (c : Trace) (rich : ¬EventuallyPeriodic (whiteNeed c))
    (join : Joined c) : ∀ N, ∃ t, N≤t ∧ noreset c t=false := by
  have hmask : whiteNeed c=emask c := by
    funext t
    cases ht : c t
    · simpa only [whiteNeed,emask,ht,Bool.not_false,Bool.true_and,Bool.and_true] using join t ht
    · simp [whiteNeed,emask,ht]
  intro N
  apply Classical.byContradiction
  intro no
  apply rich
  rw [hmask]
  apply r8maskPeriod c N
  intro t ht
  cases h : noreset c t
  · exact False.elim (no ⟨t,ht,h⟩)
  · rfl

/-- Recurrence is used only to select genuine reset-start rows. No
recurrence of an endpoint or age-length prefix is postulated. -/
private theorem color_cofinal (S : Nat → Prop) (recur : ∀ N, ∃ t,N≤t ∧ S t)
    (f : Nat → Nat) (b : Nat) (bounded : ∀ t,f t<b) :
    ∃ v, ∀ N, ∃ t,N≤t ∧ S t ∧ f t=v := by
  classical
  apply Classical.byContradiction
  intro none
  have excludeColor (v : Nat) : ∃ n,∀ t,n≤t → S t → f t≠v := by
    by_cases h : ∃ n,∀ t,n≤t → S t → f t≠v
    · exact h
    · apply False.elim
      apply none
      refine ⟨v,fun n => ?_⟩
      apply Classical.byContradiction
      intro no
      exact h ⟨n,fun t ht st eq => no ⟨t,ht,st,eq⟩⟩
  have tail (k : Nat) : ∃ n,∀ t,n≤t → S t → k≤f t := by
    induction k with
    | zero => exact ⟨0,fun _ _ _ => Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨n,hn⟩ := ih
      obtain ⟨m,hm⟩ := excludeColor k
      exact ⟨n+m,fun t h st => by have := hn t (by omega) st;have := hm t (by omega) st;omega⟩
  obtain ⟨n,hn⟩ := tail b
  obtain ⟨t,late,st⟩ := recur n
  exact (Nat.not_lt_of_ge (hn t late st)) (bounded t)

private theorem same_clock (c : Trace) (T P : Nat) (per : ∀t,T≤t → c (t+P)=c t)
    (s u : Nat) (old : T≤s) (newer : T≤u) (ph : (s-T)%P=(u-T)%P) :
    ∀ i,c (s+i)=c (u+i) := by
  intro i
  let j := (s-T)%P
  have S := Nat.mod_add_div (s-T) P
  have U := Nat.mod_add_div (u-T) P
  have hS : T+j+i+P*((s-T)/P)=s+i := by dsimp [j];omega
  have hU : T+j+i+P*((u-T)/P)=u+i := by dsimp [j];omega
  rw [←hS,←hU,period_mul c T P per _ _ (by omega),period_mul c T P per _ _ (by omega)]

private theorem west_read (c : Trace) (black : BlackLock c) (t : Nat) :
    west c t 1=xor (c (t+1)) (c t || whiteNeed c t) := by
  cases ct : c t with
  | false => cases a : west c t 1 <;> cases b : c (t+1) <;> simp_all [whiteNeed,need]
  | true => rw [black t ct];cases c (t+1) <;> rfl

/-- If k is the innermost nonmatching western cell at a reset
pair, the true discrepancy moves inward at exactly one cell per tick.
It arrives at the first mismatching white request exactly k−1 ticks
later. This induction uses the signed actual differences, not a speed
bound on an arbitrary disturbance. -/
private theorem ballistic (c : Trace) (black : BlackLock c) (k s u : Nat)
    (clk : ∀ i,c (s+i)=c (u+i))
    (near : ∀ i,i<k+1 → west c s i=west c u i)
    (edge : west c s (k+1)≠west c u (k+1)) :
    (∀ j,j<k → whiteNeed c (s+j)=whiteNeed c (u+j)) ∧
      whiteNeed c (s+k)≠whiteNeed c (u+k) := by
  have eq_iff (x y : Nat) (h : c x=c y) (hn : c (x+1)=c (y+1)) :
      whiteNeed c x=whiteNeed c y ↔ west c x 1=west c y 1 := by
    constructor
    · intro eq;rw [west_read c black x,west_read c black y,h,hn,eq]
    · intro eq;unfold whiteNeed need;rw [h,hn,eq]
  induction k generalizing s u with
  | zero =>
    simp only [Nat.add_zero] at *
    exact ⟨fun _ h => by omega,fun eq => edge ((eq_iff s u (clk 0) (clk 1)).mp eq)⟩
  | succ k ih =>
    have ns (i : Nat) (hi : i<k+1) : west c (s+1) i=west c (u+1) i := by
      cases i with
      | zero => simpa only [west0] using clk 1
      | succ i => change rule _ _ _=rule _ _ _; rw [near (i+2) (by omega),near (i+1) (by omega),near i (by omega)]
    have ne : west c (s+1) (k+1)≠west c (u+1) (k+1) := by
      intro eq
      have h := congrArg (fun b => xor b (west c s (k+1) || west c s k)) eq
      change xor (rule _ _ _) _=xor (rule _ _ _) _ at h
      rw [left_inv,near (k+1) (by omega),near k (by omega),left_inv] at h
      exact edge h
    have step := ih (s+1) (u+1) (fun i => by simpa only [Nat.add_right_comm s 1 i,Nat.add_right_comm u 1 i,Nat.add_assoc] using clk (i+1)) ns ne
    constructor
    · intro j hj
      cases j with
      | zero => simpa only [Nat.add_zero] using (eq_iff s u (clk 0) (clk 1)).mpr (near 1 (by omega))
      | succ j => simpa [Nat.add_assoc,Nat.add_comm 1 j] using step.1 j (by omega)
    · simpa [Nat.add_assoc,Nat.add_comm 1 k] using step.2

private theorem east_vacuum (c : Trace) (t d : Nat) (away : t<d) : east c t d=false := by
  induction t generalizing d with
  | zero => cases d <;> simp_all [east]
  | succ t ih =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
    change rule (east c t j) (east c t (j+1)) (east c t (j+2))=false
    rw [ih j (by omega),ih (j+1) (by omega),ih (j+2) (by omega)]
    rfl

/-- True noncancelling eastern genealogy. The last coordinate charges
2 for an outward edge, 1 for a stay and 0 for an inward edge; an inward
edge requires the receiving site vacant in BOTH copies. -/
inductive EastRoute (c : Trace) (s u y : Nat) : Nat → Nat → Nat → Prop where
  | origin (pos : 0<y) (live : east c s y≠east c u y) : EastRoute c s u y 0 y 0
  | outward {n j a} (prev : EastRoute c s u y n j a)
      (gate : (east c (s+n) (j+1) || east c (s+n) (j+2))=
        (east c (u+n) (j+1) || east c (u+n) (j+2))) :
      EastRoute c s u y (n+1) (j+1) (a+2)
  | stay {n j a} (prev : EastRoute c s u y n (j+1) a)
      (left : east c (s+n) j=east c (u+n) j)
      (gate : (east c (s+n) (j+1) || east c (s+n) (j+2))≠
        (east c (u+n) (j+1) || east c (u+n) (j+2))) :
      EastRoute c s u y (n+1) (j+1) (a+1)
  | inward {n j a} (prev : EastRoute c s u y n (j+2) a)
      (left : east c (s+n) j=east c (u+n) j)
      (emptyS : east c (s+n) (j+1)=false) (emptyU : east c (u+n) (j+1)=false) :
      EastRoute c s u y (n+1) (j+1) a

private theorem parents : ∀ l m r L M R : Bool,rule l m r≠rule L M R →
    (l≠L ∧ (m || r)=(M || R)) ∨
    (l=L ∧ m≠M ∧ (m || r)≠(M || R)) ∨
    (l=L ∧ m=false ∧ M=false ∧ r≠R) := by decide

private theorem pull_east (c : Trace) (s u n j : Nat)
    (clk : ∀i,c (s+i)=c (u+i)) (diff : east c (s+n) j≠east c (u+n) j) :
    ∃ y a,y+a=n+j ∧ east c s y≠east c u y ∧ EastRoute c s u y n j a := by
  induction n generalizing j with
  | zero =>
    simp only [Nat.add_zero] at diff
    have pos : 0<j := by
      cases j with
      | zero => exact False.elim (diff (by simpa only [east0,Nat.add_zero] using clk 0))
      | succ j => omega
    exact ⟨j,0,by omega,diff,.origin pos diff⟩
  | succ n ih =>
    cases j with
    | zero => exact False.elim (diff (by simpa only [east0] using clk (n+1)))
    | succ j =>
      have bad : rule (east c (s+n) j) (east c (s+n) (j+1)) (east c (s+n) (j+2))≠
          rule (east c (u+n) j) (east c (u+n) (j+1)) (east c (u+n) (j+2)) := by
        rw [show s+(n+1)=s+n+1 by omega,show u+(n+1)=u+n+1 by omega] at diff
        exact diff
      rcases parents _ _ _ _ _ _ bad with ⟨d,gate⟩|⟨left,d,gate⟩|⟨left,x,z,d⟩
      · obtain ⟨y,a,eq,raw,path⟩ := ih j d
        exact ⟨y,a+2,by omega,raw,.outward path gate⟩
      · obtain ⟨y,a,eq,raw,path⟩ := ih (j+1) d
        exact ⟨y,a+1,by omega,raw,.stay path left gate⟩
      · obtain ⟨y,a,eq,raw,path⟩ := ih (j+2) d
        exact ⟨y,a,by omega,raw,.inward path left x z⟩

private theorem joined_grid (c : Trace) (mark : c 0=true) (black : BlackLock c) (join : Joined c)
    (t d : Nat) : east c t d=cell t (d:Int) ∧ west c t d=cell t (-(d:Int)) := by
  have wall (i : Nat) : c (i+1)=rule (west c i 1) (c i) (east c i 1) := by
    cases co : c i
    · have w := join i co
      cases l : west c i 1 <;> cases r : east c i 1 <;> cases v : c (i+1) <;> simp_all [need,rule]
    · rw [black i co];cases c (i+1) <;> rfl
  induction t generalizing d with
  | zero =>
    cases d with
    | zero => exact ⟨mark,mark⟩
    | succ d => simp [east,west,cell];omega
  | succ t ih =>
    cases d with
    | zero =>
      have h := wall t
      rw [(ih 1).2,(ih 1).1,←east0 c t,(ih 0).1] at h
      exact ⟨h,h⟩
    | succ d =>
      constructor
      · simp only [east,(ih d).1,(ih (d+1)).1,(ih (d+2)).1,cell]
        congr 1 <;> congr 1 <;> omega
      · simp only [west,(ih d).2,(ih (d+1)).2,(ih (d+2)).2,cell]
        congr 1 <;> congr 1 <;> omega

/-- Parent in the real lag-Q spacetime comparison. This map is ordered
also at common sites, so two genuine western/eastern donors can be
traced together all the way to ONE shared initial comparison. -/
private def parentOf (Q i : Nat) (x : Int) : Int :=
  if cell i (x-1)≠cell (Q+i) (x-1) then x-1
  else if cell i x≠cell (Q+i) x then x else x+1

private def original (Q : Nat) : Nat → Int → Int
  | 0,x => x
  | i+1,x => original Q i (parentOf Q i x)

private theorem parent_bounded (Q i : Nat) (x : Int) :
    x-1≤parentOf Q i x ∧ parentOf Q i x≤x+1 := by
  by_cases l : cell i (x-1)≠cell (Q+i) (x-1) <;> by_cases m : cell i x≠cell (Q+i) x <;> simp_all [parentOf] <;> omega

private theorem parent_order (Q i : Nat) (x y : Int) (le : x≤y) :
    parentOf Q i x≤parentOf Q i y := by
  have xb := parent_bounded Q i x
  have yb := parent_bounded Q i y
  by_cases apart : x+2≤y
  · omega
  by_cases eq : x=y
  · rw [eq];exact Int.le_refl _
  have adj : y-1=x := by omega
  by_cases l : cell i (x-1)≠cell (Q+i) (x-1) <;> by_cases m : cell i x≠cell (Q+i) x <;>
    by_cases r : cell i y≠cell (Q+i) y <;> simp_all [parentOf] <;> omega

private theorem original_order (Q n : Nat) (x y : Int) (le : x≤y) :
    original Q n x≤original Q n y := by
  induction n generalizing x y with
  | zero => exact le
  | succ n ih => exact ih _ _ (parent_order Q n x y le)

private theorem original_bounds (Q n : Nat) (x : Int) :
    x-(n:Int)≤original Q n x ∧ original Q n x≤x+(n:Int) := by
  induction n generalizing x with
  | zero => simp [original]
  | succ n ih =>
    have b := ih (parentOf Q n x)
    have d := parent_bounded Q n x
    unfold original;omega

private theorem parent_live (Q n : Nat) (x : Int) (live : cell (n+1) x≠cell (Q+(n+1)) x) :
    cell n (parentOf Q n x)≠cell (Q+n) (parentOf Q n x) := by
  rw [show Q+(n+1)=Q+n+1 by omega] at live
  unfold parentOf
  split
  · assumption
  · next left =>
    split
    · assumption
    · next mid =>
      intro right
      apply live
      change rule _ _ _=rule _ _ _
      rw [Classical.byContradiction left,Classical.byContradiction mid,right]

private theorem original_live (Q n : Nat) (x : Int) (live : cell n x≠cell (Q+n) x) :
    cell 0 (original Q n x)≠cell Q (original Q n x) := by
  induction n generalizing x with
  | zero => simpa only [original,Nat.add_zero] using live
  | succ n ih => exact ih _ (parent_live _ _ _ live)

/-- No material edge can cross an aligned mature wall. Its two
sectors retain the same ordered separator at the ORIGINAL comparison
for the entire mature tail, even for unbounded lag. -/
private theorem seam_side (Q T s : Nat) (x : Int) (ts : T≤s)
    (wall : ∀i,T≤i → cell (Q+i) 0=cell i 0) (live : cell s x≠cell (Q+s) x) :
    (x<0 → original Q s x≤original Q T 0) ∧ (0<x → original Q T 0≤original Q s x) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le ts
  induction n generalizing x with
  | zero => exact ⟨fun l => original_order _ _ _ _ (by omega),fun r => original_order _ _ _ _ (by omega)⟩
  | succ n ih =>
    rw [show T+(n+1)=T+n+1 by omega] at live ⊢
    have past := parent_live Q (T+n) x live
    have nz : parentOf Q (T+n) x≠0 := by
      intro zero
      rw [zero] at past
      exact past (wall (T+n) (by omega)).symm
    have b := parent_bounded Q (T+n) x
    have was := ih (parentOf Q (T+n) x) (by omega) past
    exact ⟨fun l => was.1 (by omega),fun r => was.2 (by omega)⟩

private theorem aligned_lag (T P s u : Nat) (ts : T≤s) (su : s<u)
    (phase : (s-T)%P=(u-T)%P) : ∃ m,u-s=P*m := by
  have S := Nat.mod_add_div (s-T) P
  have U := Nat.mod_add_div (u-T) P
  have le : (s-T)/P≤(u-T)/P := Nat.div_le_div_right (by omega)
  refine ⟨(u-T)/P-(s-T)/P,?_⟩
  rw [Nat.mul_sub]
  omega

private theorem empty_outer (t : Nat) (x : Int) (out : x< -(t:Int) ∨ (t:Int)<x) : cell t x=false := by
  induction t generalizing x with
  | zero => simp [cell];omega
  | succ t ih =>
    change rule (cell t (x-1)) (cell t x) (cell t (x+1))=false
    rw [ih _ (by omega),ih _ (by omega),ih _ (by omega)];rfl

private def MarkedOrigin (Q : Nat) (x : Int) :=
  -(Q:Int)≤x ∧ x≤(Q:Int) ∧ ((x=0 ∧ center Q=false) ∨ (x≠0 ∧ cell Q x=true))

private theorem root_sign (Q n : Nat) (x : Int) (live : cell n x≠cell (Q+n) x) :
    MarkedOrigin Q (original Q n x) := by
  let j := original Q n x
  have seed : cell 0 j≠cell Q j := original_live Q n x live
  by_cases z : j=0
  · have a : cell 0 j=true := by simp [cell,z]
    have b : center Q=false := by cases k : center Q <;> simp_all [center]
    exact ⟨by omega,by omega,Or.inl ⟨z,b⟩⟩
  · have a : cell 0 j=false := by simp [cell,z]
    have b : cell Q j=true := by cases k : cell Q j <;> simp_all
    have valid : ¬(j< -(Q:Int) ∨ (Q:Int)<j) := fun outer => by
      have no := empty_outer Q j outer;rw [b] at no;contradiction
    exact ⟨by omega,by omega,Or.inr ⟨z,b⟩⟩

/-- Both founders are placed in the same row-0/row-Q comparison.
Only the original marked site can supply a negative root. Equal roots
are permitted only when their single light cone spans both founders. -/
def OriginalPair (T s u k y : Nat) : Prop :=
  let Q:=u-s
  let w:=original Q s (-((k+1:Nat):Int))
  let e:=original Q s (y:Int)
  let seam:=original Q T 0
  MarkedOrigin Q w ∧ MarkedOrigin Q e ∧ w≤seam ∧ seam≤e ∧
    -(T:Int)≤seam ∧ seam≤(T:Int) ∧
    (k+1+y : Nat) ≤ 2*s+(e-w).toNat

/-- Both sources must fit inside the same genuine finite cone. If
the east founder lies beyond the older mark, its sign is prescribed.
The western founder is exactly y plus the accumulated eastern charge. -/
def EastFounder (c : Trace) (T h s u k : Nat) : Prop :=
  ∃ y a,h+8<y ∧ y≤u ∧ y+a=k+1 ∧
    (s<y → east c s y=false ∧ east c u y=true) ∧ EastRoute c s u y k 1 a ∧ OriginalPair T s u k y

private theorem joint_founder (c : Trace) (T h s u k : Nat) (ts : T≤s) (su : s<u)
    (locked : ∀i,T≤i → c (u-s+i)=c i)
    (clk : ∀i,c (s+i)=c (u+i)) (mark : c 0=true) (black : BlackLock c) (join : Joined c)
    (westLive : west c s (k+1)≠west c u (k+1)) (same : ∀i,i≤h+8 → east c s i=east c u i)
    (split : whiteNeed c (s+k)≠whiteNeed c (u+k)) : EastFounder c T h s u k := by
  have wh : c (u+k)=false := by
    cases z : c (u+k)
    · rfl
    · exact False.elim (split (by simp [whiteNeed,clk k,z]))
  have whS := (clk k).trans wh
  have diff : east c (s+k) 1≠east c (u+k) 1 := by
    simpa only [whiteNeed,whS,wh,Bool.not_false,Bool.true_and,join (s+k) whS,join (u+k) wh] using split
  obtain ⟨y,a,eq,raw,path⟩ := pull_east c s u k 1 clk diff
  have out : h+8<y := Nat.lt_of_not_ge (fun inside => raw (same y inside))
  have within : y≤u := by
    by_cases outside : u<y
    · exact False.elim (raw ((east_vacuum c s y (by omega)).trans (east_vacuum c u y outside).symm))
    · omega
  have day : u-s+s=u := by omega
  have lw : cell s (-((k+1:Nat):Int))≠cell (u-s+s) (-((k+1:Nat):Int)) := by
    rwa [day,←(joined_grid c mark black join s (k+1)).2,←(joined_grid c mark black join u (k+1)).2]
  have le : cell s (y:Int)≠cell (u-s+s) (y:Int) := by
    rwa [day,←(joined_grid c mark black join s y).1,←(joined_grid c mark black join u y).1]
  have roots : OriginalPair T s u k y := by
    have order := original_order (u-s) s (-((k+1:Nat):Int)) y (by omega)
    have W := original_bounds (u-s) s (-((k+1:Nat):Int))
    have E := original_bounds (u-s) s (y:Int)
    have actual (i : Nat) : c i=cell i 0 := by simpa [east0] using (joined_grid c mark black join i 0).1
    have lock (i : Nat) (ti : T≤i) : cell (u-s+i) 0=cell i 0 := by rw [←actual,←actual,locked i ti]
    have wl := (seam_side (u-s) T s _ ts lock lw).1 (by omega)
    have el := (seam_side (u-s) T s _ ts lock le).2 (by omega)
    have belt := original_bounds (u-s) T 0
    exact ⟨root_sign _ _ _ lw,root_sign _ _ _ le,wl,el,by omega,by omega,by omega⟩
  exact ⟨y,a,out,within,eq,fun farther => by
    have old := east_vacuum c s y farther
    exact ⟨old,by cases bit : east c u y <;> simp_all⟩,path,roots⟩

/-- A paired reset REALIZED by two distinct ages of these same
initialized halves, and its nearest later western collision. -/
structure Matched (c : Trace) (T P d h s u k : Nat) : Prop where
  mature : T≤s
  ordered : s<u
  phase : (s-T)%P=(u-T)%P
  oldReset : noreset c s=false
  newReset : noreset c u=false
  sharedEast : ∀ i,i≤h+8 → east c s i=east c u i
  deep : d≤k
  deadline : k<u
  sharedWest : ∀ i,i≤k → west c s i=west c u i
  founder : west c s (k+1)≠west c u (k+1)
  common : ∀ j,j<k → whiteNeed c (s+j)=whiteNeed c (u+j)
  split : whiteNeed c (s+k)≠whiteNeed c (u+k)
  eastSource : EastFounder c T h s u k

/-- The common collars can be required arbitrarily wide independently. -/
def ResetStarts (c : Trace) (T P : Nat) : Prop :=
  ∀ N d h, ∃ s u k,N≤s ∧ Matched c T P d h s u k

open FiniteWindowRecurrence in
theorem reset_starts (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (per : ∀t,T≤t → c (t+P)=c t) (black : BlackLock c) (join : Joined c) : ResetStarts c T P := by
  intro N d h
  have recurrent := cofinal_resets c (west_rich c mark ⟨T,P,hp,per⟩ black) join
  let ph t := (t-T)%P
  let ew t := window (east c t) (h+9) 0
  let ww t := window (west c t) (d+1) 0
  obtain ⟨p,hp'⟩ := color_cofinal _ recurrent ph P (fun _ => Nat.mod_lt _ hp)
  obtain ⟨a,ha⟩ := color_cofinal _ hp' (fun t => encode (ew t)) (2^(h+9))
    (fun t => by simpa only [ew,window_len] using encode_bound (ew t))
  obtain ⟨b,hb⟩ := color_cofinal _ ha (fun t => encode (ww t)) (2^(d+1))
    (fun t => by simpa only [ww,window_len] using encode_bound (ww t))
  obtain ⟨s,ls,⟨⟨rs,ps⟩,es⟩,ws⟩ := hb (N+T)
  obtain ⟨u,lu,⟨⟨ru,pu⟩,eu⟩,wu⟩ := hb (s+1)
  have same_window {f : Nat → Nat → Bool} {n : Nat}
      (e : encode (window (f s) n 0)=encode (window (f u) n 0))
      (i : Nat) (il : i<n) : f s i=f u i := by
    have eq := same_encode_eq (by rw [window_len,window_len]) e
    have atI := congrArg (fun w : List Bool => w[i]?) eq
    simpa [window,il] using atI
  have far : west c s u≠west c u u := by rw [tip c mark,vacuum c s u (by omega)];decide
  have first (x : Nat) (hx : west c s x≠west c u x) :
      ∃ y,y≤x ∧ west c s y≠west c u y ∧ ∀i,i<y → west c s i=west c u i := by
    induction x using Nat.strongRecOn with
    | ind x ih =>
      by_cases prior : ∃ i,i<x ∧ west c s i≠west c u i
      · obtain ⟨i,lt,ne⟩ := prior
        obtain ⟨y,ly,ey,sy⟩ := ih i lt ne
        exact ⟨y,by omega,ey,sy⟩
      · exact ⟨x,Nat.le_refl _,hx,fun i hi => Classical.byContradiction (fun ne => prior ⟨i,hi,ne⟩)⟩
  obtain ⟨y,yu,ne,near⟩ := first u far
  have dy : d<y := by
    by_cases yes : y≤d
    · exact False.elim (ne (same_window (ws.trans wu.symm) y (by omega)))
    · omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show y≠0 by omega)
  have clk := same_clock c T P per s u (by omega) (by omega) (ps.trans pu.symm)
  have startE (i : Nat) (hi : i≤h+8) : east c s i=east c u i := same_window (es.trans eu.symm) i (by omega)
  obtain ⟨mult,lm⟩ := aligned_lag T P s u (by omega) (by omega) (ps.trans pu.symm)
  have locked (i : Nat) (late : T≤i) : c (u-s+i)=c i := by
    rw [lm,Nat.add_comm];exact period_mul c T P per mult i late
  have hit := ballistic c black k s u clk near ne
  exact ⟨s,u,k,by omega,by omega,by omega,ps.trans pu.symm,rs,ru,startE,by omega,by omega,
    fun i hi => near i (by omega),ne,hit.1,hit.2,joint_founder c T h s u k (by omega) (by omega) locked clk mark black join ne startE hit.2⟩

/-- Orient one selected arm of the actual split. The other arm is
present in the claim but its eastern label is unrestricted. -/
def Arm (c : Trace) (T P d h t v : Nat) : Prop :=
  ∃ s u k, Matched c T P d h s u (k+1) ∧
    ((t=s+k ∧ v=u+k) ∨ (t=u+k ∧ v=s+k))

private theorem arm_stamp (c : Trace) (T P d h t v : Nat)
    (period : ∀t,T≤t → c (t+P)=c t) (arm : Arm c T P d h t v) :
    c t=c v ∧ whiteNeed c t=whiteNeed c v ∧ c (t+1)=false ∧ c (v+1)=false ∧
      need c (t+1)≠need c (v+1) := by
  obtain ⟨s,u,k,m,pair⟩ := arm
  have clk := same_clock c T P period s u m.mature (Nat.le_trans m.mature (Nat.le_of_lt m.ordered)) m.phase
  have start := clk k
  have nxt : c (s+k+1)=c (u+k+1) := by simpa only [Nat.add_assoc] using clk (k+1)
  have old := m.common k (by omega)
  have split : whiteNeed c (s+k+1)≠whiteNeed c (u+k+1) := by simpa only [Nat.add_assoc] using m.split
  have white : c (u+k+1)=false := by
    cases z : c (u+k+1)
    · rfl
    · exact False.elim (split (by simp [whiteNeed,nxt,z]))
  have whiteS := nxt.trans white
  have unequal : need c (s+k+1)≠need c (u+k+1) := by
    simpa only [whiteNeed,whiteS,white,Bool.not_false,Bool.true_and] using split
  rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨start,old,whiteS,white,unequal⟩
  · exact ⟨start.symm,old.symm,white,whiteS,Ne.symm unequal⟩

/-- Six cells to the right of a held black wall; the seventh is free at
each step. The recursive predicate quantifies over both possible inputs. -/
private abbrev Band := Bool × Bool × Bool × Bool × Bool × Bool
private def advance (w : Band) (r : Bool) : Band :=
  let (a,b,d,e,f,g) := w
  (rule true a b, rule a b d, rule b d e, rule d e f, rule e f g, rule f g r)
private def freezes : Nat → Band → Bool
  | 0,w => !w.1 && w.2.1
  | n+1,w => freezes n (advance w false) && freezes n (advance w true)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 2500 in
private theorem freezes_nine : ∀ a b d e f g : Bool, freezes 9 (a,b,d,e,f,g)=true := by decide

private def band (c : Trace) (t x : Nat) : Band :=
  (east c t (x+1),east c t (x+2),east c t (x+3),east c t (x+4),east c t (x+5),east c t (x+6))

private theorem freezes_real (c : Trace) (x n t : Nat)
    (yes : freezes n (band c t x)=true) (held : ∀ i,i<n → east c (t+i) x=true) :
    east c (t+n) (x+1)=false ∧ east c (t+n) (x+2)=true := by
  induction n generalizing t with
  | zero => simpa [freezes,band] using yes
  | succ n ih =>
    have now := held 0 (by omega)
    simp only [Nat.add_zero] at now
    have next : band c (t+1) x=advance (band c t x) (east c t (x+7)) := by
      simp [band,advance,east,now]
    have pair := Bool.and_eq_true_iff.mp yes
    have guard : freezes n (band c (t+1) x)=true := by
      rw [next];cases b : east c t (x+7)
      · exact pair.1
      · exact pair.2
    have z := ih (t+1) guard (fun i li => by
      rw [show t+1+i=t+(i+1) by omega];exact held (i+1) (by omega))
    rwa [show t+1+n=t+(n+1) by omega] at z

/-- A held-black physical cell is a new wall, two places farther east
after nine ticks. No assumption on the cells ahead of that wall. -/
theorem black_pair (c : Trace) (x t : Nat)
    (held : ∀ i,i<9 → east c (t+i) x=true) :
    east c (t+9) (x+1)=false ∧ east c (t+9) (x+2)=true :=
  freezes_real c x 9 t (freezes_nine _ _ _ _ _ _) held

private def Ready (c : Trace) (b : Nat) : Prop :=
  east c b 1=true ∧ east c b 2=false ∧ east c b 3=true

private theorem head_hold (c : Trace) (t n : Nat) (one : east c t 1=true)
    (white : ∀ i,i<n → c (t+i)=false) : east c (t+n) 1=true := by
  induction n with
  | zero => exact one
  | succ n ih =>
    change rule (east c (t+n) 0) (east c (t+n) 1) (east c (t+n) 2)=true
    rw [east0,white n (by omega),ih (fun i hi => white i (by omega))]
    rfl

private theorem rise3 (c : Trace) (b : Nat) (black : c b=true)
    (rd : Ready c b) (w1 : c (b+1)=false) (w2 : c (b+2)=false) :
    east c (b+1) 1=false ∧ east c (b+2) 1=false ∧ east c (b+3) 1=true := by
  obtain ⟨r1,r2,r3⟩ := rd
  have a : east c (b+1) 1=false := by change rule (east c b 0) _ _=_;rw [east0,black,r1];rfl
  have f : east c (b+1) 2=false := by change rule (east c b 1) _ _=_;rw [r1,r2,r3];rfl
  have g : east c (b+1) 3=true := by change rule (east c b 2) _ _=_;rw [r2,r3];rfl
  have a' : east c (b+2) 1=false := by change rule (east c (b+1) 0) _ _=_;rw [east0,w1,a,f];rfl
  have f' : east c (b+2) 2=true := by change rule (east c (b+1) 1) _ _=_;rw [a,f,g];rfl
  exact ⟨a,a',by change rule (east c (b+2) 0) _ _=_;rw [east0,w2,a',f'];rfl⟩

private theorem between_pulses (c : Trace) (b n : Nat) (gap : 12≤n)
    (black : c b=true) (rd : Ready c b)
    (whites : ∀ i,0<i → i<n → c (b+i)=false) :
    Ready c (b+n) ∧ ∀ i,0<i → i<n → east c (b+i) 1=decide (3≤i) := by
  obtain ⟨lo,mid,hi⟩ := rise3 c b black rd (whites 1 (by omega) (by omega)) (whites 2 (by omega) (by omega))
  have on (i : Nat) (li : 3≤i) (le : i≤n) : east c (b+i) 1=true := by
    have z := head_hold c (b+3) (i-3) hi (fun j hj => by
      rw [show b+3+j=b+(3+j) by omega];exact whites _ (by omega) (by omega))
    rwa [show b+3+(i-3)=b+i by omega] at z
  have f := black_pair c 1 (b+n-9) (fun i li => by
    rw [show b+n-9+i=b+(n-9+i) by omega];exact on _ (by omega) (by omega))
  rw [show b+n-9+9=b+n by omega] at f
  refine ⟨⟨on n (by omega) (by omega),f⟩,?_⟩
  intro i pos lt
  by_cases ge : 3≤i
  · simpa [ge] using on i ge (by omega)
  · rcases (show i=1 ∨ i=2 by omega) with rfl|rfl
    · exact lo
    · exact mid

/-- The clock after the designated cut consists of single black pulses
with arbitrary intervening lengths at least eleven. The entering 101
is a three-cell physical condition, not a condition on future reads. -/
def PulseBasin (c : Trace) : Prop :=
  ∃ f : Nat → Nat, Ready c (f 0) ∧ ∀ k,
    c (f k)=true ∧ f k+12≤f (k+1) ∧
    ∀ i,f k<i → i<f (k+1) → c i=false

private theorem pulse_mask (c : Trace) (f : Nat → Nat) (rd : Ready c (f 0))
    (seq : ∀ k,c (f k)=true ∧ f k+12≤f (k+1) ∧
      ∀ i,f k<i → i<f (k+1) → c i=false) (join : Joined c) :
    ∀ t,f 0≤t → whiteNeed c t= !(c t || c (t-1) || c (t-2)) := by
  have jump (k : Nat) (ready : Ready c (f k)) :=
    between_pulses c (f k) (f (k+1)-f k) (by have := (seq k).2.1;omega) (seq k).1
      ready (fun i li hi => (seq k).2.2 _ (by omega) (by omega))
  have ready (k : Nat) : Ready c (f k) := by
    induction k with
    | zero => exact rd
    | succ k ih =>
      have h := (jump k ih).1
      rwa [Nat.add_sub_of_le (by have := (seq k).2.1;omega : f k≤f (k+1))] at h
  have cover (n : Nat) : ∃ k,f k≤f 0+n ∧ f 0+n<f (k+1) := by
    induction n with
    | zero => exact ⟨0,by omega,by have := (seq 0).2.1;omega⟩
    | succ n ih =>
      obtain ⟨k,lo,hi⟩ := ih
      by_cases still : f 0+(n+1)<f (k+1)
      · exact ⟨k,by omega,still⟩
      · exact ⟨k+1,by omega,by have := (seq (k+1)).2.1;omega⟩
  intro t ht
  obtain ⟨k,lo,hi⟩ := cover (t-f 0)
  rw [Nat.add_sub_of_le ht] at lo hi
  by_cases atPulse : t=f k
  · simp [whiteNeed,atPulse,(seq k).1]
  · have w := (seq k).2.2 t (by omega) hi
    have eq := (jump k (ready k)).2 (t-f k) (by omega) (by omega)
    rw [Nat.add_sub_of_le lo] at eq
    simp only [whiteNeed,w,Bool.not_false,Bool.true_and,join t w,eq,Bool.false_or]
    by_cases mid : f k+3≤t
    · have w1 := (seq k).2.2 (t-1) (by omega) (by omega)
      have w2 := (seq k).2.2 (t-2) (by omega) (by omega)
      simp [w1,w2,show 3≤t-f k by omega]
    · rcases (show t-1=f k ∨ t-2=f k by omega) with e|e
      · simp [e,(seq k).1,show ¬3≤t-f k by omega]
      · simp [e,(seq k).1,show ¬3≤t-f k by omega]

/-- The west mark forbids every periodic trace entering this basin. The
gap sequence need not be constant; knowledge of three wall bits is
enough to recover every mature masked east output. -/
theorem excludes_pulse_basin (c : Trace) (mark : c 0=true) (ep : EventuallyPeriodic c)
    (black : BlackLock c) (join : Joined c) : ¬PulseBasin c := by
  rintro ⟨f,rd,seq⟩
  have reads := pulse_mask c f rd seq join
  apply west_rich c mark ep black
  obtain ⟨T,P,hp,per⟩ := ep
  refine ⟨T+f 0+2,P,hp,?_⟩
  intro t ht
  rw [reads (t+P) (by omega),reads t (by omega),per t (by omega),
    show t+P-1=(t-1)+P by omega,per (t-1) (by omega),
    show t+P-2=(t-2)+P by omega,per (t-2) (by omega)]


/- Arbitrary normalized front: unlike the singleton's fixed left rim,
the strict right tape carried by this front at its birth is unrestricted. -/
namespace RenewalFront
variable (side : Nat → Int → Bool)
variable (law : ∀ t j, side (t+1) j=rule (side t (j-2)) (side t (j-1)) (side t j))
variable (vac : ∀ t j,j<0 → side t j=false) (root : ∀ t,side t 0=true)
/-- Sideways left recovery holds for any two time offsets and any spatial displacement. -/
private def LaneEq (A B : Nat) (k j : Int) : Prop :=
  ∀ t, side (A+t) j=side (B+t) (j+k)

private theorem xor_injective (a b c : Bool) :
    xor a c=xor b c → a=b := by
  cases a <;> cases b <;> cases c <;> decide

include law in
private theorem rewind {A B : Nat} {k j : Int}
    (here : LaneEq side A B k j) (next : LaneEq side A B k (j+1)) :
    LaneEq side A B k (j-1) := by
  intro t
  have obs := next (t+1)
  rw [show A+(t+1)=A+t+1 by omega,show B+(t+1)=B+t+1 by omega,
    law,law,
    show j+1-1=j by omega,show j+1-2=j-1 by omega,
    show j+1+k-1=j+k by omega,show j+1+k-2=j-1+k by omega,
    ←here t,←next t] at obs
  exact xor_injective _ _ _ obs

include law in
private theorem rewind_all {A B : Nat} {k j : Int}
    (here : LaneEq side A B k j) (next : LaneEq side A B k (j+1)) :
    ∀ i≤j+1, LaneEq side A B k i := by
  intro i hi
  have recPair : ∀ n : Nat, LaneEq side A B k (j-n) ∧ LaneEq side A B k (j-n+1) := by
    intro n
    induction n with
    | zero => simpa using And.intro here next
    | succ n ih =>
      refine ⟨?_,?_⟩
      · rw [show j-(↑(n+1):Int)=j-(n:Int)-1 by omega]
        exact rewind side law ih.1 ih.2
      · rw [show j-(↑(n+1):Int)+1=j-(n:Int) by omega]
        exact ih.1
  by_cases e : i=j+1
  · exact e ▸ next
  · have q : j-((j-i).toNat:Int)=i := by omega
    rw [←q]
    exact (recPair _).1

include law vac root in
/-- No two distinct adjacent normalized-west lane pairs have the same
complete later trajectory, even allowing independent temporal shifts.
The exact all-time occupied left edge is a spatial boundary marker. -/
private theorem no_repeated_lane_pair (A B : Nat) (j k : Int) (d : 0<k) (hj : -k≤j+1)
    (here : LaneEq side A B k j) (next : LaneEq side A B k (j+1)) : False := by
  have e := rewind_all side law here next (-k) hj 0
  simp only [Nat.add_zero,show -k+k=0 by omega] at e
  rw [vac A _ (by omega),root] at e
  exact Bool.noConfusion e

open FiniteWindowRecurrence QuantifiedSplit

private theorem from_return {Q p : Nat} {x : Int}
    (h : ∀ t, side (Q+t+p) x=side (Q+t) x) (m r : Nat) :
    side (Q+r+p*m) x=side (Q+r) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ,←Nat.add_assoc,show Q+r+p*m=Q+(r+p*m) by omega,h,
      ←Nat.add_assoc,ih]

include law vac root in
/-- Adjacent lane pairs have unbounded eventual time periods. If two
neighboring normalized-west lanes at depth m simultaneously inherit the
same period p, then their p-tick certificates identify every earlier
aligned lane pair as a different word of length 2*p. -/
private theorem periodic_pair_width_bound (m A p : Nat) (hp : 0<p)
    (lo : ∀ t≥A, side (t+p) (m:Int)=side t (m:Int))
    (hi : ∀ t≥A, side (t+p) ((m:Int)+1)=side t ((m:Int)+1)) :
    m<2^(p+p) := by
  have hLo : LaneEq side (A+p) A 0 (m:Int) := by
    intro t
    simpa [Nat.add_comm p t,Nat.add_assoc] using lo (A+t) (by omega)
  have hHi : LaneEq side (A+p) A 0 ((m:Int)+1) := by
    intro t
    simpa [Nat.add_comm p t,Nat.add_assoc] using hi (A+t) (by omega)
  have allP (x : Int) (hx : x≤(m:Int)+1) (t : Nat) :
      side (A+t+p) x=side (A+t) x := by
    have h := rewind_all side law hLo hHi x hx t
    simpa [Nat.add_comm p t,Nat.add_assoc] using h
  apply Classical.byContradiction
  intro notSmall
  have large : 2^(p+p)≤m := by omega
  let f (d i : Nat) := if i<p then side (A+i) (d:Int) else side (A+(i-p)) ((d:Int)+1)
  let w (d : Nat) := window (f d) (p+p) 0
  let key (d : Nat) := encode (w d)
  have cap (d : Nat) : key d<2^(p+p) := by
    simpa only [key,w,window_len] using encode_bound (w d)
  obtain ⟨i,j,lt,jb,eq⟩ := repeat_le (2^(p+p)) key (by intro d _; exact cap d)
  have words : w i=w j := same_encode_eq (by simp [w,window_len]) eq
  have cells (r : Nat) (hr : r<p+p) : f i r=f j r := by
    have g := congrArg (fun xs : List Bool => xs[r]?) words
    simpa [w,window,hr] using g
  let k : Int := (j:Int)-i
  have smalli : i≤m := by omega
  have smallj : j≤m := by omega
  have iShift : (i:Int)+k=(j:Int) := by dsimp [k]; omega
  have sShift : (i:Int)+1+k=(j:Int)+1 := by dsimp [k]; omega
  have same0 : LaneEq side A A k (i:Int) := by
    intro t
    let r := t%p
    let q := t/p
    have d : t=r+p*q := by exact (Nat.mod_add_div t p).symm
    have low : r<p := Nat.mod_lt t hp
    rw [iShift,d,←Nat.add_assoc,
      from_return side (allP _ (by omega)) q r,from_return side (allP _ (by omega)) q r]
    have e := cells r (by omega)
    simpa [f,low] using e
  have same1 : LaneEq side A A k ((i:Int)+1) := by
    intro t
    let r := t%p
    let q := t/p
    have d : t=r+p*q := by exact (Nat.mod_add_div t p).symm
    have low : r<p := Nat.mod_lt t hp
    rw [sShift,d,←Nat.add_assoc,
      from_return side (allP _ (by omega)) q r,from_return side (allP _ (by omega)) q r]
    have e := cells (p+r) (by omega)
    simpa [f,show ¬p+r<p by omega,show p+r-p=r by omega] using e
  exact no_repeated_lane_pair side law vac root A A (i:Int) k (by dsimp [k]; omega)
    (by dsimp [k]; omega) same0 same1


include law vac in
open FiniteWindowRecurrence Quantified…5312 tokens truncated…rem renewal (c : Trace) (s h m : Nat) (ml : 0<m) (long : bridgeH m≤h)
    (wh : ∀ j,j<h → c (s+j)=false) (black : c (s+h)=true) :
    ∃ y,0<y ∧ y≤bridgeK m ∧ east c (s+h+m) y=true := by
  have mcap : m+2≤bridgeK m := by unfold bridgeK;omega
  by_cases any : ∃ k,0<k ∧ k≤h+2*m ∧ east c s k=true
  · obtain ⟨d,pos,le,hit,clear⟩ := first_in c s (h+2*m) any
    by_cases early : d+9*(m+2)≤h
    · obtain ⟨y,p,k,e⟩ := checker_content _ _ m (early_checker c s h d m pos early wh clear hit)
      exact ⟨y,p,by omega,e⟩
    · obtain ⟨j,lo,hi,on⟩ := active_lane (free c s d) (fun _ _ => rfl)
        (free_vac c s d) (free_mark c s d hit) (bridgeJ m)
      have cap : 2^(laneCap (bridgeJ m)+3)≤h :=
        Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) long
      have now := on (h+m) (by omega)
      let x := j+d-(h+m)
      have bound : 24*m+48≤j := lo
      have eq := bridge_free c s h d wh clear (h+m) x (by dsimp [x];omega) (by dsimp [x];omega)
      rw [show ((x:Int)+(h+m:Nat)-d)=(j:Int) by dsimp [x];omega,now] at eq
      exact ⟨x,by dsimp [x];omega,by dsimp [x,bridgeK];omega,by simpa [Nat.add_assoc] using eq⟩
  · have empty (i : Nat) (pi : 0<i) (u : i≤h+2*m) : east c s i=false := by
      cases z : east c s i
      · rfl
      · exact False.elim (any ⟨i,pi,u,z⟩)
    have zero := white_triangle c s h (h+2*m) wh empty h (by omega)
    exact ⟨m,ml,by omega,first_flash c (s+h) m black (fun i pi z => zero _ pi (by omega))⟩

private theorem cap_mono {a b : Nat} (le : a≤b) : laneCap a≤laneCap b := by
  have low := Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add_right le 2)
  exact Nat.add_le_add (Nat.add_le_add_right le 2)
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add low low))

private theorem k_mono {a b : Nat} (le : a≤b) : bridgeK a≤bridgeK b := by
  have z := cap_mono (a:=bridgeJ a) (b:=bridgeJ b) (by unfold bridgeJ;omega)
  unfold bridgeK;omega

private theorem h_mono {a b : Nat} (le : a≤b) : bridgeH a≤bridgeH b := by
  have z := cap_mono (a:=bridgeJ a) (b:=bridgeJ b) (by unfold bridgeJ;omega)
  have p := Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add_right z 3)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add p (k_mono le))
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right le 2))) 1

private theorem space {m : Nat} : bridgeK m+9*(m+2)≤bridgeH m :=
  Nat.le_trans (Nat.add_le_add_right (Nat.le_add_left _ _) _) (Nat.le_add_right _ _)

private theorem white_profile (c : Trace) (s h d : Nat) (pos : 0<d)
    (wh : ∀ j,j<h → c (s+j)=false) (clear : ∀ y,0<y → y<d → east c s y=false)
    (hit : east c s d=true) (i : Nat) (il : i≤h) :
    east c (s+i) 1=decide (d≤i+1) := by
  by_cases arrived : d≤i+1
  · rw [decide_eq_true arrived]
    have first := compare_free c s h d wh clear (d-1) (by omega) 1 (by omega) (Or.inl (by omega))
    rw [show ((1:Nat):Int)+(d-1:Nat)-d=0 by omega,free_mark c s d hit] at first
    have z := head_hold c (s+(d-1)) (i-(d-1)) first (fun j lt => by
      rw [show s+(d-1)+j=s+(d-1+j) by omega];exact wh _ (by omega))
    rwa [show s+(d-1)+(i-(d-1))=s+i by omega] at z
  · rw [decide_eq_false arrived]
    exact (compare_free c s h d wh clear i il 1 (by omega) (Or.inl (by omega))).trans
      (free_vac c s d i _ (by omega))

private theorem compare_band (c : Trace) (s u width : Nat)
    (clk : ∀ i,c (s+i)=c (u+i)) (old : CheckerAt c s width) (newer : CheckerAt c u width) :
    ∀ i x,x+i≤width → east c (s+i) x=east c (u+i) x := by
  intro i
  induction i with
  | zero =>
    intro x le
    cases x with
    | zero => simpa [east0] using clk 0
    | succ x => exact (old _ (by omega) le).trans (newer _ (by omega) le).symm
  | succ i ih =>
    intro x le
    cases x with
    | zero => simpa [east0] using clk (i+1)
    | succ x =>
      change rule (east c (s+i) x) (east c (s+i) (x+1)) (east c (s+i) (x+2))=
        rule (east c (u+i) x) (east c (u+i) (x+1)) (east c (u+i) (x+2))
      rw [ih x (by omega),ih (x+1) (by omega),ih (x+2) (by omega)]

/-- Only the shorter bridge consumes checker width. The following long
white interval can then have any length: its first occupied position
determines all of its raw head reads and restores the whole checker. -/
private theorem paired_bridge (c : Trace) (m s u n h : Nat) (bound : n≤m)
    (long : m+2+9*(m+2)≤h) (wh : ∀ j,j<h → c (s+n+j)=false)
    (clk : ∀ i,c (s+i)=c (u+i))
    (old : CheckerAt c s (2*m+4)) (newer : CheckerAt c u (2*m+4)) :
    (CheckerAt c (s+n+h) (2*m+4) ∧ CheckerAt c (u+n+h) (2*m+4)) ∧
    ∀ i,i<n+h → east c (s+i) 1=east c (u+i) 1 := by
  have band := compare_band c s u _ clk old newer
  obtain ⟨x,xp,xb,hit⟩ := checker_content c s n (fun k pk le => old k pk (by omega))
  obtain ⟨d,dp,dx,yes,zero⟩ := first_in c (s+n) x ⟨x,xp,by omega,hit⟩
  have right : east c (u+n) d=true := (band n d (by omega)).symm.trans yes
  have zeros (y : Nat) (yp : 0<y) (yl : y<d) : east c (u+n) y=false :=
    (band n y (by omega)).symm.trans (zero _ yp yl)
  have whites (j : Nat) (lt : j<h) : c (u+n+j)=false := by
    rw [Nat.add_assoc,←clk,←Nat.add_assoc];exact wh j lt
  have room : d+9*(m+2)≤h := by omega
  refine ⟨⟨early_checker c (s+n) h d m dp room wh zero yes,
    early_checker c (u+n) h d m dp room whites zeros right⟩,?_⟩
  intro i lt
  by_cases before : i<n
  · exact band i 1 (by omega)
  · have a := white_profile c (s+n) h d dp wh zero yes (i-n) (by omega)
    have b := white_profile c (u+n) h d dp whites zeros right (i-n) (by omega)
    rw [show s+n+(i-n)=s+i by omega] at a
    rw [show u+n+(i-n)=u+i by omega] at b
    exact a.trans b.symm

private def ShortOrSolid (c : Trace) (m s n : Nat) : Prop :=
  n≤m ∨ (9≤n ∧ ∀ i,i<n → c (s+i)=true)

private theorem after_solid (c : Trace) (s n : Nat) (long : 9≤n)
    (solid : ∀ i,i<n → c (s+i)=true) :
    east c (s+n) 1=false ∧ east c (s+n) 2=true := by
  have p := black_pair c 0 (s+n-9) (fun i lt => by
    rw [east0,show s+n-9+i=s+(n-9+i) by omega];exact solid _ (by omega))
  rwa [show s+n-9+9=s+n by omega] at p

private theorem paired_span (c : Trace) (m s u n h : Nat) (kind : ShortOrSolid c m s n)
    (long : m+2+9*(m+2)≤h) (wh : ∀ j,j<h → c (s+n+j)=false)
    (clk : ∀ i,c (s+i)=c (u+i))
    (old : CheckerAt c s (2*m+4)) (newer : CheckerAt c u (2*m+4)) :
    (CheckerAt c (s+n+h) (2*m+4) ∧ CheckerAt c (u+n+h) (2*m+4)) ∧
    ∀ i,i<n+h → c (s+i)=false → east c (s+i) 1=east c (u+i) 1 := by
  rcases kind with bound|⟨sz,solid⟩
  · obtain ⟨r,eq⟩ := paired_bridge c m s u n h bound long wh clk old newer
    exact ⟨r,fun i hi _ => eq i hi⟩
  have first := after_solid c s n sz solid
  have twin := after_solid c u n sz (fun j lj => (clk j).symm.trans (solid j lj))
  have whites (j : Nat) (lt : j<h) : c (u+n+j)=false := by
    rw [Nat.add_assoc,←clk,←Nat.add_assoc];exact wh j lt
  have room : 2+9*(m+2)≤h := by omega
  have z (s' : Nat) (v : east c s' 1=false) (y : Nat) (yp : 0<y) (yl : y<2) :
      east c s' y=false := by rwa [show y=1 by omega]
  refine ⟨⟨early_checker c (s+n) h 2 m (by decide) room wh (z _ first.1) first.2,
    early_checker c (u+n) h 2 m (by decide) room whites (z _ twin.1) twin.2⟩,?_⟩
  intro i lt white
  have after : n≤i := by
    by_cases before : i<n
    · have z := solid i before;simp_all
    · omega
  have a := white_profile c (s+n) h 2 (by decide) wh (z _ first.1) first.2 (i-n) (by omega)
  have b := white_profile c (u+n) h 2 (by decide) whites (z _ twin.1) twin.2 (i-n) (by omega)
  rw [show s+n+(i-n)=s+i by omega] at a
  rw [show u+n+(i-n)=u+i by omega] at b
  exact a.trans b.symm

/-- A clock language, not an east-state hypothesis. Each arbitrary
positive bridge begins black; solid-black bridges of at least nine
steps may have unbounded length. Widths and white gaps may vary at every
occurrence; no periodicity of the chosen decomposition is assumed. -/
def Bridged (c : Trace) : Prop :=
  ∃ m : Nat, ∃ f n h : Nat → Nat, ∀ k,c (f k)=true ∧ 0<n k ∧ ShortOrSolid c m (f k) (n k) ∧
    bridgeH m≤h k ∧ f k+n k+h k=f (k+1) ∧ ∀ j,j<h k → c (f k+n k+j)=false

private def LinearTiles (c : Trace) (m : Nat) (f n h : Nat → Nat) : Prop :=
  ∀ k,c (f k)=true ∧ 0<n k ∧ ShortOrSolid c m (f k) (n k) ∧
    m+2+9*(m+2)≤h k ∧ f k+n k+h k=f (k+1) ∧ ∀ j,j<h k → c (f k+n k+j)=false

private theorem reject_checkpoints (c : Trace) (ep : EventuallyPeriodic c) (mark : c 0=true)
    (black : BlackLock c) (join : Joined c) (m : Nat) (f n h : Nat → Nat)
    (seq : LinearTiles c m f n h)
    (allcheck : ∀ k,CheckerAt c (f (k+2)) (2*m+4)) : False := by
  have advance (k : Nat) : f k<f (k+1) := by
    obtain ⟨_,p,_,_,ends,_⟩ := seq k;omega
  have many (a k : Nat) : f a+k≤f (a+k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      change f a+k+1≤f (a+k+1)
      exact Nat.le_trans (Nat.succ_le_succ ih) (advance (a+k))
  obtain ⟨T,P,hp,per⟩ := ep
  let idx (i : Nat) := T+i+2
  obtain ⟨a,b,lt,_,ph⟩ := QuantifiedSplit.repeat_le P (fun i => (f (idx i)-T)%P) (fun i _ => Nat.mod_lt _ hp)
  let A := f (idx a)
  let B := f (idx b)
  let Q := B-A
  have tA : T≤A := by have := many 0 (idx a);dsimp [A,idx] at *;simp at *;omega
  have ab : A<B := by
    have z := many (idx a) (idx b-idx a)
    have eq : idx a+(idx b-idx a)=idx b := by dsimp [idx];omega
    rw [eq] at z;dsimp [A,B];have lt' : idx a<idx b := by dsimp [idx];omega
    omega
  have atB : A+Q=B := by dsimp [Q];omega
  have align := same_clock c T P per A B tA (by omega) ph
  have later (t : Nat) (late : A≤t) : c t=c (t+Q) := by
    have z := align (t-A);rwa [show A+(t-A)=t by omega,show B+(t-A)=t+Q by omega] at z
  have older (k : Nat) := allcheck (T+a+k)
  have shift (k : Nat) : T+a+k+2=idx a+k := by dsimp [idx];omega
  have joinedChecks (k : Nat) : CheckerAt c (f (idx a+k)+Q) (2*m+4) := by
    induction k with
    | zero => change CheckerAt c (A+Q) _;rw [atB];exact allcheck (T+b)
    | succ k ih =>
      let q := idx a+k
      obtain ⟨_,_,bound,long,ends,wh⟩ := seq q
      have ca : CheckerAt c (f q) (2*m+4) := by simpa [shift k,q] using older k
      have start : A≤f q := by have := many (idx a) k;dsimp [q,A] at *;omega
      have step := paired_span c m (f q) (f q+Q) (n q) (h q) bound long wh
        (fun i => by rw [show f q+Q+i=f q+i+Q by omega];exact later _ (by omega)) ca ih
      rw [show f q+Q+n q+h q=f (q+1)+Q by omega] at step
      exact step.1.2
  have cover (t : Nat) (late : A≤t) : ∃ k,f (idx a+k)≤t ∧ t<f (idx a+k+1) := by
    have all (r : Nat) : ∃ k,f (idx a+k)≤A+r ∧ A+r<f (idx a+k+1) := by
      induction r with
      | zero => exact ⟨0,by simp [A],by simpa [A] using advance (idx a)⟩
      | succ r ih =>
        obtain ⟨k,l,u⟩ := ih
        by_cases ok : A+(r+1)<f (idx a+k+1)
        · exact ⟨k,by omega,ok⟩
        · exact ⟨k+1,by rw [←Nat.add_assoc];omega,by
            have := advance (idx a+k+1);rw [←Nat.add_assoc (idx a) k 1];omega⟩
    simpa [Nat.add_sub_of_le late] using all (t-A)
  apply west_rich c mark ⟨T,P,hp,per⟩ black
  refine ⟨A,Q,by dsimp [Q];omega,?_⟩
  intro t late
  have ct := later t late
  obtain ⟨k,lo,hi⟩ := cover t late
  let q := idx a+k
  obtain ⟨_,_,bound,long,ends,wh⟩ := seq q
  have start : A≤f q := by have := many (idx a) k;dsimp [q,A] at *;omega
  have ca : CheckerAt c (f q) (2*m+4) := by simpa [shift k,q] using older k
  have step := paired_span c m (f q) (f q+Q) (n q) (h q) bound long wh
    (fun i => by rw [show f q+Q+i=f q+i+Q by omega];exact later _ (by omega)) ca (joinedChecks k)
  change f q≤t at lo;change t<f (q+1) at hi
  have e := step.2 (t-f q) (by omega)
  rw [show f q+(t-f q)=t by omega,show f q+Q+(t-f q)=t+Q by omega] at e
  cases val : c t with
  | false => simp [whiteNeed,←ct,val,join t,join (t+Q),e val]
  | true => simp [whiteNeed,←ct,val]

theorem excludes_bridged (c : Trace) (ep : EventuallyPeriodic c) (mark : c 0=true)
    (black : BlackLock c) (join : Joined c) : ¬Bridged c := by
  rintro ⟨m,f,n,h,seq⟩
  have allcheck (k : Nat) : CheckerAt c (f (k+2)) (2*m+4) := by
    obtain ⟨_,_,_,long,ends,wh⟩ := seq k
    obtain ⟨bk,l,b,long',ends',wh'⟩ := seq (k+1)
    obtain ⟨y,yp,yb,hit⟩ : ∃ y,0<y ∧ y≤bridgeK m ∧ east c (f (k+1)+n (k+1)) y=true := by
      rcases b with b|⟨sz,solid⟩
      · have longn := Nat.le_trans (h_mono b) long
        obtain ⟨y,p,le,e⟩ := renewal c (f k+n k) (h k) (n (k+1)) l longn wh (by rw [ends];exact bk)
        rw [ends] at e;exact ⟨y,p,Nat.le_trans le (k_mono b),e⟩
      · exact ⟨2,by decide,by unfold bridgeK;omega,(after_solid c _ _ sz solid).2⟩
    obtain ⟨d,dp,dy,yes,zero⟩ := first_in c _ y ⟨y,yp,by omega,hit⟩
    have total : d+9*(m+2)≤h (k+1) := by have := Nat.le_trans (space (m:=m)) long';omega
    rw [←ends'];exact early_checker _ _ _ _ _ dp total wh' zero yes
  apply reject_checkpoints c ep mark black join m f n h _ allcheck
  intro k;obtain ⟨bk,p,kind,long,ends,wh⟩ := seq k
  have cap : m+2≤bridgeK m := by unfold bridgeK;omega
  exact ⟨bk,p,kind,Nat.le_trans (Nat.add_le_add_right cap _) (Nat.le_trans space long),ends,wh⟩

/-- On the affine-length tiling, a single real early arrival is
sufficient. No lower bound on density or recurrence of such arrivals. -/
private theorem reject_early (c : Trace) (ep : EventuallyPeriodic c) (mark : c 0=true)
    (black : BlackLock c) (join : Joined c) (m : Nat) (f n h : Nat → Nat)
    (seq : LinearTiles c m f n h) (k d : Nat) (dp : 0<d)
    (room : d+9*(m+2)≤h k) (hit : east c (f k+n k) d=true) : False := by
  obtain ⟨e,pe,le,yes,zero⟩ := first_in c _ d ⟨d,dp,by omega,hit⟩
  obtain ⟨_,_,_,_,ends,wh⟩ := seq k
  have ready := early_checker c (f k+n k) (h k) e m pe (by omega) wh zero yes
  rw [ends] at ready
  have more (r : Nat) : CheckerAt c (f (k+1+r)) (2*m+4) := by
    induction r with
    | zero => exact ready
    | succ r ih =>
      obtain ⟨_,_,kind,long,ends,wh⟩ := seq (k+1+r)
      have z := paired_span c m (f (k+1+r)) (f (k+1+r)) _ _ kind long wh (fun _ => rfl) ih ih
      rw [ends] at z;exact z.1.1
  exact reject_checkpoints c ep mark black join m (fun r => f (k+1+r))
    (fun r => n (k+1+r)) (fun r => h (k+1+r)) (fun r => seq _) (fun r => more (r+2))

/-- All black intervals are solid and unrestricted in length. The
white intervals need only 100 steps, independent of the period or the
number of black intervals. -/
def PulseWindows (c : Trace) : Prop :=
  ∃ f n h : Nat → Nat, ∀ k, 0<n k ∧ 100≤h k ∧ f k+n k+h k=f (k+1) ∧
    (∀ i,i<n k → c (f k+i)=true) ∧ (∀ j,j<h k → c (f k+n k+j)=false)

private theorem mild_tiles (c : Trace) (f n h : Nat → Nat)
    (w : ∀ k, 0<n k ∧ 100≤h k ∧ f k+n k+h k=f (k+1) ∧
      (∀ i,i<n k → c (f k+i)=true) ∧ (∀ j,j<h k → c (f k+n k+j)=false)) :
    LinearTiles c 8 f n h := by
  intro k
  obtain ⟨b,l,e,solid,wh⟩ := w k
  refine ⟨by simpa using solid 0 b,b,?_,l,e,wh⟩
  by_cases short : n k≤8
  · exact Or.inl short
  · exact Or.inr ⟨by omega,solid⟩

/-- A true late fall in this clock class always has ten vacant head
cells at the first white (indeed the forbidden depth is h-90). This
tests the same first-white gate that the exceptional L1 arm must split. -/
theorem quiet_falls (c : Trace) (ep : EventuallyPeriodic c) (mark : c 0=true)
    (black : BlackLock c) (join : Joined c) (w : PulseWindows c) :
    ∃ U,∀ t,U≤t → c t=true → c (t+1)=false →
      ∀ d,0<d → d≤10 → east c (t+1) d=false := by
  obtain ⟨f,n,h,w⟩ := w
  have tiles := mild_tiles c f n h w
  have adv (k : Nat) : f k<f (k+1) := by obtain ⟨p,_,eq,_⟩ := w k;omega
  have cover (r : Nat) : ∃ k,f k≤f 0+r ∧ f 0+r<f (k+1) := by
    induction r with
    | zero => exact ⟨0,by simp,by simpa using adv 0⟩
    | succ r ih =>
      obtain ⟨k,l,u⟩ := ih
      by_cases mid : f 0+(r+1)<f (k+1)
      · exact ⟨k,by omega,mid⟩
      · exact ⟨k+1,by omega,by have := adv (k+1);omega⟩
  refine ⟨f 0,?_⟩
  intro t late old new d dp bd
  obtain ⟨k,lo,hi⟩ := cover (t-f 0)
  rw [Nat.add_sub_of_le late] at lo hi
  obtain ⟨b,l,ends,solid,wh⟩ := w k
  have pos : t<f k+n k := by
    by_cases lt : t<f k+n k
    · exact lt
    · have z := wh (t-(f k+n k)) (by omega)
      rw [Nat.add_sub_of_le (by omega)] at z
      simp_all
  have e : t+1=f k+n k := by
    by_cases before : t+1<f k+n k
    · have z := solid (t+1-f k) (by omega)
      rw [Nat.add_sub_of_le (by omega)] at z;simp_all
    · omega
  rw [e]
  cases val : east c (f k+n k) d
  · rfl
  · exact False.elim (reject_early c ep mark black join 8 f n h tiles k d dp (by omega) val)


private def record (c : Trace) (t : Nat) : Nat → List Bool
  | 0 => []
  | n+1 => east c t (n+1)::record c t n

private def reverseRecord : List Bool → Mem → List Bool × Bool
  | [],z => ([],z.2)
  | q::w,z =>
    let (row,wall) := reverseRecord w (read q z)
    (z.2::row,wall)

private theorem reverse_real (c : Trace) (t n : Nat) :
    reverseRecord (record c (t+1) n) (east c t (n+1),east c t n)=(record c t n,c t) := by
  induction n with
  | zero => simp [reverseRecord,record,east0]
  | succ n ih => simp only [record,reverseRecord,east,undo,ih]

private def precursors (v : Bool) (land : List (List Bool)) : List (List Bool) :=
  (land.flatMap (fun w =>
    ([(false,false),(false,true),(true,false),(true,true)] : List Mem).filterMap
      (fun z => let p := reverseRecord w z; if p.2=v then some p.1 else none))).eraseDups

private theorem precursor_real (c : Trace) (t n : Nat) (land : List (List Bool))
    (v : Bool) (wall : c t=v) (mem : record c (t+1) n ∈ land) :
    record c t n ∈ precursors v land := by
  rw [precursors,List.mem_eraseDups,List.mem_flatMap]
  refine ⟨_,mem,List.mem_filterMap.mpr ⟨(east c t (n+1),east c t n),?_,?_⟩⟩
  · cases east c t (n+1) <;> cases east c t n <;> decide
  · rw [reverse_real,wall];simp

private def back : Nat → Bool → List (List Bool) → List (List Bool)
  | 0,_,land => land
  | k+1,v,land => if land.isEmpty then [] else back k v (precursors v land)

private theorem back_real (c : Trace) (s width k : Nat) (v : Bool) (land : List (List Bool))
    (clock : ∀ i,i<k → c (s+i)=v) (mem : record c (s+k) width∈land) :
    record c s width∈back k v land := by
  induction k generalizing land with
  | zero => exact mem
  | succ k ih =>
    cases land with
    | nil => contradiction
    | cons w ws =>
      simp only [back,List.isEmpty_cons,Bool.false_eq_true,ite_false]
      exact ih _ (fun i lt => clock i (by omega))
        (precursor_real _ _ _ _ _ (clock k (by omega)) mem)

private theorem blank_record (c : Trace) (t n : Nat)
    (quiet : ∀ d,0<d → d≤n → east c t d=false) : record c t n=List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [record,quiet _ (by omega) (by omega),ih (fun i pos le => quiet _ pos (by omega)),List.replicate_succ]

private def compatible (h b d : Nat) : Bool :=
  !(back h false (back b true [List.replicate d false])).isEmpty

private theorem true_bridge (c : Trace) (s h b d : Nat)
    (white : ∀ i,i<h → c (s+i)=false) (black : ∀ i,i<b → c (s+h+i)=true)
    (quiet : ∀ j,0<j → j≤d → east c (s+h+b) j=false) : compatible h b d=true := by
  have land : record c (s+h+b) d∈[List.replicate d false] := by simp [blank_record c _ _ quiet]
  have had := back_real c _ d b true _ black land
  have past := back_real c s d h false _ white had
  unfold compatible;cases e : back h false (back b true [List.replicate d false]) <;> simp_all

/- The finite inverse calculation is the literal four-possible-carry
reader above. No precomputed image or host table enters the proof. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8000 in
private theorem first_width : ∀ b : Fin 9, 0<b.val → b.val≠3 → b.val≠7 →
    compatible 100 b.val 10=false := by decide

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8000 in
private theorem second_width : compatible 13 3 19=false ∧ compatible 13 7 19=false := by decide

/-- The two forced widths reinforce each other. Ten forced vacancies
allow bridge lengths 3 and 7 at most. The new seven-cell bridge cap
forces nineteen vacancies; neither length can then occur. -/
theorem excludes_windows (c : Trace) (ep : EventuallyPeriodic c) (mark : c 0=true)
    (black : BlackLock c) (join : Joined c) : ¬PulseWindows c := by
  rintro ⟨f,n,h,w⟩
  have tiles := mild_tiles c f n h w
  have zero10 (k d : Nat) (dp : 0<d) (bound : d≤10) : east c (f k+n k) d=false := by
    cases e : east c (f k+n k) d
    · rfl
    · exact False.elim (reject_early c ep mark black join 8 f n h tiles k d dp
        (by have := (w k).2.1;omega) e)
  have predecessor (k a d : Nat) (length : a≤h k)
      (quiet : ∀ j,0<j → j≤d → east c (f (k+1)+n (k+1)) j=false) :
      compatible a (n (k+1)) d=true := by
    obtain ⟨_,_,ends,_,white⟩ := w k
    obtain ⟨_,_,_,solid,_⟩ := w (k+1)
    let s := f (k+1)-a
    have align : s+a=f (k+1) := by dsimp [s];omega
    apply true_bridge c s a (n (k+1)) d
    · intro i lt;have z := white (h k-a+i) (by omega)
      rwa [show f k+n k+(h k-a+i)=s+i by omega] at z
    · rwa [align]
    · rwa [align]
  have lengths (k : Nat) : n (k+1)=3 ∨ n (k+1)=7 := by
    obtain ⟨pos,_,_,solid,_⟩ := w (k+1)
    by_cases tooLong : 9≤n (k+1)
    · have hot := (after_solid c (f (k+1)) _ tooLong solid).2
      rw [zero10 _ _ (by decide) (by decide)] at hot;contradiction
    · have real := predecessor k 100 10 (w k).2.1 (zero10 (k+1))
      by_cases three : n (k+1)=3
      · exact Or.inl three
      · by_cases seven : n (k+1)=7
        · exact Or.inr seven
        · have no := first_width ⟨n (k+1),by omega⟩ pos three seven
          exact False.elim (Bool.noConfusion (real.symm.trans no))
  let g k := f (k+1)
  let b k := n (k+1)
  let z k := h (k+1)
  have sevenTiles : LinearTiles c 7 g b z := by
    intro k
    obtain ⟨pos,sz,ends,solid,white⟩ := w (k+1)
    refine ⟨by simpa [g] using solid 0 pos,pos,Or.inl ?_,by change 90≤h (k+1);omega,
      by simpa [g,b,z,Nat.add_assoc] using ends,white⟩
    change n (k+1)≤7;have := lengths k;omega
  have newzero (d : Nat) (dp : 0<d) (le : d≤19) : east c (f 1+n 1) d=false := by
    cases e : east c (f 1+n 1) d
    · rfl
    · exact False.elim (reject_early c ep mark black join 7 g b z sevenTiles 0 d dp
        (by change d+81≤h 1;have := (w 1).2.1;omega) e)
  have real := predecessor 0 13 19 (by have := (w 0).2.1;omega) newzero
  rcases lengths 0 with e|e
  · rw [e,second_width.1] at real;contradiction
  · rw [e,second_width.2] at real;contradiction

end RenewalFront

/-- A genuine loss is measured on one complete black run between two
whites, not on the state graph of unconstrained input symbols. -/
def PairLit (c : Trace) (t : Nat) : Prop := east c t 1=true ∨ east c t 2=true

structure OddLoss (c : Trace) (w n : Nat) : Prop where
  before : c w=false
  solid : ∀ i,i<n → c (w+1+i)=true
  after : c (w+1+n)=false
  enters : east c (w+1) 1=true
  departs : ¬PairLit c (w+1+n)
  short : n<9
  odd : n%2=1

def Losses (c : Trace) : Prop := ∀ U, ∃ w n,U≤w ∧ OddLoss c w n

def fallRead (c : Trace) (t : Nat) : Bool := c (t-1) && whiteNeed c t

private theorem lit_white (c : Trace) (t : Nat) (w : c t=false) (h : PairLit c t) :
    east c (t+1) 1=true := by
  change rule (east c t 0) (east c t 1) (east c t 2)=true
  rw [east0,w]; rcases h with e|e <;> rw [e] <;> simp [rule]

private theorem lit_two (c : Trace) (t : Nat) (b : c t=true) (b' : c (t+1)=true)
    (h : PairLit c t) : PairLit c (t+2) := by
  have cert : ∀ x y z v : Bool, (x=true ∨ y=true) →
      rule true (rule true x y) (rule x y z)=true ∨
      rule (rule true x y) (rule x y z) (rule y z v)=true := by decide
  unfold PairLit
  simp only [east,east0,b,b']
  exact cert _ _ _ _ h

private theorem lit_even (c : Trace) (t k : Nat)
    (bl : ∀ i,i<2*k → c (t+i)=true) (h : PairLit c t) : PairLit c (t+2*k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have a := ih (fun i l => bl i (by omega))
    have eq := lit_two c (t+2*k) (bl _ (by omega))
      (by rw [Nat.add_assoc];exact bl _ (by omega)) a
    rwa [show t+2*k+2=t+2*(k+1) by omega] at eq

/-- Once a genuine white read is high, its head pair cannot die at any
later white without a short odd physical loss in the intervening time. -/
theorem capture_or_loss (c : Trace) (s : Nat) (sw : c s=false) (sh : PairLit c s)
    (U : Nat) (us : U≤s) (no : ∀ w n,U≤w → ¬OddLoss c w n) :
    ∀ t,s≤t → c t=false → PairLit c t := by
  have cover (k : Nat) : ∃ z,s≤z ∧ z≤s+k ∧ c z=false ∧ PairLit c z ∧
      ∀ i,z<i → i≤s+k → c i=true := by
    induction k with
    | zero => exact ⟨s,by omega,by omega,sw,sh,fun i _ _ => by omega⟩
    | succ k ih =>
      obtain ⟨z,sz,zk,zw,hot,mid⟩ := ih
      cases v : c (s+k+1) with
      | true =>
        exact ⟨z,sz,by omega,zw,hot,fun i l r => by
          by_cases eq : i=s+k+1
          · simpa [eq] using v
          · exact mid i l (by omega)⟩
      | false =>
        refine ⟨s+k+1,by omega,by omega,v,?_,fun i _ _ => by omega⟩
        let n := s+k-z
        have e : z+1+n=s+k+1 := by dsimp [n];omega
        have solid (i : Nat) (lt : i<n) : c (z+1+i)=true :=
          mid _ (by omega) (by dsimp [n] at lt;omega)
        have start := lit_white c z zw hot
        apply Classical.byContradiction
        intro gone
        have lost : ¬PairLit c (z+1+n) := by rwa [e]
        have le : n<9 := by
          by_cases long : 9≤n
          · have both := black_pair c 0 (z+1+n-9) (fun i lt => by
              rw [east0,show z+1+n-9+i=z+1+(n-9+i) by omega];exact solid _ (by omega))
            rw [show z+1+n-9+9=z+1+n by omega] at both
            exact False.elim (lost (Or.inr both.2))
          · omega
        have odd : n%2=1 := by
          by_cases p : n%2=1
          · exact p
          have ev : 2*(n/2)=n := by omega
          have both := lit_even c (z+1) (n/2) (by rwa [ev]) (Or.inl start)
          rw [ev] at both
          exact False.elim (lost both)
        exact no z n (by omega) ⟨zw,solid,e ▸ v,start,lost,le,odd⟩
  intro t st w
  obtain ⟨z,_,zt,_,h,bl⟩ := cover (t-s)
  rw [Nat.add_sub_of_le st] at zt bl
  by_cases eq : z=t
  · simpa [eq] using h
  · have con := bl t (by omega) (by omega)
    rw [w] at con;contradiction

/-- All genuine marked clocks obey this alternative. It isolates exactly
what can hide a nonperiodic west demand at interior whites when the
first-white samples alone have a period. -/
theorem marked_fall_alternative (c : Trace) (mark : c 0=true) (ep : EventuallyPeriodic c)
    (black : BlackLock c) (join : Joined c) :
    Losses c ∨ (∃ S,∀ t,S≤t → c t=false → PairLit c t) ∧ ¬EventuallyPeriodic (fallRead c) := by
  by_cases loss : Losses c
  · exact Or.inl loss
  right
  obtain ⟨U,no⟩ : ∃ U,∀w n,U≤w → ¬OddLoss c w n := by
    apply Classical.byContradiction
    intro bad
    apply loss
    intro U
    apply Classical.byContradiction
    intro miss
    exact bad ⟨U,fun w n le event => miss ⟨w,n,le,event⟩⟩
  have rich := west_rich c mark ep black
  obtain ⟨s,us,sw,one⟩ : ∃s,U≤s ∧ c s=false ∧ east c s 1=true := by
    apply Classical.byContradiction
    intro none
    apply rich
    have zero (t : Nat) (ut : U≤t) : whiteNeed c t=false := by
      cases v : c t with
      | true => simp [whiteNeed,v]
      | false =>
        cases a : east c t 1 with
        | false => simp [whiteNeed,v,join _ v,a]
        | true => exact False.elim (none ⟨t,ut,v,a⟩)
    exact ⟨U,1,by decide,fun t late => (zero _ (by omega)).trans (zero _ late).symm⟩
  have cap := capture_or_loss c s sw (Or.inl one) U us no
  refine ⟨⟨s,cap⟩,?_⟩
  have decomp (t : Nat) (lt : s<t) : whiteNeed c t= (fallRead c t || (!c t && !c (t-1))) := by
    cases cw : c t with
    | true => simp [fallRead,whiteNeed,cw]
    | false =>
      cases prev : c (t-1) with
      | true => simp [fallRead,prev]
      | false =>
        have hot := lit_white c (t-1) prev (cap _ (by omega) prev)
        rw [show t-1+1=t by omega] at hot
        simp [fallRead,whiteNeed,cw,prev,join _ cw,hot]
  rintro ⟨F,Q,qp,fq⟩
  obtain ⟨T,P,pp,pc⟩ := ep
  apply rich
  refine ⟨s+F+T+2,P*Q,Nat.mul_pos pp qp,?_⟩
  intro t lt
  have same := period_mul c T P pc Q
  have fr := period_mul (fallRead c) F Q fq P t (by omega)
  rw [Nat.mul_comm Q P] at fr
  rw [decomp _ (by omega),decomp t (by omega),fr,same t (by omega),
    show t+P*Q-1=(t-1)+P*Q by omega,same (t-1) (by omega)]

private def rim (d : Nat) : Bool := decide (d%2=0)

private theorem rim_next (d : Nat) : rim (d+1)= !rim d := by
  unfold rim
  by_cases p : d%2=0
  · simp [p,show ¬(d+1)%2=0 by omega]
  · simp [p,show (d+1)%2=0 by omega]

private theorem held_west (c : Trace) (lock : BlackLock c) (s n : Nat)
    (held : ∀i,i<n → c (s+i)=true) (fall : c (s+n)=false) :
    ∀ d i,i+d≤n → west c (s+i) d=(if i+d=n then !rim d else rim d) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro i lim
    rcases d with _|d
    · rw [west0];by_cases eq : i=n
      · simpa [eq,rim] using fall
      · simpa [eq,rim] using held i (by omega)
    rcases d with _|d
    · rw [lock (s+i) (held i (by omega)),Nat.add_assoc]
      by_cases e : i+1=n
      · simp [e,fall,rim]
      · simp [e,held (i+1) (by omega),rim]
    · have inv : west c (s+i) (d+2)=xor (west c (s+i+1) (d+1))
          (west c (s+i) (d+1) || west c (s+i) d) := (left_inv _ _ _).symm
      rw [inv,Nat.add_assoc,ih (d+1) (by omega) (i+1) (by omega),
        ih (d+1) (by omega) i (by omega),ih d (by omega) i (by omega)]
      rw [ite_eq_right (by omega : i+(d+1)≠n),ite_eq_right (by omega : i+d≠n),
        show i+1+(d+1)=i+(d+2) by omega,rim_next (d+1),rim_next d]
      by_cases e : i+(d+2)=n <;> cases rim d <;> simp [e]

private theorem parity_next (k : Nat) : decide ((k+1)%2=1) = !decide (k%2=1) := by
  by_cases p : k%2=1
  · simp [p,show ¬(k+1)%2=1 by omega]
  · simp [p,show (k+1)%2=1 by omega]

/-- The western bit one place behind the failed checker front toggles
once per two black updates, independently of all farther western cells. -/
private theorem even_wire (c : Trace) (lock : BlackLock c) (s k : Nat)
    (held : ∀i,i<2*k → c (s+i)=true) (fall : c (s+2*k)=false) :
    west c (s+2*k) 1=xor (west c s (2*k+1)) (decide (k%2=1)) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have pat := held_west c lock s (2*(k+1)) held fall
    have a := pat (2*k+2) 0 (by omega)
    have b := pat (2*k+1) 0 (by omega)
    have d := pat (2*k+1) 1 (by omega)
    have e0 : west c s (2*k+2)=false := by
      simpa [rim,show 2*k+2=2*(k+1) by omega,show (2*(k+1))%2=0 by omega] using a
    have e1 : west c s (2*k+1)=false := by
      simpa [rim,show 2*k+1≠2*(k+1) by omega,show ¬(2*k+1)%2=0 by omega] using b
    have e2 : west c (s+1) (2*k+1)=true := by
      simpa [rim,show 1+(2*k+1)=2*(k+1) by omega,show ¬(2*k+1)%2=0 by omega] using d
    have r1 : west c (s+1) (2*k+2)=west c s (2*k+3) := by
      change rule _ _ _=_
      rw [e0,e1];cases west c s (2*k+3) <;> rfl
    have r2 : west c (s+2) (2*k+1)= !west c s (2*k+3) := by
      change rule _ _ _=_
      rw [r1,e2];cases west c s (2*k+3) <;> rfl
    have eq := ih (s+2) (fun i li => by
      rw [show s+2+i=s+(i+2) by omega];exact held _ (by omega)) (by
      rw [show s+2+2*k=s+2*(k+1) by omega];exact fall)
    rw [show s+2+2*k=s+2*(k+1) by omega,r2] at eq
    rw [eq,show 2*(k+1)+1=2*k+3 by omega,parity_next]
    cases west c s (2*k+3) <;> cases decide (k%2=1) <;> rfl

def survivesGate (c : Trace) (s : Nat) : Nat → Bool
  | 0 => true
  | k+1 => (east c s 2 || east c s 3) && survivesGate c (s+2) k

private theorem locked_pair (c : Trace) (s n : Nat)
    (held : ∀i,i<n → c (s+i)=true) (lo : east c s 1=false) (hi : east c s 2=true) :
    east c (s+n) 1=false ∧ east c (s+n) 2=true := by
  induction n with
  | zero => exact ⟨lo,hi⟩
  | succ n ih =>
    obtain ⟨a,b⟩ := ih (fun i li => held i (by omega))
    constructor <;> change rule _ _ _=_ <;> simp [east0,held n (by omega),a,b,rule]

private theorem real_gate (c : Trace) (s k : Nat)
    (held : ∀i,i<2*k → c (s+i)=true) (start : east c s 1=true) :
    east c (s+2*k) 1=survivesGate c s k := by
  induction k generalizing s with
  | zero => exact start
  | succ k ih =>
    have b : c s=true := by simpa using held 0 (by omega)
    have b' := held 1 (by omega)
    have off : east c (s+1) 1=false := by change rule (east c s 0) _ _=_;rw [east0,b,start];rfl
    have next : east c (s+1) 2= !(east c s 2 || east c s 3) := by
      change rule (east c s 1) (east c s 2) (east c s 3)=_;rw [start];simp [rule]
    cases g : east c s 2 || east c s 3 with
    | true =>
      have on : east c (s+2) 1=true := by
        change rule (east c (s+1) 0) _ _=_;rw [east0,b',off,next,g];rfl
      have z := ih (s+2) (fun i li => by
        rw [show s+2+i=s+(i+2) by omega];exact held _ (by omega)) on
      rw [show s+2+2*k=s+2*(k+1) by omega] at z
      simpa [survivesGate,g] using z
    | false =>
      have z := locked_pair c (s+1) (2*k+1) (fun i li => by
        rw [show s+1+i=s+(i+1) by omega];exact held _ (by omega)) off (by rw [next,g];rfl)
      rw [show s+1+(2*k+1)=s+2*(k+1) by omega] at z
      simpa [survivesGate,g] using z.1

def SignedGate (c : Trace) (s n : Nat) : Prop :=
  xor (west c s (n+1)) (decide ((n/2)%2=1))=xor (c (s+n+1)) (survivesGate c s (n/2))

private theorem join_gate (c : Trace) (black : BlackLock c) (join : Joined c)
    (s n : Nat) (ev : n%2=0) (held : ∀i,i<n → c (s+i)=true)
    (fall : c (s+n)=false) (hot : east c s 1=true) : SignedGate c s n := by
  have len : 2*(n/2)=n := by omega
  have wire := even_wire c black s (n/2) (by rwa [len]) (by rwa [len])
  have gate := real_gate c s (n/2) (by rwa [len]) hot
  rw [len] at wire gate
  have eq := join (s+n) fall
  simp only [need,gate,wire] at eq
  unfold SignedGate
  rw [←eq]
  cases xor (west c s (n+1)) (decide (n/2%2=1)) <;> cases c (s+n+1) <;> rfl

/-- A single anchored physical lag fork. Its incoming white run is
too short to force the checker over its actual black predecessor cone. -/
structure EvenFork (c : Trace) (Q w n : Nat) : Prop where
  prior : c w=false
  solid : ∀i,i<n → c (w+1+i)=true
  fall : c (w+1+n)=false
  pos : 0<n
  short : n<9
  even : n%2=0
  starving : ∃i,i≤9*(n/2) ∧ c (w-i)=true
  delta : east c (w+1+n+Q) 1≠east c (w+1+n) 1
  leftWire : west c (w+1+Q) (n+1)≠west c (w+1) (n+1)
  oldGate : SignedGate c (w+1) n
  newGate : SignedGate c (w+1+Q) n
  splitGate : survivesGate c (w+1+Q) (n/2)≠survivesGate c (w+1) (n/2)

private theorem low_even (c : Trace) (s k : Nat) (low : east c s 1=false)
    (bl : ∀ i,i<2*k → c (s+i)=true) : east c (s+2*k) 1=false := by
  induction k with
  | zero => simpa using low
  | succ k ih =>
    have a := ih (fun i l => bl i (by omega))
    have b := bl (2*k) (by omega)
    have b' : c (s+2*k+1)=true := by rw [Nat.add_assoc];exact bl _ (by omega)
    rw [show s+2*(k+1)=s+2*k+1+1 by omega]
    simp only [east,east0,b,b',a]
    cases east c (s+2*k) 2 <;> cases east c (s+2*k) 3 <;> rfl

private theorem fall_odd (c : Trace) (s n : Nat) (on : east c s 1=true)
    (odd : n%2=1) (bl : ∀ i,i<n → c (s+i)=true) : east c (s+n) 1=false := by
  have b : c s=true := by simpa using bl 0 (by omega)
  have off : east c (s+1) 1=false := by change rule (east c s 0) _ _=_;rw [east0,b,on];rfl
  have z := low_even c (s+1) (n/2) off (fun i hi => by
    rw [show s+1+i=s+(i+1) by omega];exact bl _ (by omega))
  rwa [show s+1+2*(n/2)=s+n by omega] at z

private theorem fed_checker (c : Trace) (w n S : Nat) (late : S+9*(n/2)≤w)
    (even : n%2=0) (cap : ∀t,S≤t → c t=false → PairLit c t)
    (white : ∀i,i≤9*(n/2) → c (w-i)=false) : RenewalFront.CheckerAt c (w+1) (n+1) := by
  let d := 9*(n/2)
  have start := white d (by omega)
  have first := lit_white c (w-d) start (cap _ (by dsimp [d];omega) start)
  have on (i : Nat) (le : i≤d) : east c (w-d+1+i) 1=true := by
    apply head_hold c _ i first
    intro j jl
    rw [show w-d+1+j=w-(d-1-j) by dsimp [d] at *;omega]
    exact white _ (by dsimp [d] at *;omega)
  intro x px hx
  have pair := RenewalFront.checker c 1 (w-d+1) d (x/2) on d
    (by dsimp [d];omega) (Nat.le_refl _)
  rw [show w-d+1+d=w+1 by dsimp [d] at *;omega] at pair
  by_cases yes : x%2=1
  · rw [decide_eq_true yes,show x=1+2*(x/2) by omega];exact pair.1
  · rw [decide_eq_false yes,show x=1+2*(x/2)-1 by omega];exact pair.2 (by omega)

def CollisionSupply (c : Trace) (P : Nat) : Prop :=
  Losses c ∨ ∀ k,0<k → ∀U, ∃ w n,U≤w ∧ EvenFork c (P*k) w n

/-- The dichotomy applies to EVERY multiple of the proposed period.
If physical odd extinctions stop, arbitrary late forks of that fixed
lag must use a short even run immediately after an underfed white run. -/
theorem marked_supply (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (per : ∀t,T≤t → c (t+P)=c t) (mix : Mixed c) (black : BlackLock c) (join : Joined c) :
    CollisionSupply c P := by
  rcases marked_fall_alternative c mark ⟨T,P,hp,per⟩ black join with loss|⟨⟨S,cap⟩,rich⟩
  · exact Or.inl loss
  right;intro k kp U
  let Q := P*k
  have qp : 0<Q := Nat.mul_pos hp kp
  have eq (t : Nat) (late : T≤t) : c (t+Q)=c t := period_mul c T P per k t late
  obtain ⟨a,la,aw⟩ := mix (S+U+T+40) false
  obtain ⟨t,lt,diff⟩ : ∃ t,a+2≤t ∧ fallRead c (t+Q)≠fallRead c t := by
    apply Classical.byContradiction;intro bad
    apply rich
    exact ⟨a+2,Q,qp,fun t late => Classical.byContradiction (fun no => bad ⟨t,late,no⟩)⟩
  have prev := eq (t-1) (by omega)
  have now := eq t (by omega)
  rw [←show t+Q-1=(t-1)+Q by omega] at prev
  have fact : c (t-1)=true ∧ c t=false ∧ east c (t+Q) 1≠east c t 1 := by
    cases v : c (t-1) <;> cases w : c t <;>
      simp_all [fallRead,whiteNeed]
    rwa [←join _ now,←join _ w]
  obtain ⟨last,ww,split⟩ := fact
  have old (j : Nat) : ∃ w,a≤w ∧ w≤a+j ∧ c w=false ∧ ∀ i,w<i → i≤a+j → c i=true := by
    induction j with
    | zero => exact ⟨a,by omega,by omega,aw,fun i _ _ => by omega⟩
    | succ j ih =>
      cases v : c (a+j+1) with
      | false => exact ⟨_,by omega,by omega,v,fun i _ _ => by omega⟩
      | true =>
        obtain ⟨w,l,r,wh,b⟩ := ih
        exact ⟨w,l,by omega,wh,fun i wi it => by
          by_cases e : i=a+j+1
          · simpa [e] using v
          · exact b i wi (by omega)⟩
  obtain ⟨w,aw',wt,wh,solid⟩ := old (t-1-a)
  rw [show a+(t-1-a)=t-1 by omega] at wt solid
  let n := t-(w+1)
  have date : w+1+n=t := by dsimp [n];omega
  have len : 0<n := by
    by_cases e : w=t-1
    · rw [e,last] at wh;contradiction
    · dsimp [n];omega
  have hb (i : Nat) (hi : i<n) : c (w+1+i)=true := solid _ (by omega) (by omega)
  have twin (i : Nat) (hi : i<n) : c (w+Q+1+i)=true := by
    rw [show w+Q+1+i=w+1+i+Q by omega,eq _ (by omega)];exact hb i hi
  have ending : w+Q+1+n=t+Q := by omega
  have small : n<9 := by
    by_cases big : 9≤n
    · have one := (RenewalFront.after_solid c (w+1) n big hb).1
      have two := (RenewalFront.after_solid c (w+Q+1) n big twin).1
      rw [date] at one;rw [ending] at two
      exact False.elim (split (two.trans one.symm))
    · omega
  have zw := (eq w (by omega)).trans wh
  have ev : n%2=0 := by
    by_cases p : n%2=1
    · have one := fall_odd c (w+1) n (lit_white c w wh (cap _ (by omega) wh)) p hb
      have two := fall_odd c (w+Q+1) n (lit_white c (w+Q) zw (cap _ (by omega) zw)) p twin
      rw [date] at one;rw [ending] at two
      exact False.elim (split (two.trans one.symm))
    · omega
  have hot := lit_white c w wh (cap _ (by omega) wh)
  have hot' := lit_white c (w+Q) zw (cap _ (by omega) zw)
  have eqn : 2*(n/2)=n := by omega
  have a1 := join_gate c black join (w+1) n ev hb (date ▸ ww) hot
  have a2 := join_gate c black join (w+Q+1) n ev twin (ending ▸ now.trans ww) hot'
  have g1 := real_gate c (w+1) (n/2) (by rwa [eqn]) hot
  have g2 := real_gate c (w+Q+1) (n/2) (by rwa [eqn]) hot'
  rw [eqn,date] at g1;rw [eqn,ending] at g2
  have gates : survivesGate c (w+Q+1) (n/2)≠survivesGate c (w+1) (n/2) := by rwa [←g1,←g2]
  have westFork : west c (w+Q+1) (n+1)≠west c (w+1) (n+1) := by
    intro same
    unfold SignedGate at a1 a2
    have cn : c (w+Q+1+n+1)=c (w+1+n+1) := by
      rw [show w+Q+1+n+1=w+1+n+1+Q by omega,eq _ (by omega)]
    rw [same,cn,a1] at a2
    exact gates (by cases c (w+1+n+1) <;>
      cases survivesGate c (w+1) (n/2) <;> cases survivesGate c (w+Q+1) (n/2) <;> simp_all)
  have comm : w+1+Q=w+Q+1 := by omega
  refine ⟨w,n,by omega,wh,hb,date ▸ ww,len,small,ev,?_,by simpa [date] using split,
    comm ▸ westFork,a1,comm ▸ a2,comm ▸ gates⟩
  apply Classical.byContradiction;intro no
  have whites (i : Nat) (il : i≤9*(n/2)) : c (w-i)=false := by
    cases z : c (w-i)
    · rfl
    · exact False.elim (no ⟨i,il,z⟩)
  have fed := fed_checker c w n S (by omega) ev cap whites
  have fed' := fed_checker c (w+Q) n S (by omega) ev cap (fun i il => by
    rw [show w+Q-i=w-i+Q by omega,eq _ (by omega)];exact whites i il)
  have band := RenewalFront.compare_band c (w+1) (w+Q+1) (n+1) (fun i => by
    rw [show w+Q+1+i=w+1+i+Q by omega,eq _ (by omega)]) fed fed' n 1 (by omega)
  rw [date,ending] at band
  exact split band.symm

/-- A black interval of odd length cannot take an initially low head
to a vacant pair. Starting 01 remains locked; starting 00 emits a 1
on the first step and the remaining even interval preserves capture. -/
private theorem low_odd_lit (c : Trace) (s n : Nat) (lo : east c s 1=false)
    (odd : n%2=1) (held : ∀i,i<n → c (s+i)=true) : PairLit c (s+n) := by
  cases sec : east c s 2 with
  | true => exact Or.inr (locked_pair c s n held lo sec).2
  | false =>
    have b : c s=true := by simpa using held 0 (by omega)
    have on : east c (s+1) 1=true := by
      change rule (east c s 0) _ _=_;rw [east0,b,lo,sec];rfl
    have z := lit_even c (s+1) (n/2) (fun i li => by
      rw [show s+1+i=s+(i+1) by omega];exact held _ (by omega)) (Or.inl on)
    rwa [show s+1+2*(n/2)=s+n by omega] at z

/-- The last lit white of the SAME copy before a dark white has a
unique intervening extinction. The entire following white history
stays dark, so that same odd block cannot recur before the target. -/
structure DarkSource (c : Trace) (P B t : Nat) : Prop where
  located : ∃ w n, B≤w ∧ w+1+n≤t ∧ t<w+1+n+P ∧ OddLoss c w n ∧
    ∀i,w<i → i≤t → c i=false → ¬PairLit c i

private theorem locate_dark (c : Trace) (T P a t : Nat) (hp : 0<P)
    (per : ∀i,T≤i → c (i+P)=c i) (late : T≤a) (atA : c a=false)
    (lit : PairLit c a) (atT : c t=false) (atime : a≤t) (dark : ¬PairLit c t) :
    DarkSource c P a t := by
  have scan (j : Nat) : ∃ w,a≤w ∧ w≤a+j ∧ c w=false ∧ PairLit c w ∧
      ∀i,w<i → i≤a+j → c i=false → ¬PairLit c i := by
    induction j with
    | zero => exact ⟨a,by omega,by omega,atA,lit,fun i _ _ => by omega⟩
    | succ j ih =>
      by_cases newbit : c (a+j+1)=false ∧ PairLit c (a+j+1)
      · exact ⟨a+j+1,by omega,by omega,newbit.1,newbit.2,fun i _ _ => by omega⟩
      · obtain ⟨w,l,r,wh,hot,after⟩ := ih
        exact ⟨w,l,by omega,wh,hot,fun i wi it iw li => by
          by_cases e : i=a+j+1
          · exact newbit (e ▸ And.intro iw li)
          · exact after _ wi (by omega) iw li⟩
  obtain ⟨w,aw,wt,wh,hot,after⟩ := scan (t-a)
  rw [Nat.add_sub_of_le atime] at wt after
  have strict : w<t := by
    by_cases eq : w=t
    · exact False.elim (dark (eq ▸ hot))
    · omega
  have first (k : Nat) (wht : c (w+1+k)=false) :
      ∃ n,n≤k ∧ c (w+1+n)=false ∧ ∀i,i<n → c (w+1+i)=true := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      by_cases some : ∃j,j<k ∧ c (w+1+j)=false
      · obtain ⟨j,jk,v⟩ := some
        obtain ⟨n,le,atN,pref⟩ := ih j jk v
        exact ⟨n,by omega,atN,pref⟩
      · exact ⟨k,by omega,wht,fun i li => by
          cases z : c (w+1+i)
          · exact False.elim (some ⟨i,li,z⟩)
          · rfl⟩
  obtain ⟨n,lim,fin,middle⟩ := first (t-(w+1)) (by rwa [show w+1+(t-(w+1))=t by omega])
  have limit : w+1+n≤t := by omega
  have lost := after (w+1+n) (by omega) limit fin
  have on := lit_white c w wh hot
  have small : n<9 := by
    by_cases big : 9≤n
    · exact False.elim (lost (Or.inr (RenewalFront.after_solid c (w+1) n big middle).2))
    · omega
  have odd : n%2=1 := by
    by_cases ev : 2*(n/2)=n
    · have z := lit_even c (w+1) (n/2) (by rwa [ev]) (Or.inl on)
      exact False.elim (lost (ev ▸ z))
    · omega
  refine ⟨w,n,aw,limit,?_,⟨wh,middle,fin,on,lost,small,odd⟩,after⟩
  by_cases ahead : w+1+n+P≤t
  · have vw := (per w (by omega)).trans wh
    have gone := after (w+P) (by omega) (by omega) vw
    have head : east c (w+P+1) 1=false := by
      have no1 : east c (w+P) 1=false := by cases z : east c (w+P) 1 <;> simp_all [PairLit]
      have no2 : east c (w+P) 2=false := by cases z : east c (w+P) 2 <;> simp_all [PairLit]
      change rule (east c (w+P) 0) _ _=_;rw [east0,vw,no1,no2];rfl
    have bright := low_odd_lit c (w+P+1) n head odd (fun i il => by
      rw [show w+P+1+i=w+1+i+P by omega,per _ (by omega)];exact middle i il)
    rw [show w+P+1+n=w+1+n+P by omega] at bright
    exact False.elim (after _ (by omega) ahead ((per _ (by omega)).trans fin) bright)
  · omega

/-- Here the final gate in the other copy is deliberately NOT assumed
to be 1: that is the positive conclusion supplied by the marked fork. -/
structure DarkArm (c : Trace) (T P d h t v : Nat) : Prop where
  matched : Arm c T P (d+P+10) h t v
  lowWhite : c t=false
  nextWhite : c (t+1)=false
  low : east c t 1=false ∧ east c t 2=false
  oppositeLow : east c v 1=false
  origin : DarkSource c P T t

private theorem true_high (c : Trace) (U : Nat) (rich : ¬EventuallyPeriodic (whiteNeed c))
    (join : Joined c) : ∃t,U≤t ∧ c t=false ∧ east c t 1=true := by
  apply Classical.byContradiction;intro none;apply rich
  have zero (t : Nat) (ut : U≤t) : whiteNeed c t=false := by
    cases v : c t with
    | true => simp [whiteNeed,v]
    | false =>
      cases a : east c t 1 with
      | false => simp [whiteNeed,v,join _ v,a]
      | true => exact False.elim (none ⟨t,ut,v,a⟩)
  exact ⟨U,1,by decide,fun t late => (zero _ (by omega)).trans (zero _ late).symm⟩

/-- No inverse-predictor challenge is needed when the first-white reads
share the clock: the marked fork must be interior. Its low arm's true
odd extinction lies inside the long COMMON masked past, within one
period of the fork's preceding tick (plus the short black run itself). -/
theorem interior_fork (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (per : ∀i,T≤i → c (i+P)=c i) (fp : ∀i,T≤i → fallRead c (i+P)=fallRead c i)
    (lock : BlackLock c) (join : Joined c) (starts : ResetStarts c T P) (N d h : Nat) :
    ∃ t v,N≤t ∧ DarkArm c T P d h t v ∧ east c v 2=true := by
  obtain ⟨a,la,aw,lit⟩ := true_high c (N+T) (west_rich _ mark ⟨T,P,hp,per⟩ lock) join
  obtain ⟨s,u,k,as,m⟩ := starts a (d+P+10) h
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by have := m.deep;omega)
  let x := s+j
  let y := u+j
  have arm : Arm c T P (d+P+10) h x y := ⟨s,u,j,m,Or.inl ⟨rfl,rfl⟩⟩
  have rev : Arm c T P (d+P+10) h y x := ⟨s,u,j,m,Or.inr ⟨rfl,rfl⟩⟩
  obtain ⟨cs,shared,wh,wh',split⟩ := arm_stamp c T P _ _ x y per arm
  have fclk := same_clock (fallRead c) T P fp s u m.mature
    (Nat.le_trans m.mature (Nat.le_of_lt m.ordered)) m.phase (j+1)
  have sf : fallRead c (x+1)=fallRead c (y+1) := by simpa [x,y,Nat.add_assoc] using fclk
  have oldW : c x=false := by
    cases z : c x
    · rfl
    · have vz := cs.symm.trans z
      exact False.elim (split (by simpa [fallRead,whiteNeed,z,vz,wh,wh'] using sf))
  have oldW' := cs.symm.trans oldW
  have common : east c x 1=east c y 1 := by
    simpa [whiteNeed,oldW,oldW',join _ oldW,join _ oldW'] using shared
  have ne : east c (x+1) 1≠east c (y+1) 1 := by rwa [←join _ wh,←join _ wh']
  have changeX : east c (x+1) 1=(east c x 1 || east c x 2) := by
    change rule (east c x 0) _ _=_;rw [east0,oldW];simp [rule]
  have changeY : east c (y+1) 1=(east c y 1 || east c y 2) := by
    change rule (east c y 0) _ _=_;rw [east0,oldW'];simp [rule]
  rw [changeX,changeY] at ne
  have lowx : east c x 1=false := by
    cases z : east c x 1
    · rfl
    · exact False.elim (ne (by simp [common.symm.trans z,z]))
  have lowy := common.symm.trans lowx
  simp only [lowx,lowy,Bool.false_or] at ne
  have make (t v : Nat) (atN : a≤t) (z : c t=false) (nwh : c (t+1)=false)
      (h1 : east c t 1=false) (h2 : east c t 2=false) (rv : east c v 1=false)
      (ar : Arm c T P (d+P+10) h t v) (hiv : east c v 2=true) :
      ∃ t v,N≤t ∧ DarkArm c T P d h t v ∧ east c v 2=true := by
    obtain ⟨⟨w,n,wa,l,r,b,dead⟩⟩ := locate_dark c T P a t hp per (by omega) aw
      (Or.inl lit) z atN (by simp [PairLit,h1,h2])
    exact ⟨t,v,by omega,⟨ar,z,nwh,⟨h1,h2⟩,rv,⟨w,n,by omega,l,r,b,dead⟩⟩,hiv⟩
  cases v0 : east c x 2 <;> cases v1 : east c y 2
  · exact False.elim (ne (v0.trans v1.symm))
  · exact make x y (by dsimp [x];omega) oldW wh lowx v0 lowy arm v1
  · exact make y x (by dsimp [y];have := m.ordered;omega) oldW' wh' lowy v1 lowx rev v0
  · exact False.elim (ne (v0.trans v1.symm))

/-- L1: at least ONE arm of an actual marked collision challenges the
inverse predictor on a capable label. This does not require either
recurrence of the endpoint word or coincidence of the two endpoint words. -/
theorem L1 (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (outside : ¬PulseBasin c ∧ ¬RenewalFront.SparsePulseClock c ∧ ¬RenewalFront.Bridged c) (short : ¬RenewalFront.PulseWindows c)
    (channel : CollisionSupply c P) (rich : ¬EventuallyPeriodic (fallRead c)) (starts : ResetStarts c T P) :
    ∀ N d h, ∃ t v,N≤t ∧ Arm c T P d h t v ∧ capable (seven c (t+2))=true ∧
      need c (t+1)≠guess (seven c (t+2)) := by
  sorry

def CollisionStop (c : Trace) (T P n : Nat) : Prop :=
  ∀ t v,n≤t → Arm c T P n n t v → c t=true → c (t+1)=false → east c t 1=false →
      let w := seven c (t+2)
      (code w=67 ∨ code w=91) → BlackCut c t w → Bracket c P t w →
      xor (west c t 2) (east c t 2)=c (t+2) → east c (t+2) 8=true →
      reset w (east c (t+2) 8)=false → east c (t+1) 1=guess w

/-- Discharge the actual two-arm case 67/91 on every pulse window:
both matched eastern heads have to be quiet at their first whites,
whereas the same joined western histories require opposite bits. -/
theorem windows_stop (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀ t,T≤t → c (t+P)=c t) (black : BlackLock c) (join : Joined c)
    (w : RenewalFront.PulseWindows c) : ∃ n,CollisionStop c T P n := by
  obtain ⟨U,quiet⟩ := RenewalFront.quiet_falls c ⟨T,P,hp,period⟩ mark black join w
  refine ⟨U+2,?_⟩
  intro t v late arm bw white _ _ _ _ _ _ _
  obtain ⟨same,_,_,ow,split⟩ := arm_stamp c T P (U+2) (U+2) t v period arm
  have lv : U≤v := by
    obtain ⟨s,u,k,r,pair⟩ := arm
    have dep := r.deep
    rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
  have z := quiet t (by omega) bw white 1 (by decide) (by decide)
  have zv := quiet v lv (same.symm.trans bw) ow 1 (by decide) (by decide)
  exact False.elim (split ((join _ white).trans (z.trans (zv.symm.trans (join _ ow).symm))))

/-- The two alternatives are disjoint. When first whites themselves
are irregular, stop the old two-word predictor escape. When the two
clocks are aligned, stop propagation from the identified true dark
source across its other arm's second gate. -/
def TerminalStop (c : Trace) (T P n : Nat) : Prop :=
  (¬EventuallyPeriodic (fallRead c) → CollisionStop c T P n) ∧
  ((∀i,T≤i → fallRead c (i+P)=fallRead c i) →
    ∀ t v,n≤t → DarkArm c T P n n t v → east c v 2=false)

/-- L2: either block the actual two-word first-white escape, or,
only on an aligned first-white clock, extinguish the opposite head at
the matched interior source. Neither case addresses unmatched rows. -/
theorem L2 (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (outside : ¬PulseBasin c ∧ ¬RenewalFront.SparsePulseClock c ∧ ¬RenewalFront.Bridged c)
    (short : ¬RenewalFront.PulseWindows c) (channel : CollisionSupply c P) :
    ∃ n,TerminalStop c T P n := by
  sorry

private theorem stays_high (c : Trace) (t : Nat) (white : c t=false) (old : east c t 1=true) :
    east c (t+1) 1=true := by
  change rule (east c t 0) (east c t 1) (east c t 2)=true
  rw [east0,white,old]
  simp [rule]

theorem collision (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (join : Joined c) : False := by
  have outside := And.intro (excludes_pulse_basin c mark ⟨T,P,hp,period⟩ black join)
    (And.intro (RenewalFront.excludes_sparse c ⟨T,P,hp,period⟩ mark black join)
      (RenewalFront.excludes_bridged c ⟨T,P,hp,period⟩ mark black join))
  have noWindows := RenewalFront.excludes_windows c ⟨T,P,hp,period⟩ mark black join
  by_cases first : EventuallyPeriodic (fallRead c)
  · obtain ⟨F,R,rp,fr⟩ := first
    let A := T+F
    let Q := P*R
    have aq : 0<Q := Nat.mul_pos hp rp
    have pc (t : Nat) (lt : A≤t) : c (t+Q)=c t :=
      period_mul c T P period R t (by dsimp [A] at lt;omega)
    have pq (t : Nat) (lt : A≤t) : fallRead c (t+Q)=fallRead c t := by
      rw [show Q=R*P by exact Nat.mul_comm P R]
      exact period_mul (fallRead c) F R fr P t (by dsimp [A] at lt;omega)
    have channel := marked_supply c A Q aq mark pc mixed black join
    obtain ⟨n,_,stop⟩ := L2 c A Q aq mark pc mixed (fun i _ => join i) black outside noWindows channel
    obtain ⟨t,v,late,arm,hit⟩ := interior_fork c A Q aq mark pc pq black join
      (reset_starts c A Q aq mark pc black join) n n n
    exact Bool.noConfusion (hit.symm.trans (stop pq t v late arm))
  have channel := marked_supply c T P hp mark period mixed black join
  obtain ⟨n,stops⟩ := L2 c T P hp mark period mixed past black outside noWindows channel
  have stop := stops.1 first
  obtain ⟨t,v,late,arm,cap,bad⟩ := L1 c T P hp mark period mixed past black outside noWindows channel first
    (reset_starts c T P hp mark period black join) (n+T+P+6) n n
  obtain ⟨last,shared,white,other,unequal⟩ := arm_stamp c T P n n t v period arm
  have wrong : east c (t+1) 1≠guess (seven c (t+2)) := by rwa [←join (t+1) white]
  obtain ⟨spec,bit,unsync⟩ := decoder_bound c (t+1) white cap wrong
  have shape := older_escape c t _ rfl white spec wrong
  rcases shape with ⟨back,_⟩|⟨back,words⟩
  · have oldW : c t=false := congrArg Prod.snd back
    have old1 : east c t 1=true := congrArg Prod.fst back
    have vW : c v=false := last.symm.trans oldW
    have same := shared
    simp only [whiteNeed,oldW,vW,Bool.not_false,Bool.true_and,join t oldW,join v vW,old1] at same
    have t1 := stays_high c t oldW old1
    have v1 := stays_high c v vW same.symm
    exact unequal ((join (t+1) white).trans (t1.trans (v1.symm.trans (join (v+1) other).symm)))
  · have bw : c t=true := congrArg Prod.snd back
    have zero : east c t 1=false := congrArg Prod.fst back
    have cut := physical_cut c t _ rfl white words wrong back
    have br := actual_bracket c T P t hp period (by omega) black join bw white zero _ rfl cut bit unsync
    exact wrong (stop t v (by omega) arm bw white zero words cut br (mirrored c t bw white zero join) bit unsync)

private theorem halves_actual (t d : Nat) :
    east center t d=cell t (d:Int) ∧ west center t d=cell t (-(d:Int)) := by
  induction t generalizing d with
  | zero =>
    cases d with
    | zero => exact ⟨rfl,rfl⟩
    | succ d => simp [east,west,cell]; omega
  | succ t ih =>
    cases d with
    | zero => exact ⟨rfl,rfl⟩
    | succ d =>
      constructor
      · simp only [east,(ih d).1,(ih (d+1)).1,(ih (d+2)).1,cell]
        congr 1 <;> congr 1 <;> omega
      · simp only [west,(ih d).2,(ih (d+1)).2,(ih (d+2)).2,cell]
        congr 1 <;> congr 1 <;> omega

private theorem actual_wall (t : Nat) :
    center (t+1)=rule (west center t 1) (center t) (east center t 1) := by
  rw [(halves_actual t 1).1,(halves_actual t 1).2]
  rfl

private theorem actual_locks : BlackLock center ∧ Joined center := by
  constructor <;> intro t bit
  · have h := actual_wall t
    rw [bit] at h
    cases a : west center t 1 <;> cases b : center (t+1) <;> simp_all [rule]
  · have h := actual_wall t
    rw [bit] at h
    unfold need
    cases a : west center t 1 <;> cases b : east center t 1 <;> simp_all [rule]

private theorem actual_mixed (ep : EventuallyPeriodic center) : Mixed center := by
  intro N b
  apply Classical.byContradiction
  intro miss
  have fixed (t : Nat) (late : N≤t) : center t= !b := by
    cases h : center t <;> cases b <;> simp_all
  apply MaskedRightRigidity.claim_of_periodic_mask _ ep
  cases b with
  | false =>
    exact ⟨N,1,by decide,fun t late => by simp [MaskedRightRigidity.maskedRight,fixed t late,fixed (t+1) (by omega)]⟩
  | true =>
    have latch (t : Nat) (lt : N≤t) (one : cell t 1=true) : cell (t+1) 1=true := by
      change rule (center t) (cell t 1) (cell t 2)=true
      rw [fixed t lt,one];rfl
    by_cases any : ∃ t,N≤t ∧ cell t 1=true
    · obtain ⟨a,late,one⟩ := any
      have high (j : Nat) : cell (a+j) 1=true := by
        induction j with
        | zero => simpa using one
        | succ j ih => exact latch (a+j) (by omega) ih
      exact ⟨a,1,by decide,fun t le => by
        simp [MaskedRightRigidity.maskedRight,fixed t (by omega),fixed (t+1) (by omega),
          show cell t 1=true by simpa [Nat.add_sub_of_le le] using high (t-a),
          show cell (t+1) 1=true by simpa [Nat.add_sub_of_le (show a≤t+1 by omega)] using high (t+1-a)]⟩
    · have zero (t : Nat) (lt : N≤t) : cell t 1=false := by
        cases h : cell t 1 with
        | false => rfl
        | true => exact False.elim (any ⟨t,lt,h⟩)
      exact ⟨N,1,by decide,fun t late => by simp [MaskedRightRigidity.maskedRight,zero t late,zero (t+1) (by omega)]⟩

theorem close_step4 (hcenter : EventuallyPeriodic center) : False := by
  have mixed := actual_mixed hcenter
  obtain ⟨T,P,hp,clock⟩ := hcenter
  exact collision center T P hp rfl clock mixed (fun t _ => actual_locks.2 t) actual_locks.1 actual_locks.2

end OpenProblem.AncestryBlueprint
#print axioms OpenProblem.AncestryBlueprint.decoder_bound
#print axioms OpenProblem.AncestryBlueprint.reset_starts
#print axioms OpenProblem.AncestryBlueprint.RenewalFront.excludes_windows
#print axioms OpenProblem.AncestryBlueprint.interior_fork
#print axioms OpenProblem.AncestryBlueprint.marked_supply
#print axioms OpenProblem.AncestryBlueprint.windows_stop
#print axioms OpenProblem.AncestryBlueprint.RenewalFront.excludes_bridged
#print axioms OpenProblem.AncestryBlueprint.RenewalFront.excludes_sparse
#print axioms OpenProblem.AncestryBlueprint.excludes_pulse_basin
#print axioms OpenProblem.AncestryBlueprint.west_rich
#print axioms OpenProblem.AncestryBlueprint.close_step4
