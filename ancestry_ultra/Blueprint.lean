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
open FiniteWindowRecurrence QuantifiedSplit in
private theorem prefix_cycle (d : Nat) :
    ∃ p,0<p ∧ p≤2^(d+1) ∧ ∀ t,2^(d+1)≤t → ∀ k, k≤d →
      side (t+p) (k:Int)=side t (k:Int) := by
  let w t := window (fun i : Nat => side t (i:Int)) (d+1) 0
  obtain ⟨a,b,ab,bc,eq⟩ := repeat_le (2^(d+1)) (fun t => encode (w t))
    (fun t _ => by simpa [w,window_len] using encode_bound (w t))
  have rows := same_encode_eq (by simp [w,window_len]) eq
  have matchAt (n : Nat) : ∀ i : Int,i≤(d:Int) → side (a+n) i=side (b+n) i := by
    induction n with
    | zero =>
      intro i hi
      by_cases neg : i<0
      · rw [vac _ _ neg,vac _ _ neg]
      · have low : i.toNat < d+1 := by omega
        have h := congrArg (fun xs : List Bool => xs[i.toNat]?) rows
        have take (v : Nat) : (w v)[i.toNat]?=some (side v i) := by
          change (List.ofFn (fun j : Fin (d+1) => side v ((0+j.val:Nat):Int)))[i.toNat]?=_
          rw [List.getElem?_ofFn]; simp [low,Int.toNat_of_nonneg (by omega : 0≤i)]
        rw [take,take] at h; exact Option.some.inj h
    | succ n ih =>
      intro i hi
      rw [show a+(n+1)=a+n+1 by omega,show b+(n+1)=b+n+1 by omega,
        law,law,ih (i-2) (by omega),ih (i-1) (by omega),ih i hi]
  refine ⟨b-a,by omega,by omega,?_⟩
  intro t ht k hk
  have h := matchAt (t-a) (k:Int) (by omega)
  rw [show a+(t-a)=t by omega,show b+(t-a)=t+(b-a) by omega] at h
  exact h.symm
private def EventuallyP (p : Nat) (j : Int) : Prop :=
  ∃ A, ∀ t≥A, side (t+p) j=side t j

private def EventuallyWhite (j : Int) : Prop :=
  ∃ A, ∀ t≥A, side t j=false

include law in
private theorem period_advance_of_recurring_black {p : Nat} {j : Int}
    (lo : EventuallyP side p (j-1)) (hi : EventuallyP side p j)
    (recurs : ¬ EventuallyWhite side j) :
    EventuallyP side p (j+1) := by
  obtain ⟨A,lo⟩ := lo
  obtain ⟨B,hi⟩ := hi
  obtain ⟨s,late,hit⟩ : ∃ s, max A B≤s ∧ side s j=true := by
    apply Classical.byContradiction
    intro misses
    apply recurs
    refine ⟨max A B,?_⟩
    intro t ht
    cases e : side t j
    · rfl
    · exact False.elim (misses ⟨t,ht,e⟩)
  have start : side (s+1+p) (j+1)=side (s+1) (j+1) := by
    rw [show s+1+p=s+p+1 by omega,law,law,
      show j+1-1=j by omega,show j+1-2=j-1 by omega,
      lo _ (by omega),hi _ (by omega),hit]
    cases side s (j-1) <;> cases side (s+p) (j+1) <;>
      cases side s (j+1) <;> rfl
  have stable (r : Nat) : side (s+1+r+p) (j+1)=side (s+1+r) (j+1) := by
    induction r with
    | zero => exact start
    | succ r prev =>
      rw [show s+1+(r+1)+p=s+1+r+p+1 by omega,
        show s+1+(r+1)=s+1+r+1 by omega,law,law,
        show j+1-1=j by omega,show j+1-2=j-1 by omega,
        lo _ (by omega),hi _ (by omega),prev]
  refine ⟨s+1,?_⟩
  intro t ht
  have e : t=s+1+(t-(s+1)) := by omega
  rw [e]
  exact stable _


include law vac in
/-- A bounded normalized prefix is already on a cycle by a bound
which depends only on its width. If a deep zero exists on every tick
after some later date, it must already hold throughout this cycle. -/
private theorem white_now (j t : Nat) (late : 2^(j+1)≤t)
    (white : EventuallyWhite side (j:Int)) : side t (j:Int)=false := by
  obtain ⟨p,hp,_,clock⟩ := prefix_cycle side law vac j
  obtain ⟨a,white⟩ := white
  have repeated := period_mul (fun s => side s (j:Int)) _ p
    (fun s hs => clock s hs j (by omega)) a t late
  have growth : a≤p*a := by simpa using Nat.mul_le_mul_right a hp
  exact repeated.symm.trans (white _ (by omega))

def laneCap (j : Nat) : Nat := j+2+2^(2^(j+2)+2^(j+2))

include law vac root in
/-- Uniform in all possible initial eastern tails, including the time
before which the lane could be transient. The growing bound is used
symbolically and is never enumerated. -/
theorem vacant_lane (j : Nat) :
    ∃ k,j≤k ∧ k≤laneCap j ∧ ∀ t,2^(laneCap j+1)≤t → side t (k:Int)=false := by
  let D := laneCap j
  obtain ⟨p,hp,pbound,small⟩ := prefix_cycle side law vac (j+1)
  have low (i : Nat) (hi : i≤j+1) : EventuallyP side p (i:Int) :=
    ⟨2^(j+1+1),fun t ht => small t ht i hi⟩
  have badRange : ∃ k,j≤k ∧ k≤D ∧ EventuallyWhite side (k:Int) := by
    apply Classical.byContradiction
    intro absent
    have all (n : Nat) (le : j+n≤D) :
        EventuallyP side p ((j+n:Nat):Int) ∧ EventuallyP side p ((j+n+1:Nat):Int) := by
      induction n with
      | zero => exact ⟨low _ (by omega),low _ (by omega)⟩
      | succ n ih =>
        obtain ⟨a,b⟩ := ih (by omega)
        have more := period_advance_of_recurring_black side law
          (j:=((j+n+1:Nat):Int)) (by simpa using a) b (fun e => absent ⟨_,by omega,by omega,e⟩)
        exact ⟨by simpa [Nat.add_assoc] using b,by
          rw [show ((j+(n+1)+1:Nat):Int)=((j+n+1:Nat):Int)+1 by omega];exact more⟩
    have lowD : j≤D := Nat.le_trans (Nat.le_add_right j 2) (Nat.le_add_right _ _)
    have ed : j+(D-j)=D := Nat.add_sub_of_le lowD
    obtain ⟨⟨a,pa⟩,⟨b,pb⟩⟩ := all (D-j) (by rw [ed];omega)
    rw [ed] at pa pb
    have lim := periodic_pair_width_bound side law vac root D (max a b) p hp
      (fun n hn => pa n (by omega)) (fun n hn => pb n (by omega))
    have mono := Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add pbound pbound)
    have bound : 2^(p+p)≤D := Nat.le_trans mono (Nat.le_add_left _ _)
    exact Nat.not_lt_of_ge bound lim
  obtain ⟨k,lo,hi,white⟩ := badRange
  exact ⟨k,lo,hi,fun t ht => white_now side law vac k t
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : k+1≤laneCap j+1)) ht) white⟩

include law vac root in
private theorem active_lane (j : Nat) :
    ∃ k,j≤k ∧ k≤laneCap j+2 ∧ ∀ t,2^(laneCap j+3)≤t → side t (k:Int)=true := by
  obtain ⟨w,ws,wb,white⟩ := vacant_lane side law vac root j
  let A := 2^(laneCap j+1)
  have noPair (n : Nat) (zero : ∀ t,A≤t → side t (n:Int)=false)
      (next : ∀ t,A≤t → side t ((n:Int)+1)=false) : False := by
    induction n with
    | zero => exact Bool.noConfusion ((root A).symm.trans (zero A (by omega)))
    | succ n ih =>
      have prev (t : Nat) (ht : A≤t) : side t (n:Int)=false := by
        have e := next (t+1) (by omega)
        rw [law,show ((↑(n+1):Int)+1)-2=n by omega,
          show ((↑(n+1):Int)+1)-1=(n+1:Nat) by omega,zero t ht,next t ht] at e
        simpa [rule] using e
      exact ih prev (fun t ht => by simpa using zero t ht)
  obtain ⟨r,rs,rh⟩ : ∃ r,A≤r ∧ side r ((w:Int)+1)=true := by
    apply Classical.byContradiction
    intro missing
    exact noPair w white (fun t ht => by
      cases e : side t ((w:Int)+1)
      · rfl
      · exact False.elim (missing ⟨t,ht,e⟩))
  have latch (t : Nat) (ht : A≤t) : side (t+1) ((w:Int)+2)=(side t ((w:Int)+1) || side t ((w:Int)+2)) := by
    rw [law,show ((w:Int)+2)-2=w by omega,show ((w:Int)+2)-1=(w:Int)+1 by omega,white t ht]
    simp [rule]
  have on (i : Nat) : side (r+1+i) ((w:Int)+2)=true := by
    induction i with
    | zero => simp [latch r rs,rh]
    | succ i ih => rw [show r+1+(i+1)=r+1+i+1 by omega,latch _ (by omega),ih,Bool.or_true]
  refine ⟨w+2,by omega,by omega,?_⟩
  intro t late
  obtain ⟨p,hp,_,per⟩ := prefix_cycle side law vac (w+2)
  have tcap : 2^(w+2+1)≤t := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : w+2+1≤laneCap j+3)) late
  have eq := period_mul (fun s => side s ((w+2:Nat):Int)) _ p
    (fun s hs => per s hs _ (by omega)) (r+1) t tcap
  have mul : r+1≤p*(r+1) := by simpa using Nat.mul_le_mul_right (r+1) hp
  rw [←eq,show t+p*(r+1)=r+1+(t+p*(r+1)-(r+1)) by omega]
  simpa using on (t+p*(r+1)-(r+1))

private def free (c : Trace) (s d : Nat) : Nat → Int → Bool
  | 0,j => if j<0 then false else east c s ((d:Int)+j).toNat
  | n+1,j => rule (free c s d n (j-2)) (free c s d n (j-1)) (free c s d n j)

private theorem free_vac (c : Trace) (s d t : Nat) (j : Int) (hj : j<0) :
    free c s d t j=false := by
  induction t generalizing j with
  | zero => simp [free,hj]
  | succ t ih => rw [free,ih (j-2) (by omega),ih (j-1) (by omega),ih j hj];rfl

private theorem free_mark (c : Trace) (s d : Nat) (hit : east c s d=true) (t : Nat) :
    free c s d t 0=true := by
  induction t with
  | zero => simpa [free] using hit
  | succ t ih => rw [free,free_vac _ _ _ _ _ (by decide),free_vac _ _ _ _ _ (by decide),ih];rfl

/-- The actual white-clamped east and the normalized free front coincide
until the disturbance of the wall can reach the indicated coordinate. -/
private theorem compare_free (c : Trace) (s h d : Nat)
    (wh : ∀ j,j<h → c (s+j)=false)
    (clear : ∀ y,0<y → y<d → east c s y=false) :
    ∀ i,i≤h → ∀ x,i<d+x → (0<x ∨ i<h) →
      east c (s+i) x=free c s d i ((x:Int)+i-d) := by
  intro i
  induction i with
  | zero =>
    intro _ x _ visible
    by_cases neg : (x:Int)-d<0
    · rw [free_vac _ _ _ _ _ (by omega)]
      cases x with
      | zero => simpa [east0] using wh 0 (by rcases visible with a|a <;> omega)
      | succ x => exact clear _ (by omega) (by omega)
    · simp [free,show (d:Int)+((x:Int)-d)=x by omega] <;> omega
  | succ i ih =>
    intro lim x bound visible
    cases x with
    | zero =>
      rw [east0,free_vac _ _ _ _ _ (by omega)]
      apply wh;rcases visible with h|h <;> omega
    | succ x =>
      change rule (east c (s+i) x) (east c (s+i) (x+1)) (east c (s+i) (x+2))=_
      rw [free,ih (by omega) x (by omega) (Or.inr (by omega)),
        ih (by omega) (x+1) (by omega) (Or.inl (by omega)),
        ih (by omega) (x+2) (by omega) (Or.inl (by omega))]
      congr 1 <;> congr 1 <;> omega

/-- Compare past the end of the white run while the changed wall is
outside the backward cone. The later bridge may have any bit pattern. -/
private theorem bridge_free (c : Trace) (s h d : Nat)
    (wh : ∀ j,j<h → c (s+j)=false)
    (clear : ∀ y,0<y → y<d → east c s y=false) :
    ∀ i x,i<d+x → i<h+x →
      east c (s+i) x=free c s d i ((x:Int)+i-d) := by
  intro i
  induction i with
  | zero =>
    intro x bound safe
    exact compare_free c s h d wh clear 0 (by omega) x bound (by omega)
  | succ i ih =>
    intro x bound safe
    cases x with
    | zero =>
      rw [east0,free_vac _ _ _ _ _ (by omega)]
      exact wh _ (by omega)
    | succ x =>
      change rule (east c (s+i) x) (east c (s+i) (x+1)) (east c (s+i) (x+2))=_
      rw [free,ih x (by omega) (by omega),ih (x+1) (by omega) (by omega),
        ih (x+2) (by omega) (by omega)]
      congr 1 <;> congr 1 <;> omega

private theorem early_ready (c : Trace) (s h d : Nat) (pos : 0<d) (room : d+8≤h)
    (wh : ∀ j,j<h → c (s+j)=false) (clear : ∀ y,0<y → y<d → east c s y=false)
    (hit : east c s d=true) : Ready c (s+h) := by
  have arrive := compare_free c s h d wh clear (d-1) (by omega) 1 (by omega) (Or.inl (by omega))
  rw [show ((1:Nat):Int)+(d-1:Nat)-d=0 by omega,free_mark c s d hit] at arrive
  have high (i : Nat) (lo : d-1≤i) (hi : i≤h) : east c (s+i) 1=true := by
    have held := head_hold c (s+(d-1)) (i-(d-1)) arrive (fun j hj => by
      rw [show s+(d-1)+j=s+(d-1+j) by omega];exact wh _ (by omega))
    rwa [show s+(d-1)+(i-(d-1))=s+i by omega] at held
  have lock := black_pair c 1 (s+h-9) (fun i hi => by
    rw [show s+h-9+i=s+(h-9+i) by omega];exact high _ (by omega) (by omega))
  rw [show s+h-9+9=s+h by omega] at lock
  exact ⟨high h (by omega) (by omega),lock⟩

private theorem white_triangle (c : Trace) (s h w : Nat)
    (wh : ∀ j,j<h → c (s+j)=false)
    (clear : ∀ i,0<i → i≤w → east c s i=false) :
    ∀ k,k≤h → ∀ i,0<i → i+k≤w → east c (s+k) i=false := by
  intro k
  induction k with
  | zero => intro hk i ip ls;exact clear i ip (by omega)
  | succ k ih =>
    intro hk i ip ls
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i≠0 by omega)
    have low : east c (s+k) n=false := by
      cases n with
      | zero => rw [east0,wh k (by omega)]
      | succ n => exact ih (by omega) _ (by omega) (by omega)
    change rule (east c (s+k) n) (east c (s+k) (n+1)) (east c (s+k) (n+2))=false
    rw [low,ih (by omega) (n+1) (by omega) (by omega),ih (by omega) (n+2) (by omega) (by omega)]
    rfl

/-- A black wall and an old zero at x cannot be followed by x+1
strict eastern zeros. The proof backs the last 00 up to the wall. -/
private theorem next_hit (c : Trace) (t x : Nat) (black : c t=true) (zero : east c t x=false) :
    ∃ y,0<y ∧ y≤x+1 ∧ east c (t+1) y=true := by
  induction x with
  | zero => rw [east0,black] at zero;contradiction
  | succ x ih =>
    by_cases near : east c (t+1) (x+1)=true
    · exact ⟨_,by omega,by omega,near⟩
    by_cases far : east c (t+1) (x+2)=true
    · exact ⟨_,by omega,by omega,far⟩
    have p : east c t x=false := by
      change ¬rule (east c t x) _ _=true at near
      change ¬rule (east c t (x+1)) _ _=true at far
      cases a : east c t x <;> cases b : east c t (x+2) <;> simp_all [rule]
    obtain ⟨y,pos,le,e⟩ := ih p
    exact ⟨y,pos,by omega,e⟩

private theorem first_in (c : Trace) (s w : Nat)
    (any : ∃ k,0<k ∧ k≤w ∧ east c s k=true) :
    ∃ d,0<d ∧ d≤w ∧ east c s d=true ∧ ∀ k,0<k → k<d → east c s k=false := by
  induction w with
  | zero => obtain ⟨_,_,_,_⟩ := any;omega
  | succ w ih =>
    by_cases earlier : ∃ k,0<k ∧ k≤w ∧ east c s k=true
    · obtain ⟨d,p,b,o,v⟩ := ih earlier;exact ⟨d,p,by omega,o,v⟩
    · obtain ⟨k,p,b,o⟩ := any
      exact ⟨k,p,b,o,fun i pi lo => by
        cases z : east c s i
        · rfl
        · exact False.elim (earlier ⟨i,pi,by omega,z⟩)⟩

/-- Lengths finite but not tuned to a simulated front. -/
private def settle (J : Nat) := 2^(laneCap J+1)+laneCap J+20

theorem bounded_after_pulse (J : Nat) (margin : 24≤J) (c : Trace) (s h : Nat) (long : settle J≤h)
    (wh : ∀ j,j<h → c (s+j)=false) (black : c (s+h)=true) :
    ∃ y,0<y ∧ y≤laneCap J+3 ∧ east c (s+h+1) y=true := by
  by_cases any : ∃ k,0<k ∧ k≤h+2 ∧ east c s k=true
  · obtain ⟨d,pos,le,hit,clear⟩ := first_in c s (h+2) any
    by_cases early : d+8≤h
    · obtain ⟨a,b,g⟩ := early_ready c s h d pos early wh clear hit
      refine ⟨3,by omega,by omega,?_⟩
      change rule (east c (s+h) 2) _ _=true
      rw [b,g];rfl
    · obtain ⟨j,lo,hi,stable⟩ := vacant_lane (free c s d) (fun _ _ => rfl)
        (free_vac c s d) (free_mark c s d hit) J
      have z := stable h (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) long)
      let x := j+d-h
      have cmp := compare_free c s h d wh clear h (by omega) x
        (by dsimp [x];omega) (Or.inl (by dsimp [x];omega))
      rw [show ((x:Int)+h-d)=(j:Int) by dsimp [x];omega,z] at cmp
      obtain ⟨y,p,b,e⟩ := next_hit c (s+h) x black cmp
      exact ⟨y,p,by dsimp [x] at b;omega,e⟩
  · have empty (i : Nat) (pi : 0<i) (le : i≤h+2) : east c s i=false := by
      cases z : east c s i
      · rfl
      · exact False.elim (any ⟨i,pi,le,z⟩)
    have tri := white_triangle c s h (h+2) wh empty h (by omega)
    refine ⟨1,by omega,by omega,?_⟩
    change rule (east c (s+h) 0) _ _=true
    rw [east0,black,tri 1 (by omega) (by omega),tri 2 (by omega) (by omega)]
    rfl

/-- This condition mentions only the clock. It needs no eastern
admission certificate, no common future of two differing right tapes,
and no assumption about the part of the history preceding f(0). -/
def SparsePulseClock (c : Trace) : Prop :=
  ∃ f : Nat → Nat, ∀ k,c (f k)=true ∧ f k+settle 24+1≤f (k+1) ∧
    ∀ i,f k<i → i<f (k+1) → c i=false

private theorem enter_sparse (J : Nat) (margin : 24≤J) (c : Trace) (f : Nat → Nat)
    (seq : ∀ k,c (f k)=true ∧ f k+settle J+1≤f (k+1) ∧
        ∀ i,f k<i → i<f (k+1) → c i=false) : PulseBasin c := by
  have room : laneCap J+11≤settle J :=
    Nat.add_le_add (Nat.le_add_left (laneCap J) _) (by decide : 11≤20)
  have gap (k : Nat) : f k+12≤f (k+1) := by have := (seq k).2.1;omega
  let h (k : Nat) := f (k+1)-(f k+1)
  have ends (k : Nat) : f k+1+h k=f (k+1) := by dsimp [h];have := gap k;omega
  have long (k : Nat) : settle J≤h k := by dsimp [h];have := (seq k).2.1;omega
  have held (k i : Nat) (ls : i<h k) : c (f k+1+i)=false :=
    (seq k).2.2 _ (by omega) (by have := ends k;omega)
  have blk (k : Nat) : c (f k+1+h k)=true := by rw [ends];exact (seq _).1
  obtain ⟨x,xp,xb,occ⟩ := bounded_after_pulse J margin c _ _ (long 0) (held 0) (blk 0)
  rw [ends] at occ
  obtain ⟨d,dp,db,hit,empty⟩ := first_in c (f 1+1) x ⟨x,xp,by omega,occ⟩
  have rd := early_ready c (f 1+1) (h 1) d dp (by have := long 1;omega) (held 1) empty hit
  rw [ends] at rd
  refine ⟨fun k => f (2+k),by simpa using rd,?_⟩
  intro k
  exact ⟨(seq _).1,gap _,(seq _).2.2⟩

theorem excludes_sparse (c : Trace) (ep : EventuallyPeriodic c) (mark : c 0=true)
    (black : BlackLock c) (join : Joined c) : ¬SparsePulseClock c := by
  rintro ⟨f,z⟩
  exact excludes_pulse_basin _ mark ep black join (enter_sparse 24 (Nat.le_refl _) c f z)

/-- Behind a high head the stationary checker grows two cells per
nine ticks. This statement applies at any physical column. -/
private theorem checker (c : Trace) (x s h n : Nat)
    (held : ∀ i,i≤h → east c (s+i) x=true) :
    ∀ i,9*n≤i → i≤h →
      east c (s+i) (x+2*n)=true ∧
        (0<n → east c (s+i) (x+2*n-1)=false) := by
  induction n with
  | zero => intro i lo hi;exact ⟨by simpa using held i hi,by omega⟩
  | succ n ih =>
    intro i lo hi
    have z := black_pair c (x+2*n) (s+i-9) (fun a ha => by
      rw [show s+i-9+a=s+(i-9+a) by omega]
      exact (ih _ (by omega) (by omega)).1)
    rw [show s+i-9+9=s+i by omega] at z
    exact ⟨by simpa [Nat.mul_succ,Nat.add_assoc] using z.2,fun _ => by
      rw [show x+2*(n+1)-1=x+2*n+1 by omega];exact z.1⟩

private def CheckerAt (c : Trace) (t width : Nat) : Prop :=
  ∀ k,0<k → k≤width → east c t k=decide (k%2=1)

private theorem early_checker (c : Trace) (s h d m : Nat) (pos : 0<d)
    (room : d+9*(m+2)≤h) (wh : ∀ j,j<h → c (s+j)=false)
    (clear : ∀ y,0<y → y<d → east c s y=false) (hit : east c s d=true) :
    CheckerAt c (s+h) (2*m+4) := by
  have arrive := compare_free c s h d wh clear (d-1) (by omega) 1 (by omega) (Or.inl (by omega))
  rw [show ((1:Nat):Int)+(d-1:Nat)-d=0 by omega,free_mark c s d hit] at arrive
  have high (i : Nat) (ls : i≤h-(d-1)) : east c (s+(d-1)+i) 1=true := by
    exact head_hold c (s+(d-1)) i arrive (fun j hj => by
      rw [show s+(d-1)+j=s+(d-1+j) by omega];exact wh _ (by omega))
  intro k pk uk
  have eq := checker c 1 (s+(d-1)) (h-(d-1)) (k/2) high (h-(d-1)) (by omega) (by omega)
  rw [show s+(d-1)+(h-(d-1))=s+h by omega] at eq
  by_cases odd : k%2=1
  · rw [decide_eq_true odd,show k=1+2*(k/2) by omega];exact eq.1
  · rw [decide_eq_false odd,show k=1+2*(k/2)-1 by omega];exact eq.2 (by omega)

private theorem checker_survives (c : Trace) (t width : Nat) (ch : CheckerAt c t width) :
    ∀ i x,i<x → x+i≤width → east c (t+i) x=decide (x%2=1) := by
  intro i
  induction i with
  | zero => intro x pos lim;exact ch x pos lim
  | succ i ih =>
    intro x pos lim
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show x≠0 by omega)
    change rule (east c (t+i) k) (east c (t+i) (k+1)) (east c (t+i) (k+2))=_
    rw [ih k (by omega) (by omega),ih (k+1) (by omega) (by omega),ih (k+2) (by omega) (by omega)]
    by_cases odd : k%2=1
    · simp [rule,odd,show ¬(k+1)%2=1 by omega,show (k+2)%2=1 by omega]
    · simp [rule,odd,show (k+1)%2=1 by omega]

private theorem checker_content (c : Trace) (t m : Nat) (ch : CheckerAt c t (2*m+4)) :
    ∃ y,0<y ∧ y≤m+2 ∧ east c (t+m) y=true := by
  let y := if m%2=0 then m+1 else m+2
  have z := checker_survives c t _ ch m y (by dsimp [y];split <;> omega)
    (by dsimp [y];split <;> omega)
  refine ⟨y,by dsimp [y];split <;> omega,by dsimp [y];split <;> omega,?_⟩
  rw [z];apply decide_eq_true;dsimp [y];split <;> omega

private theorem first_flash (c : Trace) (t m : Nat)
    (black : c t=true) (empty : ∀ i,0<i → i≤2*m → east c t i=false) :
    east c (t+m) m=true := by
  have triangle (k : Nat) (small : k≤m) :
      east c (t+k) k=true ∧ ∀ i,k<i → i+k≤2*m → east c (t+k) i=false := by
    induction k with
    | zero => exact ⟨by simpa [east0] using black,fun i ip sz => empty i ip sz⟩
    | succ k ih =>
      obtain ⟨mark,z⟩ := ih (by omega)
      constructor
      · change rule (east c (t+k) k) (east c (t+k) (k+1)) (east c (t+k) (k+2))=true
        rw [mark,z _ (by omega) (by omega),z _ (by omega) (by omega)];rfl
      · intro i lo hi
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i≠0 by omega)
        change rule (east c (t+k) j) (east c (t+k) (j+1)) (east c (t+k) (j+2))=false
        rw [z _ (by omega) (by omega),z _ (by omega) (by omega),z _ (by omega) (by omega)];rfl
  exact (triangle m (by omega)).1

def bridgeJ (m : Nat) := 24*m+48
def bridgeK (m : Nat) := laneCap (bridgeJ m)+2*m+4
def bridgeH (m : Nat) := 2^(laneCap (bridgeJ m)+3)+bridgeK m+9*(m+2)+1

/-- All m-bit bridges beginning black qualify, not just isolated
black pulses. No value of any other bridge bit is assumed. -/
theorem renewal (c : Trace) (s h m : Nat) (ml : 0<m) (long : bridgeH m≤h)
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

/-- L1: at least ONE arm of an actual marked collision challenges the
inverse predictor on a capable label. This does not require either
recurrence of the endpoint word or coincidence of the two endpoint words. -/
theorem L1 (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (outside : ¬PulseBasin c ∧ ¬RenewalFront.SparsePulseClock c ∧ ¬RenewalFront.Bridged c) (short : ¬RenewalFront.PulseWindows c) (starts : ResetStarts c T P) :
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

/-- L2: exclude the two surviving actual escape classes on an arm
from sufficiently deep matched reset starts. It says nothing about
unmatched cuts, bounded source collars, or any other phase or word. -/
theorem L2 (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (outside : ¬PulseBasin c ∧ ¬RenewalFront.SparsePulseClock c ∧ ¬RenewalFront.Bridged c)
    (short : ¬RenewalFront.PulseWindows c) :
    ∃ n,CollisionStop c T P n := by
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
  obtain ⟨n,stop⟩ := L2 c T P hp mark period mixed past black outside noWindows
  obtain ⟨t,v,late,arm,cap,bad⟩ := L1 c T P hp mark period mixed past black outside noWindows
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
#print axioms OpenProblem.AncestryBlueprint.windows_stop
#print axioms OpenProblem.AncestryBlueprint.RenewalFront.excludes_bridged
#print axioms OpenProblem.AncestryBlueprint.RenewalFront.excludes_sparse
#print axioms OpenProblem.AncestryBlueprint.excludes_pulse_basin
#print axioms OpenProblem.AncestryBlueprint.west_rich
#print axioms OpenProblem.AncestryBlueprint.close_step4
