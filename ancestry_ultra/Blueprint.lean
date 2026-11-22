import Statement
import MaskedRightRigidity

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

private theorem zero_only (s : Nat) (fixed : r8turn s=s) (hi : 10≤r8rank s) : s=0 := by
  by_cases a : s=57 <;> try (subst s;contradiction)
  by_cases b : s=206 <;> try (subst s;contradiction)
  by_cases d : s=115 <;> try (subst s;contradiction)
  by_cases e : s=156 <;> try (subst s;contradiction)
  by_cases f : s=231 <;> try (subst s;contradiction)
  have next : r8next s=0 := by unfold r8next; split <;> simp_all
  simpa [r8turn,next,r8next] using fixed.symm

private theorem rank_le_range (c : Trace) (a t : Nat)
    (all : ∀i,a≤i → i≤t → noreset c i=true) (i j : Nat) (ai : a≤i) (ij : i≤j) (jt : j≤t) :
    r8rank (r8state c j)≤r8rank (r8state c i) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ij
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact Nat.le_trans (r8local c (i+k) (all _ (by omega) (by omega))
      (all _ (by omega) (by omega))).1 (ih (by omega) (by omega))

/-- A nonreset path ending in old east8=0 cannot idle anywhere
except zero (the competing 5-cycle lies below rank ten). At most five
strict decreases fit above rank ten. A black drive P ticks earlier
then forces escape from zero, which cannot return on this path. -/
private theorem prior_zero_reset (c : Trace) (T P t : Nat) (hp : 0<P)
    (period : ∀i,T≤i → c (i+P)=c i) (late : T+P+6≤t)
    (black : c t=true) (zero : r8state c t=0) :
    ∃ i,i≤t ∧ t≤i+P+6 ∧ noreset c i=false := by
  classical
  apply Classical.byContradiction
  intro none
  let a := t-(P+6)
  let b := t-P
  have ab : a+6=b := by dsimp [a,b];omega
  have final : b+P=t := by dsimp [b];omega
  have all (i : Nat) (ai : a≤i) (it : i≤t) : noreset c i=true := by
    cases atI : noreset c i
    · exact False.elim (none ⟨i,it,by dsimp [a] at ai;omega,atI⟩)
    · rfl
  let R i := r8rank (r8state c i)
  have bottom : R t=10 := by dsimp [R];rw [zero];decide
  have low (i : Nat) (ai : a≤i) (it : i≤t) : 10≤R i := by
    rw [←bottom];exact rank_le_range c a t all i t ai it (Nat.le_refl _)
  have pers (i : Nat) (ai : a≤i) (it : i≤t) (z : r8state c i=0)
      (j : Nat) (ij : i≤j) (jt : j≤t) : r8state c j=0 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ij
    induction k with
    | zero => simpa using z
    | succ k ih =>
      have old := ih (by omega) (by omega)
      have r : R (i+k)=10 := by dsimp [R];rw [old];decide
      have e := r8local c (i+k) (all _ (by omega) (by omega)) (all _ (by omega) jt)
      have lo := low (i+k+1) (by omega) jt
      have eq : R (i+k+1)=R (i+k) := Nat.le_antisymm e.1 (by omega)
      rw [←Nat.add_assoc,(e.2 eq).1,old];rfl
  have zb : r8state c b=0 := by
    apply Classical.byContradiction
    intro nz
    have strict (i : Nat) (ai : a≤i) (ib : i<b) : R (i+1)<R i := by
      have endle : i+1≤t := by omega
      have e := r8local c i (all _ ai (by omega)) (all _ (by omega) endle)
      by_cases eq : R (i+1)=R i
      · have z := zero_only _ ((e.2 eq).2.2) (low i ai (by omega))
        exact False.elim (nz (pers i ai (by omega) z b (by omega) (by omega)))
      · exact Nat.lt_of_le_of_ne e.1 eq
    have drops (k : Nat) (kb : k≤6) : R (a+k)+k≤R a := by
      induction k with
      | zero => simp
      | succ k ih =>
        have := ih (by omega)
        have s := strict (a+k) (by omega) (by omega)
        rw [show a+(k+1)=a+k+1 by omega];omega
    have upper : R a<16 := Nat.mod_lt _ (by decide)
    have limit := drops 6 (by decide)
    rw [ab] at limit
    have lo := low b (by omega) (by omega)
    omega
  have zn := pers b (by omega) (by omega) zb (b+1) (by omega) (by omega)
  have bt : c b=true := by rw [←period b (by dsimp [b];omega),final,black]
  have raise : ∀ a b d e f g h z : Bool,
      r8code a b d e f g h z=0 → rule true a b=true := by decide
  have one : east c (b+1) 1=true := by
    change rule (east c b 0) (east c b 1) (east c b 2)=true
    rw [east0,bt]
    exact raise _ _ _ _ _ _ _ _ zb
  have clear : ∀ a b d e f g h z : Bool,r8code a b d e f g h z=0 → a=false := by decide
  have zz : east c (b+1) 1=false := clear _ _ _ _ _ _ _ _ zn
  rw [one] at zz
  contradiction

/-- The two possible wrong arms occupy short gaps BETWEEN actual
resets, with an exact post-reset one tick after their exceptional
eight-bit state. For 91 the prior reset is at one of two named ticks. -/
def Bracket (c : Trace) (P t : Nat) (w : Seven) : Prop :=
  noreset c (t+3)=false ∧
    (code w=67 → ∃ i,i≤t ∧ t≤i+P+6 ∧ noreset c i=false) ∧
    (code w=91 → noreset c t=false ∨ noreset c (t+1)=false)

private theorem actual_bracket (c : Trace) (T P t : Nat) (hp : 0<P)
    (period : ∀i,T≤i → c (i+P)=c i) (late : T+P+6≤t) (black : c t=true)
    (w : Seven) (word : seven c (t+2)=w) (cut : BlackCut c t w)
    (bit : east c (t+2) 8=true) (unsync : reset w (east c (t+2) 8)=false) : Bracket c P t w := by
  have nr : noreset c (t+2)=true := by simp only [noreset,word,unsync,Bool.not_false]
  have st : r8state c (t+2)=code w+128 := by simp [r8state,word,bit]
  rcases cut with ⟨id,old,old8,_⟩|⟨id,_,prior⟩
  · rw [id] at st
    have after := next_reset_of_dead c (t+2) nr (by rw [st];decide) (by rw [st];decide)
    have zero : r8state c t=0 := by simp [r8state,old,old8]
    exact ⟨after,fun _ => prior_zero_reset c T P t hp period late black zero,fun h => by omega⟩
  · rw [id] at st
    have after := next_reset_of_dead c (t+2) nr (by rw [st];decide) (by rw [st];decide)
    refine ⟨after,fun h => by omega,fun _ => ?_⟩
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

/-- L1: at least ONE arm of an actual marked collision challenges the
inverse predictor on a capable label. This does not require either
recurrence of the endpoint word or coincidence of the two endpoint words. -/
theorem L1 (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (starts : ResetStarts c T P) :
    ∀ N d h, ∃ t v,N≤t ∧ Arm c T P d h t v ∧ capable (seven c (t+2))=true ∧
      need c (t+1)≠guess (seven c (t+2)) := by
  sorry

/-- L2: exclude the two surviving actual escape classes on an arm
from sufficiently deep matched reset starts. It says nothing about
unmatched cuts, bounded source collars, or any other phase or word. -/
theorem L2 (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) :
    ∃ n, ∀ t v,n≤t → Arm c T P n n t v → c t=true → c (t+1)=false → east c t 1=false →
      let w := seven c (t+2)
      (code w=67 ∨ code w=91) → BlackCut c t w → Bracket c P t w →
      xor (west c t 2) (east c t 2)=c (t+2) → east c (t+2) 8=true →
      reset w (east c (t+2) 8)=false → east c (t+1) 1=guess w := by
  sorry

private theorem stays_high (c : Trace) (t : Nat) (white : c t=false) (old : east c t 1=true) :
    east c (t+1) 1=true := by
  change rule (east c t 0) (east c t 1) (east c t 2)=true
  rw [east0,white,old]
  simp [rule]

theorem collision (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (join : Joined c) : False := by
  obtain ⟨n,stop⟩ := L2 c T P hp mark period mixed past black
  obtain ⟨t,v,late,arm,cap,bad⟩ := L1 c T P hp mark period mixed past black
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
    have br := actual_bracket c T P t hp period (by omega) bw _ rfl cut bit unsync
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
#print axioms OpenProblem.AncestryBlueprint.west_rich
#print axioms OpenProblem.AncestryBlueprint.close_step4
