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

def Visit (c : Trace) (P p : Nat) (w : Seven) (t : Nat) : Prop :=
  t%P=p ∧ c t=false ∧ seven c (t+1)=w

def WesternFork (c : Trace) (P p : Nat) (w : Seven) : Prop :=
  ∀ N (b : Bool), ∃ t, N≤t ∧ Visit c P p w t ∧ need c t=b

/-- L1: only a seven-bit projection is tagged. It is enough that some
eighth extension resets; neither actual eighth input is required to reset.
The entire white stream is not assumed correct: only the pre-onset
prefix and the exact black locks are given. -/
theorem L1 (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (rich : ¬EventuallyPeriodic (whiteNeed c)) :
    ∃ p w, p<P ∧ capable w=true ∧ WesternFork c P p w := by
  sorry

/-- L2 is restricted to the four physical escape words. It only bars
cofinal joint use of the nonreset, high-eighth escape with the opposite
old head IN A western-fork class, not arbitrary right words or clocks.
No late white agreement is assumed. -/
theorem L2 (c : Trace) (T P p : Nat) (w : Seven) (hp : 0<P) (ph : p<P)
    (mark : c 0=true) (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (cap : capable w=true)
    (special : exceptional w=true) (fork : WesternFork c P p w) :
    ∃ N, ∀ t, N≤t → Visit c P p w t → east c (t+1) 8=true →
      reset w (east c (t+1) 8)=false → east c t 1=guess w := by
  sorry

theorem collision (c : Trace) (T P : Nat) (hp : 0<P) (mark : c 0=true)
    (period : ∀t,T≤t → c (t+P)=c t) (mixed : Mixed c)
    (past : Prefix c T) (black : BlackLock c) (join : Joined c) : False := by
  have rich := west_rich c mark ⟨T,P,hp,period⟩ black
  obtain ⟨p,w,ph,cap,fork⟩ := L1 c T P hp mark period mixed past black rich
  have escaped (N : Nat) : ∃t, N≤t ∧ Visit c P p w t ∧ east c t 1≠guess w ∧
      exceptional w=true ∧ east c (t+1) 8=true ∧ reset w (east c (t+1) 8)=false := by
    obtain ⟨t,late,v,needOpp⟩ := fork N (!guess w)
    have outside : east c t 1≠guess w := by
      rw [←join t v.2.1,needOpp]
      simp
    obtain ⟨spec,bit,unsync⟩ := decoder_bound c t v.2.1 (by rwa [v.2.2]) (by rwa [v.2.2])
    rw [v.2.2] at spec unsync
    exact ⟨t,late,v,outside,spec,bit,unsync⟩
  obtain ⟨_,_,_,_,special,_,_⟩ := escaped 0
  obtain ⟨N,stop⟩ := L2 c T P p w hp ph mark period mixed past black cap special fork
  obtain ⟨t,late,v,different,_,bit,unsync⟩ := escaped N
  exact different (stop t late v bit unsync)

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
#print axioms OpenProblem.AncestryBlueprint.west_rich
#print axioms OpenProblem.AncestryBlueprint.close_step4
