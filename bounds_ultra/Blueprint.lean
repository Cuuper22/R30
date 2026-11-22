import Statement
import OutgoingClock
import MaskedRightRigidity
import FiniteWaveAnchors

/-! Route A. Laurent coefficients are represented by their integer exponent.
Multiplication by z + z⁻¹ is the linear Rule 90 propagator. Rule 30 injects
one unit at each right endpoint of a black run. Separate the unique outer
endpoint from all interior endpoints, at EVERY genuine singleton row. -/
namespace OpenProblem.BoundsBlueprint

def westSatellite (t : Nat) (x : Int) : Bool := decide (2≤t ∧ x=1-(t:Int))

def interiorSource (t : Nat) (x : Int) : Bool :=
  ((cell t x && !(cell t (x + 1))) && decide (x ≠ (t : Int))) && !westSatellite t x

/-- Parity of all paths from genuine interior black-run endpoints to (t,x). -/
def interior : Nat → Int → Bool
  | 0, _ => false
  | t + 1, x => xor (xor (interior t (x-1)) (interior t (x+1))) (interiorSource t x)

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

private theorem leftVac (t : Nat) (x : Int) (h : x < -(t:Int)) : cell t x=false := by
  induction t generalizing x with
  | zero => simp [cell];omega
  | succ t ih =>
    simp only [cell,rule]
    rw [ih (x-1) (by omega),ih x (by omega),ih (x+1) (by omega)]
    rfl

private theorem leftMark (t : Nat) : cell t (-(t:Int))=true := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [cell,rule]
    rw [show -((t+1:Nat):Int)+1= -(t:Int) by omega,ih,leftVac t _ (by omega),leftVac t _ (by omega)]
    rfl

private theorem leftOne (t : Nat) : cell (t+1) (-(t:Int))=true := by
  simp [cell,rule,leftVac t _ (show -(t:Int)-1 < -(t:Int) by omega),leftMark]

private theorem leftTwo (t : Nat) : cell (t+2) (-(t:Int))=false := by
  simp only [cell,rule]
  change rule (cell (t+1) (-(t:Int)-1)) (cell (t+1) (-(t:Int))) (cell (t+1) (-(t:Int)+1))=false
  rw [show -(t:Int)-1= -((t+1:Nat):Int) by omega,leftMark,leftOne];rfl

private theorem source_split (t : Nat) (x : Int) :
    (cell t x && !(cell t (x+1))) =
      xor (xor (decide (x=(t:Int))) (westSatellite t x)) (interiorSource t x) := by
  by_cases h : x=(t:Int)
  · subst x
    have n : ¬(2≤t ∧ (t:Int)=1-(t:Int)) := by omega
    simp [interiorSource,westSatellite,n,rightMark,rightVac t ((t:Int)+1) (by omega)]
  by_cases w : 2≤t ∧ x=1-(t:Int)
  · obtain ⟨m,hm⟩ : ∃ m, t=m+2 := ⟨t-2,by omega⟩
    have a : cell t x=true := by
      rw [hm, show x= -((m+1:Nat):Int) by omega];exact leftOne (m+1)
    have b : cell t (x+1)=false := by
      rw [hm,show x+1= -(m:Int) by omega];exact leftTwo m
    have marked : westSatellite t x=true := decide_eq_true w
    simp [interiorSource,marked,h,a,b]
  · simp [interiorSource,westSatellite,h,w]

/-- Response of the true 10 at x=1-t, present at every t≥2. -/
def westFringe (t : Nat) (x : Int) : Bool :=
  if t<2 then false else xor (wave (t-2) (x+2)) (decide (x= -(t:Int)))

private theorem westFringe_step (t : Nat) (x : Int) :
    westFringe (t+1) x=xor (xor (westFringe t (x-1)) (westFringe t (x+1))) (westSatellite t x) := by
  match t with
  | 0 => simp [westFringe,westSatellite]
  | 1 =>
    have eq : (x+2=0) ↔ x=(-2:Int) := by omega
    simp [westFringe,westSatellite,wave,eq]
  | n+2 =>
    have a : (x-1= -((n+2:Nat):Int)) ↔ x=1-((n+2:Nat):Int) := by omega
    have b : (x+1= -((n+2:Nat):Int)) ↔ x= -((n+2+1:Nat):Int) := by omega
    simp only [westFringe,westSatellite,show ¬n+2<2 by omega,show ¬n+2+1<2 by omega,
      show 2≤n+2 by omega,ite_false,true_and,show n+2+1-2=n+1 by omega,
      show n+2-2=n by omega,wave,a,b]
    rw [show x+2-1=x-1+2 by omega,show x+2+1=x+1+2 by omega]
    generalize wave n (x-1+2)=a; generalize wave n (x+1+2)=b
    generalize decide (x= -((n+2+1:Nat):Int))=c;generalize decide (x=1-((n+2:Nat):Int))=d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

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
    cell t x = xor (xor (fringe t x) (westFringe t x)) (interior t x) := by
  induction t generalizing x with
  | zero =>
    simp only [cell, interior, fringe, westFringe, show 0<2 by decide, ite_true, wave, Bool.xor_false]
    have h : (x-1=0) ↔ (x=(0:Nat)+1) := by omega
    simp only [h]
    generalize decide (x=0)=a
    generalize decide (x=(0:Nat)+1)=b
    cases a <;> cases b <;> rfl
  | succ t ih =>
    simp only [cell, local_split, interior, fringe_step,westFringe_step]
    rw [source_split, ih (x-1), ih (x+1)]
    generalize fringe t (x-1)=a; generalize fringe t (x+1)=b
    generalize interior t (x-1)=c; generalize interior t (x+1)=d
    generalize decide (x=(t:Int))=e; generalize interiorSource t x=f
    generalize westFringe t (x-1)=g;generalize westFringe t (x+1)=h;generalize westSatellite t x=i
    simp only [Bool.xor_left_comm,Bool.xor_comm]

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

private theorem west_odd (m : Nat) : westFringe (2*m+1) 0=false := by
  cases m with
  | zero => rfl
  | succ n =>
    have a : wave (2*n) 1=false := (wave_double n 0).2
    have b : wave (2*n) 3=false := by
      have z := (wave_double n 1).2
      rwa [show (2*(1:Int)+1)=3 by decide] at z
    have non : ¬(0:Int)= -((2*(n+1)+1:Nat):Int) := by omega
    simp only [westFringe,show ¬2*(n+1)+1<2 by omega,ite_false,non,decide_false,Bool.xor_false,
      show 2*(n+1)+1-2=2*n+1 by omega]
    change xor (wave (2*n) 1) (wave (2*n) 3)=false
    rw [a,b];rfl

private theorem west_even (m : Nat) (hm : 0<m) :
    westFringe (2*(m+1)) 0 = fringe m 0 := by
  have non : ¬(0:Int)= -((2*(m+1):Nat):Int) := by omega
  simp only [westFringe,show ¬2*(m+1)<2 by omega,ite_false,non,decide_false,Bool.xor_false,
    show 2*(m+1)-2=2*m by omega,central_fringe]
  have db := (wave_double m 1).1
  rw [show (2*(1:Int))=2 by decide] at db
  change wave (2*m) 2 = xor (wave m 0) (wave m (-1))
  rw [db,wave_reflect m 1]
  have zero : wave m 0=false := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm);exact wave_center j
  simp [zero]

/-- Right-normalized Laurent multiplication by (1+z²), repeated n times. -/
private def walk : Nat → (Int → Bool) → Int → Bool
  | 0, f, x => f x
  | t+1, f, x => xor (walk t f x) (walk t f (x-2))

private theorem walk_xor (t : Nat) (f g : Int → Bool) (x : Int) :
    walk t (fun y => xor (f y) (g y)) x = xor (walk t f x) (walk t g x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    simp only [walk,ih]
    generalize walk t f x=a; generalize walk t g x=b
    generalize walk t f (x-2)=c; generalize walk t g (x-2)=d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem walk_flip (t : Nat) (f : Int→Bool) (x : Int) :
    walk t (fun y => xor (f y) (f (y-2))) x = walk (t+1) f x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [walk,ih]

private theorem walk_pow (k t : Nat) (f : Int→Bool) (x : Int) :
    walk (t+2^k) f x = xor (walk t f x) (walk t f (x - 2*(2^k:Nat))) := by
  induction k generalizing t x with
  | zero => simp [walk]
  | succ k ih =>
    rw [Nat.pow_succ, show t+2^k*2=t+2^k+2^k by omega, ih, ih (t:=t), ih (t:=t)]
    have h : x-2*((2^k:Nat):Int)-2*((2^k:Nat):Int) =
        x-2*(((2^k:Nat)*2:Nat):Int) := by push_cast; omega
    rw [h]
    generalize walk t f x=a; generalize walk t f (x-2*((2^k:Nat):Int))=b
    generalize walk t f (x-2*(((2^k:Nat)*2:Nat):Int))=c
    cases a <;> cases b <;> cases c <;> rfl

private theorem walk_cone (r : Nat) (f : Int→Bool) (x : Int)
    (hz : ∀ y : Int, x-2*(r:Int) ≤ y → y ≤ x → f y=false) : walk r f x=false := by
  induction r generalizing x with
  | zero => exact hz x (by omega) (by omega)
  | succ r ih =>
    simp only [walk]
    rw [ih x (fun y hy h => hz y (by omega) h),
        ih (x-2) (fun y hy h => hz y (by omega) (by omega))]
    rfl

/-- The entire right-moving inverse of row zero is a solid black ray. -/
private theorem back_ones : OutgoingClock.step (fun _ => true) = OutgoingClock.seed := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [OutgoingClock.step,OutgoingClock.lower,OutgoingClock.seed]

/-- At time t, an actual right endpoint at depth d in the dyadic collar
1..k can only occur at depth STRICTLY below twice the next epoch's phase. -/
theorem collar_support (t k d : Nat) (hd : 0<d) (hk : d≤k)
    (he : interiorSource t ((t:Int)-d)=true) : d+1 < 2*((t+1) % 2^k) := by
  let D := 2^k
  let p := (t+1)%D
  let q := (t+1)/D
  change d+1<2*p
  have hsum : p+q*D=t+1 := by
    simpa [p,q,Nat.mul_comm,D] using Nat.mod_add_div (t+1) D
  have ident (i : Nat) : OutgoingClock.traj (fun _ => true) (t+1) i =
      cell t ((t:Int)-i) := by
    rw [show t+1=1+t by omega, ← OutgoingClock.traj_add]
    change OutgoingClock.traj (OutgoingClock.step (fun _ => true)) t i = _
    rw [back_ones, ←OutgoingClock.actual_eq]; rfl
  have folded (i : Nat) (hi : i≤k) :
      cell t ((t:Int)-i) = OutgoingClock.traj (fun _ => true) p i := by
    rw [←ident,←hsum]
    exact OutgoingClock.prefixPeriod_mul _ k q p i hi
  obtain ⟨e₀,_⟩ := Bool.and_eq_true_iff.mp he
  obtain ⟨a,h⟩ := Bool.and_eq_true_iff.mp e₀
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp a
  by_cases hp : p=0
  · rw [show (t:Int)-d+1=(t:Int)-(d-1:Nat) by omega, folded (d-1) (by omega), hp] at hb
    contradiction
  · have pm : p=(p-1)+1 := by omega
    have ret : OutgoingClock.traj (fun _ => true) p d = OutgoingClock.traj OutgoingClock.seed (p-1) d := by
      rw [pm,show p-1+1=1+(p-1) by omega, ←OutgoingClock.traj_add]
      change OutgoingClock.traj (OutgoingClock.step (fun _ => true)) _ _ = _
      rw [back_ones]; congr 2 <;> omega
    rw [folded d hk, ret] at ha
    apply Classical.byContradiction; intro high
    have vac := (OutgoingClock.peakTraj OutgoingClock.seed_peak (p-1)).2 d (by omega)
    rw [vac] at ha
    contradiction

/-- All genuine interior sources except the first k right-normalized lanes. -/
def coreSource (k t : Nat) (x : Int) : Bool :=
  interiorSource t x && decide ((k:Int)<(t:Int)-x)

/-- Full Rule 90 linear response to the moving interior core, in physical coordinates. -/
def core (k : Nat) : Nat → Int → Bool
  | 0, _ => false
  | t+1, x => xor (xor (core k t (x-1)) (core k t (x+1))) (coreSource k t x)

private def stripSource (k t : Nat) (d : Int) : Bool :=
  xor (interiorSource t ((t:Int)+1-d)) (coreSource k t ((t:Int)+1-d))

private theorem strip_support (k t : Nat) (y : Int) (active : stripSource k t y=true) :
    0<y ∧ y<2*((((t+1)%2^k):Nat):Int) := by
  unfold stripSource coreSource at active
  by_cases hy : y≤0
  · have hz : interiorSource t ((t:Int)+1-y)=false := by
      simp [interiorSource,rightVac t ((t:Int)+1-y) (by omega)]
    simp [hz] at active
  by_cases hy1 : y=1
  · subst y; simp [interiorSource] at active
  have hc : ¬(k:Int)<(t:Int)-((t:Int)+1-y) := by
    intro h; simp [h] at active
  have e : interiorSource t ((t:Int)+1-y)=true := by simpa [hc] using active
  let d := (y-1).toNat
  have hd : (d:Int)=y-1 := by dsimp [d]; omega
  rw [show (t:Int)+1-y=(t:Int)-d by omega] at e
  have lim := collar_support t k d (by omega) (by omega) e
  omega

private theorem packet_hole (k q r p : Nat) (m : Int) (f : Int→Bool)
    (hx : p+r+1=2^k) (hf : ∀ y, f y=true → 0≤y ∧ y≤2*(p:Int)) :
    walk (q*2^k+r) f (m*(2*((2^k:Nat):Int))-1)=false := by
  induction q generalizing m with
  | zero =>
    simp only [Nat.zero_mul,Nat.zero_add]
    apply walk_cone
    intro y hy hy'
    cases e : f y with
    | false => rfl
    | true =>
      obtain ⟨lo,hi⟩ := hf y e
      have pos : 0 < ((2^k:Nat):Int) := by exact_mod_cast Nat.pow_pos (a:=2) (by decide)
      by_cases hm : m≤0
      · have le := Int.mul_le_mul_of_nonneg_right hm (show 0≤2*((2^k:Nat):Int) by omega)
        simp only [Int.zero_mul] at le; omega
      · have le := Int.mul_le_mul_of_nonneg_right (show 1≤m by omega)
            (show 0≤2*((2^k:Nat):Int) by omega)
        simp only [Int.one_mul] at le; omega
  | succ q ih =>
    rw [Nat.succ_mul,show q*2^k+2^k+r=q*2^k+r+2^k by omega,walk_pow,ih]
    have off : m*(2*((2^k:Nat):Int))-1-2*((2^k:Nat):Int) =
        (m-1)*(2*((2^k:Nat):Int))-1 := by rw [Int.sub_mul,Int.one_mul];omega
    rw [off,ih];rfl

private theorem source_hole (k t u : Nat) (m : Int) (hm : (t+1+u+1)%2^k=0) :
    walk u (stripSource k t) (m*(2*((2^k:Nat):Int))-1)=false := by
  let D := 2^k
  let p := (t+1)%D
  let r := u%D
  have hD : 0<D := Nat.pow_pos (by decide)
  have hp : p<D := Nat.mod_lt _ hD
  have hr : r<D := Nat.mod_lt _ hD
  have he : (p+r+1)%D=0 := by
    have eq : (p+r)%D=(t+1+u)%D := (Nat.add_mod _ _ _).symm
    calc (p+r+1)%D = ((p+r)%D+1%D)%D := Nat.add_mod _ _ _
         _ = ((t+1+u)%D+1%D)%D := by rw [eq]
         _ = (t+1+u+1)%D := (Nat.add_mod _ _ _).symm
         _ = 0 := hm
  have total : p+r+1=D := by
    by_cases sm : p+r+1<D
    · rw [Nat.mod_eq_of_lt sm] at he; omega
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (show p+r+1-D<D by omega)] at he
      omega
  have hu : u=(u/D)*D+r := by
    simpa [r,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div u D).symm
  calc
    _ = walk ((u/D)*D+r) (stripSource k t) (m*(2*((2^k:Nat):Int))-1) :=
      congrArg (fun n => walk n (stripSource k t) _) hu
    _ = false := packet_hole k (u/D) r p m _ total (fun y yv => ⟨Int.le_of_lt (strip_support k t y yv).1, Int.le_of_lt (strip_support k t y yv).2⟩)

private theorem even_packet (k q r p : Nat) (m : Int) (f : Int→Bool)
    (hx : p+r≤2^k) (hf : ∀ y, f y=true → 0<y ∧ y<2*(p:Int)) :
    walk (q*2^k+r) f (m*(2*((2^k:Nat):Int)))=false := by
  induction q generalizing m with
  | zero =>
    simp only [Nat.zero_mul,Nat.zero_add]
    apply walk_cone
    intro y hy hy'
    cases e : f y with
    | false => rfl
    | true =>
      obtain ⟨lo,hi⟩ := hf y e
      have pos : 0 < ((2^k:Nat):Int) := by exact_mod_cast Nat.pow_pos (a:=2) (by decide)
      by_cases hm : m≤0
      · have le := Int.mul_le_mul_of_nonneg_right hm (show 0≤2*((2^k:Nat):Int) by omega)
        simp only [Int.zero_mul] at le; omega
      · have le := Int.mul_le_mul_of_nonneg_right (show 1≤m by omega)
            (show 0≤2*((2^k:Nat):Int) by omega)
        simp only [Int.one_mul] at le; omega
  | succ q ih =>
    rw [Nat.succ_mul,show q*2^k+2^k+r=q*2^k+r+2^k by omega,walk_pow,ih]
    rw [show m*(2*((2^k:Nat):Int))-2*((2^k:Nat):Int)=(m-1)*(2*((2^k:Nat):Int)) by rw [Int.sub_mul,Int.one_mul],ih];rfl

private theorem even_source_hole (k t u : Nat) (m : Int) (hm : (t+1+u)%2^k=0) :
    walk u (stripSource k t) (m*(2*((2^k:Nat):Int)))=false := by
  let D := 2^k
  let p := (t+1)%D
  let r := u%D
  have hD : 0<D := Nat.pow_pos (by decide)
  have hp : p<D := Nat.mod_lt _ hD
  have hr : r<D := Nat.mod_lt _ hD
  have he : (p+r)%D=0 := (Nat.add_mod _ _ _).symm.trans hm
  have total : p+r≤D := by
    by_cases sm : p+r<D
    · omega
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (show p+r-D<D by omega)] at he;omega
  have hu : u=(u/D)*D+r := by
    simpa [r,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div u D).symm
  calc
    _ = walk ((u/D)*D+r) (stripSource k t) (m*(2*((2^k:Nat):Int))) :=
      congrArg (fun n => walk n (stripSource k t) _) hu
    _ = false := even_packet k (u/D) r p m _ total (strip_support k t)

private def gap (k t : Nat) (d : Int) : Bool :=
  xor (interior t ((t:Int)-d)) (core k t ((t:Int)-d))

private theorem gap_step (k t : Nat) (d : Int) :
    gap k (t+1) d = xor (xor (gap k t d) (gap k t (d-2))) (stripSource k t d) := by
  unfold gap stripSource
  simp only [interior,core,Int.natCast_succ]
  rw [show (t:Int)+1-d-1=(t:Int)-d by omega,
      show (t:Int)+1-d+1=(t:Int)-(d-2) by omega]
  generalize interior t ((t:Int)-d)=a;generalize interior t ((t:Int)-(d-2))=b
  generalize core k t ((t:Int)-d)=c;generalize core k t ((t:Int)-(d-2))=e
  generalize interiorSource t ((t:Int)+1-d)=f;generalize coreSource k t ((t:Int)+1-d)=g
  cases a <;> cases b <;> cases c <;> cases e <;> cases f <;> cases g <;> rfl

private theorem gap_after (k t u : Nat) (m : Int) (hm : (t+u+1)%2^k=0) :
    walk u (gap k t) (m*(2*((2^k:Nat):Int))-1)=false := by
  induction t generalizing u with
  | zero => apply walk_cone; intro y _ _; rfl
  | succ t ih =>
    have step : gap k (t+1) = fun d =>
        xor (xor (gap k t d) (gap k t (d-2))) (stripSource k t d) := funext (gap_step k t)
    rw [step, walk_xor, walk_flip, ih (u+1) (by rwa [show t+(u+1)+1=t+1+u+1 by omega]),
      source_hole k t u m hm]; rfl

private theorem even_gap_after (k t u : Nat) (m : Int) (hm : (t+u)%2^k=0) :
    walk u (gap k t) (m*(2*((2^k:Nat):Int)))=false := by
  induction t generalizing u with
  | zero => apply walk_cone; intro y _ _; rfl
  | succ t ih =>
    have step : gap k (t+1) = fun d =>
        xor (xor (gap k t d) (gap k t (d-2))) (stripSource k t d) := funext (gap_step k t)
    rw [step, walk_xor, walk_flip, ih (u+1) (by rwa [show t+(u+1)=t+1+u by omega]),
      even_source_hole k t u m hm];rfl

theorem even_shell_cut (k b : Nat) :
    interior (b*2^(k+1)) 0 = core k (b*2^(k+1)) 0 := by
  let n := b*2^(k+1)
  have eq : n=(b*2)*2^k := by dsimp [n];rw [Nat.pow_succ];ac_rfl
  have mod0 : (n+0)%2^k=0 := by rw [Nat.add_zero,eq,Nat.mul_mod_left]
  have h := even_gap_after k n 0 (b:Int) mod0
  have idx : (b:Int)*(2*((2^k:Nat):Int))=n := by
    rw [eq];push_cast;ac_rfl
  change gap k n _=false at h
  rw [idx] at h;simpa [gap] using h

/-- Uniform moving-core deletion, for EVERY multiplier b: all right-endpoint
sources at original depths 1 through k can be discarded exactly at every
shell b·2^(k+1)−1. The width k grows with shell order. -/
theorem shell_cut (k b : Nat) (hb : 0<b) :
    interior (b*2^(k+1)-1) 0 = core k (b*2^(k+1)-1) 0 := by
  let n := b*2^(k+1)-1
  have pos : 0<b*2^(k+1) := Nat.mul_pos hb (Nat.pow_pos (by decide))
  have hplus : n+1=b*2^(k+1) := by dsimp [n];omega
  have mod0 : (n+0+1)%2^k=0 := by
    rw [Nat.add_zero,hplus,Nat.pow_succ,show b*(2^k*2)=(b*2)*2^k by ac_rfl,Nat.mul_mod_left]
  have h := gap_after k n 0 (b:Int) mod0
  have idx : (b:Int)*(2*((2^k:Nat):Int))-1=(n:Int) := by
    have eq : b*2^(k+1)=b*(2*2^k) := by rw [Nat.pow_succ,Nat.mul_comm (2^k) 2]
    have lift : ((b*2^(k+1):Nat):Int)=(b:Int)*(2*((2^k:Nat):Int)) := by
      rw [eq];push_cast;rfl
    omega
  change gap k n _=false at h
  rw [idx] at h
  simpa [gap] using h

private theorem core_vac (k t : Nat) (x : Int) (out : x < -(t:Int) ∨ (t:Int)<x) :
    core k t x=false := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have v : cell t x=false := by
      rcases out with h|h
      · exact leftVac t x (by omega)
      · exact rightVac t x (by omega)
    simp [core, coreSource,interiorSource,v,ih (x-1) (by omega),ih (x+1) (by omega)]

/-- Fresh moving-core response: only genuine events from ages s through
s+r−1 are read. Coordinate d is normalized from the true east mark. -/
def fresh (k s : Nat) : Nat → Int → Bool
  | 0, _ => false
  | r+1, d => xor (xor (fresh k s r d) (fresh k s r (d-2)))
      (coreSource k (s+r) ((s:Int)+(r:Int)+1-d))

private theorem fresh_decomp (k s r : Nat) (d : Int) :
    core k (s+r) ((s:Int)+(r:Int)-d) =
      xor (walk r (fun y => core k s ((s:Int)-y)) d) (fresh k s r d) := by
  induction r generalizing d with
  | zero => simp [walk,fresh]
  | succ r ih =>
    rw [show s+(r+1)=s+r+1 by omega]
    simp only [core,walk,fresh,Int.natCast_succ]
    rw [show (s:Int)+((r:Int)+1)-d-1=(s:Int)+(r:Int)-d by omega,
        show (s:Int)+((r:Int)+1)-d+1=(s:Int)+(r:Int)-(d-2) by omega,
        show (s:Int)+((r:Int)+1)-d=(s:Int)+(r:Int)+1-d by omega,ih,ih]
    generalize walk r (fun y => core k s ((s:Int)-y)) d=a
    generalize walk r (fun y => core k s ((s:Int)-y)) (d-2)=b
    generalize fresh k s r d=c;generalize fresh k s r (d-2)=e
    generalize coreSource k (s+r) ((s:Int)+(r:Int)+1-d)=f
    cases a <;> cases b <;> cases c <;> cases e <;> cases f <;> rfl

/-- At the top of a dyadic cone, the input row enters only at its two
extremal sites. For the true finite singleton, both lie outside the mark. -/
theorem fresh_reset (k s h : Nat) (early : s<2^h) :
    core k (s+2^h) 0 = fresh k s (2^h) ((s+2^h:Nat):Int) := by
  let d : Int := ((s+2^h:Nat):Int)
  have e := fresh_decomp k s (2^h) d
  have z : (s:Int)+((2^h:Nat):Int)-d=0 := by dsimp [d];omega
  rw [z] at e
  have f := walk_pow h 0 (fun y => core k s ((s:Int)-y)) d
  simp only [Nat.zero_add,walk] at f
  have hd : d=(s:Int)+((2^h:Nat):Int) := by dsimp [d]
  rw [core_vac k s _ (Or.inl (by omega)),core_vac k s _ (Or.inr (by omega))] at f
  rw [f] at e
  simpa [d] using e

/-- The finite triangle needed for a shell coefficient n: discard all
source ages below n−2^⌊log₂ n⌋, including their accumulated state. -/
def shellRead (k n : Nat) : Bool :=
  fresh k (n-2^n.log2) (2^n.log2) (n:Int)

theorem shellRead_eq (k n : Nat) (pos : 0<n) : core k n 0=shellRead k n := by
  have lo := Nat.log2_self_le (Nat.ne_of_gt pos)
  have hi := Nat.lt_log2_self (n:=n)
  rw [Nat.pow_succ] at hi
  have h := fresh_reset k (n-2^n.log2) n.log2 (by omega)
  rwa [show n-2^n.log2+2^n.log2=n by omega] at h

def shellAge (k b : Nat) : Nat := b*2^(k+1)-1

private theorem repeat_add {f : Nat → Bool} {T P : Nat}
    (h : ∀ t, T ≤ t → f (t+P)=f t) (t : Nat) (ht : T≤t) (m : Nat) :
    f (t + P*m) = f t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, h (t+P*m) (by omega), ih]

private theorem repeat_mod {f : Nat→Bool} {P T A B : Nat} (h : ∀ t,T≤t → f (t+P)=f t)
    (a : T≤A) (b : T≤B) (same : A%P=B%P) : f A=f B := by
  have a' := Nat.mod_add_div A P
  have b' := Nat.mod_add_div B P
  have eq : A+P*(B/P)=B+P*(A/P) := by omega
  exact (repeat_add h A a (B/P)).symm.trans ((congrArg f eq).trans (repeat_add h B b (A/P)))

/-- One actual retained nonlinear source, directly west of center. -/
def pulse (k t : Nat) : Bool := coreSource k t (-1)

private theorem pulse_mask (k t : Nat) (ht : k+3≤t) :
    MaskedRightRigidity.maskedRight t =
      xor (pulse k t) (!(center t) && center (t+1)) := by
  have raw (a b c : Bool) :
      (c && !b) = xor (a && !b) (!b && rule a b c) := by
    cases a <;> cases b <;> cases c <;> rfl
  have neq : (-1:Int)≠(t:Int) := by omega
  have inside : (k:Int)<(t:Int)-(-1) := by omega
  simpa [pulse,coreSource,interiorSource,MaskedRightRigidity.maskedRight,center,cell,neq,westSatellite,show ¬(2≤t ∧ (-1:Int)=1-(t:Int)) by omega,show (k:Int)<(t:Int)+1 by omega] using
    raw (cell t (-1)) (cell t 0) (cell t 1)

theorem pulse_nonperiodic (hc : EventuallyPeriodic center) (k : Nat) :
    ¬EventuallyPeriodic (pulse k) := by
  intro bad
  obtain ⟨U,q,hq,pu⟩ := bad
  obtain ⟨V,p,hp,cv⟩ := hc
  apply MaskedRightRigidity.claim_of_periodic_mask _ ⟨V,p,hp,cv⟩
  refine ⟨k+U+V+3,p*q,Nat.mul_pos hp hq,?_⟩
  intro t ht
  have a := repeat_add cv t (by omega) q
  have b := repeat_add cv (t+1) (by omega) q
  have c := repeat_add pu t (by omega) p
  rw [Nat.mul_comm q p] at c
  rw [pulse_mask k _ (by omega),pulse_mask k t (by omega),
    show t+p*q+1=t+1+p*q by omega,a,b,c]

/-- The retained physical source has no nonzero finite shift filter even
modulo eventually periodic sequences. This uses the genuine finite west. -/
def IrregularPulse : Prop := ∀ (k : Nat) (v : List Bool),
  ¬ EventuallyPeriodic (fun t =>
    xor (pulse k (t+v.length))
      (FiniteWindowRecurrence.dot v (FiniteWindowRecurrence.window (pulse k) v.length t)))

theorem pulse_filters (hc : EventuallyPeriodic center) : IrregularPulse := by
  intro k coeff hh
  exact pulse_nonperiodic hc k
    (FiniteWindowRecurrence.eventuallyPeriodic_of_xor_polynomial (pulse k) coeff hh)

private theorem head_by_pulse (k t : Nat) (ht : k+3≤t) :
    cell t (-1) = if center t then !(center (t+1)) else pulse k t := by
  have nw : ¬(2≤t ∧ (-1:Int)=1-(t:Int)) := by omega
  have nx : (-1:Int)≠(t:Int) := by omega
  have raw (a b c : Bool) : a=(if b then !(rule a b c) else a && !b) := by
    cases a <;> cases b <;> cases c <;> rfl
  simpa [pulse,coreSource,interiorSource,westSatellite,nw,nx,
    show (k:Int)<(t:Int)+1 by omega,center,cell] using raw (cell t (-1)) (cell t 0) (cell t 1)

private theorem inverse_law (t : Nat) (x : Int) :
    cell t (x-1)=xor (cell (t+1) x) (cell t x || cell t (x+1)) := by
  simp [cell,rule]

private theorem decodePulse (k s Q r : Nat) (early : k+3≤s)
    (wall : ∀ n, center (s+Q+n)=center (s+n))
    (agree : ∀ n, n<r → pulse k (s+Q+n)=pulse k (s+n)) :
    ∀ j n, n+j≤r → cell (s+Q+n) (-(j:Int))=cell (s+n) (-(j:Int)) := by
  have heads (n : Nat) (hn : n<r) : cell (s+Q+n) (-1)=cell (s+n) (-1) := by
    rw [head_by_pulse k _ (by omega),head_by_pulse k _ (by omega),wall n,
      show s+Q+n+1=s+Q+(n+1) by omega,show s+n+1=s+(n+1) by omega,wall (n+1),agree n hn]
  have west (j : Nat) : ∀ n, n+j≤r →
      cell (s+Q+n) (-(j:Int))=cell (s+n) (-(j:Int)) := by
    induction j using Nat.strongRecOn with
    | ind j ih =>
      cases j with
      | zero => intro n _;exact wall n
      | succ j =>
        cases j with
        | zero => intro n hn;exact heads n (by omega)
        | succ j =>
          intro n hn
          have z0 := ih (j+1) (by omega) n (by omega)
          have z1 := ih (j+1) (by omega) (n+1) (by omega)
          have z2 := ih j (by omega) n (by omega)
          rw [show -((j+1+1:Nat):Int)= -((j+1:Nat):Int)-1 by omega,inverse_law,inverse_law,
            show -((j+1:Nat):Int)+1= -(j:Int) by omega,show s+Q+n+1=s+Q+(n+1) by omega,
            show s+n+1=s+(n+1) by omega,z0,z1,z2]
  exact west

/-- Every multiplicative-scale time window must contain a true signed
difference of the seam source at the prescribed lag, not merely a difference
some arbitrarily long time later. -/
def AnnularPulse (P N : Nat) : Prop := ∀ (k s m : Nat), N≤s → k+3≤s → 0<m →
    ∃ t : Nat, s≤t ∧ t<2*s+P*m ∧ pulse k (t+P*m)≠pulse k t

theorem pulse_annuli (P N : Nat) (hp : 0<P)
    (per : ∀ t, N≤t → center (t+P)=center t) : AnnularPulse P N := by
  intro k s m hs early hm
  let Q := P*m
  have hq : 0<Q := Nat.mul_pos hp hm
  apply Classical.byContradiction
  intro no
  have agree (n : Nat) (hn : n<s+Q) :
      pulse k (s+Q+n)=pulse k (s+n) := by
    rw [show s+Q+n=(s+n)+P*m by dsimp [Q];omega]
    apply Classical.byContradiction
    intro ne;exact no ⟨s+n,by omega,by change s+n<2*s+Q;omega,ne⟩
  have wall (n : Nat) : center (s+Q+n)=center (s+n) := by
    rw [show s+Q+n=(s+n)+P*m by dsimp [Q];omega]
    exact repeat_add per (s+n) (by omega) m
  have west := decodePulse k s Q (s+Q) early wall agree
  have impossible := west (s+Q) 0 (by omega)
  simp only [Nat.add_zero] at impossible
  rw [leftMark,leftVac s _ (by omega)] at impossible;contradiction

/-- Fixed-lag mismatches enter before 2s minus every fixed additive margin,
uniformly over all sufficiently late genuine cuts. -/
private theorem earlyPulse (P N Q D : Nat) (hq : 0<Q)
    (clock : ∀ t, N≤t → center (t+Q)=center t) :
    ∃ T, ∀ s≥T, ∃ t, s≤t ∧ t+D<2*s ∧ pulse P (t+Q)≠pulse P t := by
  obtain ⟨H,T,detect⟩ := FiniteWaveAnchors.physical_lag_visible Q hq (D:Int)
  refine ⟨N+T+H.toNat+P+D+3,?_⟩
  intro s late
  obtain ⟨j,jlo,jhi,ne⟩ := detect s (by omega)
  apply Classical.byContradiction
  intro no
  have wall (n : Nat) : center (s+Q+n)=center (s+n) := by
    rw [show s+Q+n=s+n+Q by omega,clock _ (by omega)]
  have agree (n : Nat) (lt : n<s-D) : pulse P (s+Q+n)=pulse P (s+n) := by
    rw [show s+Q+n=s+n+Q by omega]
    exact Classical.byContradiction fun nx => no ⟨s+n,by omega,by omega,nx⟩
  have w := decodePulse P s Q (s-D) (by omega) wall agree ((s-j).toNat) 0 (by omega)
  simp only [Nat.add_zero] at w
  exact ne (by simpa only [show -((s-j).toNat:Int)=j-s by omega] using w)

/-- Explicit transfer from the one marked source. The oldest pulse has
kernel weight wave r (x+1); the remaining terms use later epochs. -/
def taps (k : Nat) : Nat → Nat → Int → Bool
  | _, 0, _ => false
  | s, r+1, x => xor (wave r (x+1) && pulse k s) (taps k (s+1) r x)

private theorem taps_snoc (k s r : Nat) (x : Int) :
    taps k s (r+1) x = xor (xor (taps k s r (x-1)) (taps k s r (x+1)))
      (decide (x=(-1:Int)) && pulse k (s+r)) := by
  induction r generalizing s x with
  | zero =>
    change xor (decide (x+1=0) && pulse k s) false =
      xor (xor false false) (decide (x=-1) && pulse k (s+0))
    simp [show (x+1=0) ↔ (x=-1) by omega]
  | succ r ih =>
    conv => lhs; rw [taps,ih]
    conv => rhs; rw [taps,taps]
    rw [show s+1+r=s+(r+1) by omega]
    change _ = _
    simp only [wave]
    rw [show x+1-1=x by omega, show x-1+1=x by omega]
    generalize wave r x=a;generalize wave r (x+1+1)=b
    generalize pulse k s=c;generalize taps k (s+1) r (x-1)=d
    generalize taps k (s+1) r (x+1)=e
    generalize (decide (x=-1) && pulse k (s+(r+1)))=f
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

/-- The same genuine finite cone with the one known-irregular source removed. -/
def off (k s : Nat) : Nat → Int → Bool
  | 0, _ => false
  | r+1, x => xor (xor (off k s r (x-1)) (off k s r (x+1)))
      (decide (x≠(-1:Int)) && coreSource k (s+r) x)

private theorem fresh_seam (k s r : Nat) (x : Int) :
    fresh k s r ((s:Int)+(r:Int)-x) = xor (taps k s r x) (off k s r x) := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    rw [fresh, taps_snoc, off]
    have d : (s:Int)+((r+1:Nat):Int)-x = (s:Int)+(r:Int)-(x-1) := by omega
    have e : (s:Int)+((r+1:Nat):Int)-x-2 = (s:Int)+(r:Int)-(x+1) := by omega
    have f : (s:Int)+(r:Int)+1-((s:Int)+((r+1:Nat):Int)-x) = x := by omega
    rw [e,f,d,ih,ih]
    have src : coreSource k (s+r) x =
        xor (decide (x=-1) && pulse k (s+r)) (decide (x≠-1) && coreSource k (s+r) x) := by
      by_cases hx : x=(-1:Int)
      · subst x; simp [pulse]
      · simp [hx]
    conv => lhs; rw [src]
    generalize taps k s r (x-1)=a;generalize taps k s r (x+1)=b
    generalize off k s r (x-1)=c;generalize off k s r (x+1)=d
    generalize (decide (x=-1) && pulse k (s+r))=e
    generalize (decide (x≠-1) && coreSource k (s+r) x)=f
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

def shellTap (k n : Nat) : Bool := taps k (n-2^n.log2) (2^n.log2) 0
def shellOff (k n : Nat) : Bool := off k (n-2^n.log2) (2^n.log2) 0

theorem shell_seam (k n : Nat) (pos : 0<n) :
    shellRead k n=xor (shellTap k n) (shellOff k n) := by
  have le := Nat.log2_self_le (Nat.ne_of_gt pos)
  have e := fresh_seam k (n-2^n.log2) (2^n.log2) 0
  have idx : ((n-2^n.log2:Nat):Int)+((2^n.log2:Nat):Int)-0=n := by omega
  rwa [idx] at e

/-- The false and true tags probe the adjacent odd and even ages. -/
def tagAge (k b : Nat) (even : Bool) : Nat :=
  if even then b*2^(k+1) else shellAge k b

private theorem tag_cut (k b : Nat) (hb : 0<b) (ev : Bool) :
    interior (tagAge k b ev) 0=core k (tagAge k b ev) 0 := by
  cases ev with
  | false => exact shell_cut k b hb
  | true => exact even_shell_cut k b

/-- The two genuine moving sources produce the same binary arithmetic
classification on BOTH checkerboard parities: the true east mark gives
the odd flag, the true west satellite gives the immediately following
even flag. No other run endpoint was used to compute this pair. -/
theorem two_marks (k b : Nat) (big0 : 1<b*2^k) (ev : Bool) :
    xor (fringe (tagAge k b ev) 0) (westFringe (tagAge k b ev) 0) =
    fringe (shellAge k b) 0 := by
  let M := b*2^k
  have z : b*2^(k+1)=2*M := by dsimp [M];rw [Nat.pow_succ];ac_rfl
  have big : 1<M := big0
  have hb : 0<b := by
    cases b with
    | zero => simp at big0
    | succ b => omega
  cases ev with
  | false =>
    change xor (fringe _ 0) (westFringe (b*2^(k+1)-1) 0)=_
    rw [z,show 2*M-1=2*(M-1)+1 by omega,west_odd,Bool.xor_false];rfl
  | true =>
    change xor (fringe (b*2^(k+1)) 0) (westFringe (b*2^(k+1)) 0) = _
    rw [z,fringe_even M (by omega),Bool.false_xor,show 2*M=2*((M-1)+1) by omega,
      west_even (M-1) (by omega)]
    change fringe (b*2^k-1) 0=fringe (b*2^(k+1)-1) 0
    rw [strip_ones b k hb,strip_ones b (k+1) hb]

private def freeMarks (n : Nat) (x : Int) : Bool :=
  xor (xor (wave (n+2) x) (wave (n+2) (x-1))) (wave n (x+2))

private theorem marks_step (n : Nat) (x : Int) :
    freeMarks (n+1) x=xor (freeMarks n (x-1)) (freeMarks n (x+1)) := by
  let a := wave (n+2)
  let b := wave n
  change xor (xor (xor (a (x-1)) (a (x+1))) (xor (a (x-1-1)) (a (x-1+1))))
      (xor (b (x+2-1)) (b (x+2+1))) =
    xor (xor (xor (a (x-1)) (a (x-1-1))) (b (x-1+2)))
      (xor (xor (a (x+1)) (a (x+1-1))) (b (x+1+2)))
  rw [show x-1+1=x+1-1 by omega,show x+2-1=x-1+2 by omega,show x+2+1=x+1+2 by omega]
  generalize a (x-1)=u;generalize a (x+1)=v;generalize a (x-1-1)=w;generalize a (x+1-1)=y
  generalize b (x-1+2)=g;generalize b (x+1+2)=h
  cases u <;> cases v <;> cases w <;> cases y <;> cases g <;> cases h <;> rfl

private theorem wave_vac (n : Nat) (x : Int) (h : x < -(n:Int) ∨ (n:Int)<x) :
    wave n x=false := by
  induction n generalizing x with
  | zero => simp [wave];omega
  | succ n ih => rw [wave,ih (x-1) (by omega),ih (x+1) (by omega)];rfl

private theorem marks_vac (n : Nat) (x : Int) (h : x < -(n:Int)-4 ∨ (n:Int)+4<x) :
    freeMarks n x=false := by
  rw [freeMarks,wave_vac _ _ (by omega),wave_vac _ _ (by omega),wave_vac _ _ (by omega)];rfl

private theorem tap_vac (n : Nat) (x : Int) (h : x < -(n:Int)-1 ∨ (n:Int)+1<x) :
    taps 0 0 n x=false := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [taps_snoc,ih _ (by omega),ih _ (by omega)];simp [show x≠-1 by omega]

private theorem tap_source (s n : Nat) :
    taps 0 s (n+1) (-1)=pulse 0 (s+n) := by
  induction n generalizing s with
  | zero => simp [taps,wave]
  | succ n ih =>
    change xor (wave (n+1) 0 && _) _=_
    rw [wave_center,ih];simp [show s+1+n=s+(n+1) by omega]

private def packet (n : Nat) (x : Int) : Bool := xor (freeMarks n x) (taps 0 0 (n+2) x)

private theorem packet_step (n : Nat) (x : Int) (nx : x≠ -1) :
    packet (n+1) x=xor (packet n (x-1)) (packet n (x+1)) := by
  unfold packet
  rw [marks_step,show n+1+2=n+2+1 by omega,taps_snoc]
  simp [nx,Bool.xor_comm,Bool.xor_left_comm,Bool.xor_assoc]

/-- Full response of every genuine unmarked lane except x=-1. -/
def bulk (n : Nat) : Bool := off 0 0 (n+2) 0

private theorem packet_center (n : Nat) : packet n 0=xor (center (n+2)) (bulk n) := by
  have eqc : ∀ t x, interior t x=core 0 t x := by
    intro t
    induction t with
    | zero => intro _;rfl
    | succ t ih =>
      intro x
      rw [interior,core,ih,ih]
      by_cases h : x<(t:Int)
      · simp [coreSource,h]
      · by_cases z : x=(t:Int)
        · simp [coreSource,interiorSource,z]
        · simp [coreSource,interiorSource,rightVac t x (by omega)]
  have fr := fresh_decomp 0 0 (n+2) (n+2)
  have none : walk (n+2) (fun _ => false) (n+2)=false := walk_cone _ _ _ (by intros;rfl)
  change _ = xor (walk _ (fun _ => false) _) _ at fr
  have se := fresh_seam 0 0 (n+2) 0
  simp only [Int.natCast_add,Int.cast_ofNat_Int,Int.zero_add,Int.sub_zero] at se fr
  simp only [Nat.zero_add,Int.sub_self,none,Bool.false_xor] at fr
  have m : xor (fringe (n+2) 0) (westFringe (n+2) 0)=freeMarks n 0 := by
    simp [fringe,westFringe,freeMarks,show ¬n+2<2 by omega,show (0:Int)≠(n:Int)+2+1 by omega,
      show (0:Int)≠ -((n:Int)+2) by omega]
  unfold packet center bulk
  rw [row_split,m,eqc,fr,se]
  simp only [Bool.xor_assoc,Bool.xor_self,Bool.xor_false]

/-- Frobenius clears a fixed central reading band of a finite free packet
through almost the entire next factor-of-two interval. -/
private theorem packet_hush (Z : Nat→Int→Bool) (L k r : Nat) (x : Int)
    (law : ∀ n y, Z (n+1) y=xor (Z n (y-1)) (Z n (y+1)))
    (vac : ∀ y, y < -(L:Int) ∨ (L:Int)<y → Z 0 y=false)
    (near : -1≤x ∧ x≤1) (room : r+L+1<2^k) : Z (2^k+r) x=false := by
  have track (n : Nat) (y : Int) : Z n y=walk n (Z 0) (y+n) := by
    induction n generalizing y with
    | zero => simp [walk]
    | succ n ih =>
      rw [law,ih,ih,walk,show y-1+(n:Int)=y+(↑(n+1):Int)-2 by omega,
        show y+1+(n:Int)=y+(↑(n+1):Int) by omega,Bool.xor_comm]
  rw [track,Nat.add_comm (2^k) r,walk_pow]
  have h1 : walk r (Z 0) (x+↑(r+2^k))=false := by
    apply walk_cone;intro y lo hi;exact vac y (Or.inr (by omega))
  have h2 : walk r (Z 0) (x+↑(r+2^k)-2*((2^k:Nat):Int))=false := by
    apply walk_cone;intro y lo hi;exact vac y (Or.inl (by omega))
  rw [h1,h2];rfl

private theorem reflect_law (Z : Nat→Int→Bool)
    (wall : ∀ n, Z n 0=false)
    (law : ∀ n y, 0<y → Z (n+1) y=xor (Z n (y-1)) (Z n (y+1))) :
    ∀ n x, Z (n+1) (if x<0 then -x else x) =
      xor (Z n (if x-1<0 then -(x-1) else x-1)) (Z n (if x+1<0 then -(x+1) else x+1)) := by
  intro n x
  by_cases h : x<0
  · simp only [if_pos h,if_pos (show x-1<0 by omega)]
    rw [law _ _ (by omega),show -(x-1)= -x+1 by omega]
    by_cases h' : x+1<0
    · rw [if_pos h',show -(x+1)= -x-1 by omega,Bool.xor_comm]
    · have e : x= -1 := by omega
      subst x;simp [Bool.xor_comm]
  · by_cases z : x=0
    · subst x;simp [wall]
    · simp only [if_neg h,if_neg (show ¬x-1<0 by omega),if_neg (show ¬x+1<0 by omega)]
      exact law n x (by omega)

private theorem xorLag {a b c d : Bool} : xor (xor a b) (xor c d)=xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The complementary nonlinear bulk itself has to be aperiodic. A putative
periodic bulk gives a zero-boundary free difference to the east of the
physical marked source. Its reflected packet is exactly vacant on a dyadic
annulus, contradicting the true moving-west detector. -/
theorem bulk_nonperiodic (hc : EventuallyPeriodic center) : ¬EventuallyPeriodic bulk := by
  intro hb
  obtain ⟨T,P,hp,cper⟩ := hc
  obtain ⟨U,p,pp,bper⟩ := hb
  let Q:=P*p
  let S:=T+U+3
  let L:=S+Q+10
  let D:=L+S+8
  have qp : 0<Q:=Nat.mul_pos hp pp
  have clock (t : Nat) (late : T≤t) : center (t+Q)=center t := repeat_add cper t late p
  have bk (t : Nat) (late : U≤t) : bulk (t+Q)=bulk t := by
    rw [show Q=p*P by dsimp [Q];ac_rfl];exact repeat_add bper t late P
  let Z (n : Nat) (x : Int) := xor (packet (S+n+Q) x) (packet (S+n) x)
  let W (n : Nat) (x : Int) := xor (freeMarks (S+n+Q) x) (freeMarks (S+n) x)
  have wall (n : Nat) : Z n 0=false := by
    dsimp [Z];rw [packet_center,packet_center,show S+n+Q+2=S+n+2+Q by omega,
      clock _ (by dsimp [S];omega),bk _ (by dsimp [S];omega),Bool.xor_self]
  have interiorEq (n : Nat) (x : Int) (nx : x≠ -1) :
      Z (n+1) x=xor (Z n (x-1)) (Z n (x+1)) := by
    dsimp [Z];rw [show S+(n+1)+Q=(S+n+Q)+1 by omega,show S+(n+1)=(S+n)+1 by omega,
      packet_step _ _ nx,packet_step _ _ nx,xorLag]
  have wlaw (n : Nat) (x : Int) : W (n+1) x=xor (W n (x-1)) (W n (x+1)) := by
    dsimp [W];rw [show S+(n+1)+Q=(S+n+Q)+1 by omega,show S+(n+1)=(S+n)+1 by omega,
      marks_step,marks_step,xorLag]
  have wvac (y : Int) (v : y< -(L:Int) ∨ (L:Int)<y) : W 0 y=false := by
    dsimp [W,L] at *;rw [marks_vac _ _ (by omega),marks_vac _ _ (by omega)];rfl
  have zvac (y : Int) (v : y< -(L:Int) ∨ (L:Int)<y) :
      Z 0 (if y<0 then -y else y)=false := by
    let j := if y<0 then -y else y
    have h : (L:Int)<j := by dsimp [j];split <;> omega
    change Z 0 j=false
    dsimp [Z,packet,L] at *
    rw [marks_vac _ _ (by omega),marks_vac _ _ (by omega),tap_vac _ _ (by omega),tap_vac _ _ (by omega)];rfl
  obtain ⟨V,find⟩ := earlyPulse 0 T Q D qp clock
  let k:=V+1
  have big : V<2^k := by dsimp [k];have h:=Nat.lt_two_pow_self (n:=V+1);omega
  let s:=S+2^k+1
  obtain ⟨t,a,b,ne⟩ := find s (by dsimp [s];omega)
  let r:=t-s
  let n:=2^k+r
  have time : S+n+1=t := by dsimp [n,r,s] at *;omega
  have room : r+L+1<2^k := by dsimp [D,r,s] at *;omega
  have w1 := packet_hush W L k r (-1) wlaw wvac (by decide) room
  have z1 := packet_hush (fun n x => Z n (if x<0 then -x else x)) L k r 1
    (reflect_law Z wall (fun n x hx => interiorEq n x (by omega))) zvac (by decide) room
  change W n (-1)=false at w1
  change Z n 1=false at z1
  have z0 := interiorEq n 0 (by decide)
  change Z (n+1) 0=xor (Z n (-1)) (Z n 1) at z0
  rw [wall,z1,Bool.xor_false] at z0
  have z := z0.symm
  unfold Z packet at z
  rw [tap_source,tap_source,xorLag] at z
  change xor (W n (-1)) (xor (pulse 0 (0+(S+n+Q+1))) (pulse 0 (0+(S+n+1))))=false at z
  rw [w1,Bool.false_xor,Nat.zero_add,Nat.zero_add,show S+n+Q+1=t+Q by omega,time] at z
  exact ne (by cases a : pulse 0 (t+Q) <;> cases b : pulse 0 t <;> simp_all)

private def mix : List Bool → (Int→Bool) → Int → Bool
  | [], _, _ => false
  | b::v,f,x => xor (b && f x) (mix v f (x+1))

private theorem mix_congr (v : List Bool) (f g : Int→Bool) (x : Int)
    (same : ∀ i, x≤i → i<x+(v.length:Int) → f i=g i) : mix v f x=mix v g x := by
  induction v generalizing x with
  | nil => rfl
  | cons b v ih =>
    simp only [List.length_cons,Int.natCast_succ] at same
    rw [mix,mix,same x (by omega) (by omega),ih (x+1) (by intro i a b;exact same i (by omega) (by omega))]

private theorem mix_shift (v : List Bool) (f : Int→Bool) (x d : Int) :
    mix v (fun y => f (y+d)) x=mix v f (x+d) := by
  induction v generalizing x with
  | nil => rfl
  | cons b v ih => rw [mix,mix,ih,show x+1+d=x+d+1 by omega]

private theorem mix_add (v : List Bool) (f g : Int→Bool) (x : Int) :
    mix v (fun y => xor (f y) (g y)) x=xor (mix v f x) (mix v g x) := by
  induction v generalizing x with
  | nil => rfl
  | cons b v ih =>
    rw [mix,mix,mix,ih]
    cases b with
    | false => simp
    | true => simpa only [Bool.true_and] using (xorLag (a:=f x) (b:=g x) (c:=mix v f (x+1)) (d:=mix v g (x+1)))

/-- End coefficients are both 1; the listed bits are all interior
coefficients, in physical spatial order. -/
private def stencil (v : List Bool) (f : Int→Bool) (x : Int) : Bool :=
  xor (xor (f (x-1)) (mix v f x)) (f (x+v.length))

private theorem stencil_add (v : List Bool) (f g : Int→Bool) (x : Int) :
    stencil v (fun y => xor (f y) (g y)) x=xor (stencil v f x) (stencil v g x) := by
  unfold stencil;rw [mix_add,xorLag (a:=f (x-1)),xorLag]

private theorem stencil_step (v : List Bool) (Z : Nat→Int→Bool) (n : Nat) (x : Int)
    (law : ∀ i, x-1≤i → Z (n+1) i=xor (Z n (i-1)) (Z n (i+1))) :
    stencil v (Z (n+1)) x=xor (stencil v (Z n) (x-1)) (stencil v (Z n) (x+1)) := by
  let f:=Z n
  have wel : mix v (Z (n+1)) x=mix v (fun i => xor (f (i+(-1))) (f (i+1))) x :=
    mix_congr v _ _ x (by intro i lo _;exact law _ (by omega))
  unfold stencil
  rw [wel,mix_add,mix_shift,mix_shift,law (x-1) (by omega),law (x+v.length) (by omega)]
  change _ = xor (xor (xor (f (x-1-1)) (mix v f (x-1))) (f (x-1+v.length)))
    (xor (xor (f (x+1-1)) (mix v f (x+1))) (f (x+1+v.length)))
  rw [show x+-1=x-1 by omega,show x-1+1=x+1-1 by omega,
    show x+(v.length:Int)-1=x-1+v.length by omega,show x+(v.length:Int)+1=x+1+v.length by omega]
  dsimp only [f]
  generalize Z n (x-1-1)=a;generalize Z n (x+1-1)=b
  generalize mix v (Z n) (x-1)=c;generalize mix v (Z n) (x+1)=d
  generalize Z n (x-1+v.length)=g;generalize Z n (x+1+v.length)=h
  cases a <;> cases b <;> cases c <;> cases d <;> cases g <;> cases h <;> rfl

private theorem leftSolve {a b c : Bool} (eq : xor (xor a b) c=false) : a=xor b c := by
  cases a <;> cases b <;> cases c <;> simp_all
private theorem rightSolve {a b c : Bool} (eq : xor (xor a b) c=false) : c=xor a b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- A finite homogeneous spatial filter at both bounding positions makes
the enclosed Rule90 strip autonomous, without requiring a spatially
periodic state or any prescribed exterior history. -/
private theorem collar_echo (v : List Bool) (Z : Nat→Int→Bool) (U : Nat)
    (law : ∀ n x, 0≤x → Z (n+1) x=xor (Z n (x-1)) (Z n (x+1)))
    (cut : ∀ n, n<U → stencil v (Z n) 0=false ∧ stencil v (Z n) 1=false) :
    ∃ h, 0<h ∧ h≤2^(v.length+1) ∧ ∀ n, 2^(v.length+1)≤n → n+h<U →
      Z (n+h) (-1)=Z n (-1) := by
  let d:=v.length
  let B:=2^(d+1)
  let rows (a : Nat):=FiniteWindowRecurrence.window (fun j : Nat => Z a j) (d+1) 0
  obtain ⟨i,j,lt,cap,e⟩ := QuantifiedSplit.repeat_le B
    (fun a => FiniteWindowRecurrence.encode (rows a)) (fun t _ => by
      simpa [rows,B,FiniteWindowRecurrence.window_len] using FiniteWindowRecurrence.encode_bound (rows t))
  let same (a b : Nat) := ∀ y : Int, 0≤y → y≤d → Z a y=Z b y
  have eq0 : same i j := by
    have eq := FiniteWindowRecurrence.same_encode_eq (xs:=rows i) (ys:=rows j)
      (by simp [rows,FiniteWindowRecurrence.window_len]) e
    intro y lo hi
    have yh : y.toNat<d+1 := by omega
    have ai : (rows i)[y.toNat]'(by simp [rows,FiniteWindowRecurrence.window_len,yh])=Z i y := by
      rw [FiniteWindowRecurrence.window_at (fun j : Nat => Z i j) (d+1) 0 _ yh];simp [Int.toNat_of_nonneg lo]
    have aj : (rows j)[y.toNat]'(by simp [rows,FiniteWindowRecurrence.window_len,yh])=Z j y := by
      rw [FiniteWindowRecurrence.window_at (fun k : Nat => Z j k) (d+1) 0 _ yh];simp [Int.toNat_of_nonneg lo]
    simpa only [eq,aj] using ai.symm
  have border (a b : Nat) (au : a<U) (bu : b<U) (s : same a b) :
      Z a (-1)=Z b (-1) ∧ Z a ((d:Int)+1)=Z b ((d:Int)+1) := by
    obtain ⟨al,ar⟩:=cut a au
    obtain ⟨bl,br⟩:=cut b bu
    have l1:=leftSolve al;have l2:=leftSolve bl
    change Z a (-1)=xor (mix v (Z a) 0) (Z a (0+d)) at l1
    change Z b (-1)=xor (mix v (Z b) 0) (Z b (0+d)) at l2
    have r1:=rightSolve ar;have r2:=rightSolve br
    change Z a (1+d)=xor (Z a 0) (mix v (Z a) 1) at r1
    change Z b (1+d)=xor (Z b 0) (mix v (Z b) 1) at r2
    constructor
    · rw [l1,l2,mix_congr v (Z a) (Z b) 0 (by intro y ly hy;exact s y ly (by dsimp [d];omega)),
        s (0+d) (by omega) (by omega)]
    · rw [show (d:Int)+1=1+d by omega,r1,r2,s 0 (by omega) (by omega),
        mix_congr v (Z a) (Z b) 1 (by intro y ly hy;exact s y (by omega) (by dsimp [d];omega))]
  have advance (k : Nat) (lim : j+k≤U) : same (i+k) (j+k) := by
    induction k with
    | zero => simpa using eq0
    | succ k ih =>
      have prev:=ih (by omega)
      have ⟨left,right⟩:=border _ _ (by omega) (by omega) prev
      have ext (y : Int) (lo : -1≤y) (hi : y≤(d:Int)+1) : Z (i+k) y=Z (j+k) y := by
        by_cases le : y= -1
        · simpa [le] using left
        by_cases ri : y=(d:Int)+1
        · simpa [ri] using right
        exact prev y (by omega) (by omega)
      intro y lo hi
      rw [show i+(k+1)=i+k+1 by omega,show j+(k+1)=j+k+1 by omega,law _ _ lo,law _ _ lo,
        ext (y-1) (by omega) (by omega),ext (y+1) (by omega) (by omega)]
  refine ⟨j-i,by omega,by change j-i≤B;omega,?_⟩
  intro n early lim
  change B≤n at early
  let k:=n-i
  have a : i+k=n:=by dsimp [k];omega
  have b : j+k=n+(j-i):=by dsimp [k];omega
  have pair:=border (i+k) (j+k) (by omega) (by omega) (advance k (by omega))
  simpa [a,b] using pair.1.symm

private theorem rectLag (g : Nat→Bool) (t Q h : Nat)
    (echoLag : ∀ i, i≤2*(Q*h) →
      xor (g (t+i+h+Q)) (g (t+i+h))=xor (g (t+i+Q)) (g (t+i))) :
    g (t+2*(Q*h))=g t := by
  let M:=Q*h
  let d (i : Nat):=xor (g (t+i+Q)) (g (t+i))
  have times (i k : Nat) (room : i+h*k≤2*M) : d (i+h*k)=d i := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      change xor (g (t+(i+h*k+h)+Q)) (g (t+(i+h*k+h)))=_
      rw [show t+(i+h*k+h)=t+(i+h*k)+h by omega,echoLag _ (by rw [Nat.mul_succ] at room;omega)]
      exact ih (by rw [Nat.mul_succ] at room;omega)
  have same (i : Nat) (bound : i≤M) : d (i+M)=d i := by
    have m : h*Q=M:=Nat.mul_comm ..;simpa [m] using times i Q (by rw [m];omega)
  let p (i : Nat):=xor (g (t+i+M)) (g (t+i))
  have advance (i : Nat) (bound : i≤M) : p (i+Q)=p i := by
    have a := same i bound
    dsimp [p,d] at *
    rw [show t+(i+M)+Q=t+i+Q+M by omega,show t+(i+M)=t+i+M by omega] at a
    rw [show t+(i+Q)=t+i+Q by omega]
    generalize g (t+i+Q+M)=A at a ⊢
    generalize g (t+i+M)=B at a ⊢
    generalize g (t+i+Q)=C at a ⊢
    generalize g (t+i)=D at a ⊢
    cases A <;> cases B <;> cases C <;> cases D <;> simp_all
  have walkP (k : Nat) (cap : k≤h) : p (Q*k)=p 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ,advance _ (Nat.mul_le_mul_left _ (by omega)),ih (by omega)]
  have a:=walkP h (by omega)
  change p M=p 0 at a
  dsimp [p] at a
  rw [show t+M+M=t+2*M by omega] at a
  change g (t+2*M)=g t
  generalize g (t+2*M)=A at a ⊢;generalize g (t+M)=B at a ⊢;generalize g t=C at a ⊢
  cases A <;> cases B <;> cases C <;> simp_all

private theorem bounded_late (R : Nat→Nat→Prop) (h : ∀ j, 0<j → ∃ V, ∀ s≥V, R j s) (B : Nat) :
    ∃ V, ∀ j, 0<j → j≤B → ∀ s≥V, R j s := by
  induction B with
  | zero => exact ⟨0,by intros;omega⟩
  | succ b ih =>
    obtain ⟨V,low⟩:=ih
    obtain ⟨T,top⟩:=h (b+1) (by omega)
    refine ⟨V+T,?_⟩
    intro j pos cap s late
    by_cases z : j=b+1
    · exact z ▸ top s (by omega)
    · exact low j pos (by omega) s (by omega)

/-- The signed physical stencil of the genuinely marked source against
arbitrary east positions. At the distinguished time n, x=−1 is the old
nonlinear pulse plus the explicitly known marks; correcting removes
that free field. For the empty stencil, this is the direct pulse/bulk
cancellation test. -/
def markedLink (v : List Bool) (corr : Bool) (n : Nat) : Bool :=
  xor (stencil v (packet n) 0) (corr && freeMarks n (-1))

theorem no_marked_link (hc : EventuallyPeriodic center) (v : List Bool) (corr : Bool) :
    ¬EventuallyPeriodic (markedLink v corr) := by
  intro hb
  obtain ⟨T,P,hp,cper⟩:=hc
  obtain ⟨U,p,pp,per⟩:=hb
  let Q:=P*p
  let S:=T+U+3
  let L:=S+Q+10
  let B:=2^(v.length+1)
  let D:=L+S+3*B+2*(Q*B)+40
  have qp : 0<Q:=Nat.mul_pos hp pp
  let Z (n : Nat) (x : Int):=xor (packet (S+n+Q) x) (packet (S+n) x)
  let W (n : Nat) (x : Int):=xor (freeMarks (S+n+Q) x) (freeMarks (S+n) x)
  let Y (n : Nat) (x : Int):=xor (stencil v (Z n) x) (corr && W n (x-1))
  have wall (n : Nat) : Y n 0=false := by
    have h:=repeat_add per (S+n) (by dsimp [S];omega) P
    rw [show p*P=Q by dsimp [Q];ac_rfl] at h
    dsimp [markedLink,Y,Z,W] at *
    rw [stencil_add]
    generalize stencil v (packet (S+n+Q)) 0=a at *
    generalize stencil v (packet (S+n)) 0=b at *
    change (a ^^ (corr && freeMarks (S+n+Q) (-1)))=(b ^^ (corr && freeMarks (S+n) (-1))) at h
    change ((a ^^ b) ^^ (corr && (freeMarks (S+n+Q) (-1) ^^ freeMarks (S+n) (-1))))=false
    generalize freeMarks (S+n+Q) (-1)=c at *
    generalize freeMarks (S+n) (-1)=d at *
    cases corr <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all
  have zlaw (n : Nat) (x : Int) (pos : 0≤x) :
      Z (n+1) x=xor (Z n (x-1)) (Z n (x+1)) := by
    dsimp [Z];rw [show S+(n+1)+Q=(S+n+Q)+1 by omega,show S+(n+1)=(S+n)+1 by omega,
      packet_step _ _ (by omega),packet_step _ _ (by omega),xorLag]
  have wlaw (n : Nat) (x : Int) : W (n+1) x=xor (W n (x-1)) (W n (x+1)) := by
    dsimp [W];rw [show S+(n+1)+Q=(S+n+Q)+1 by omega,show S+(n+1)=(S+n)+1 by omega,
      marks_step,marks_step,xorLag]
  have ylaw (n : Nat) (x : Int) (pos : 0<x) :
      Y (n+1) x=xor (Y n (x-1)) (Y n (x+1)) := by
    dsimp only [Y];rw [stencil_step _ _ _ _ (fun i lo => zlaw n i (by omega)),wlaw,
      show x-1+1=x+1-1 by omega]
    cases corr with
    | false => simp
    | true => simpa only [Bool.true_and] using xorLag
  have wvac (y : Int) (out : y< -(L:Int) ∨ (L:Int)<y) : W 0 y=false := by
    dsimp [W,L] at *;rw [marks_vac _ _ (by omega),marks_vac _ _ (by omega)];rfl
  have yvac (y : Int) (out : y< -(L:Int) ∨ (L:Int)<y) : Y 0 (if y<0 then -y else y)=false := by
    let j:=if y<0 then -y else y
    have far : (L:Int)<j:=by dsimp [j];split <;> omega
    have zw (x : Int) (hx : j-1≤x) : Z 0 x=false := by
      dsimp [Z,packet,L] at *;rw [marks_vac _ _ (by omega),marks_vac _ _ (by omega),
        tap_vac _ _ (by omega),tap_vac _ _ (by omega)];rfl
    have wh : W 0 (j-1)=false := by
      dsimp [W,L] at *;rw [marks_vac _ _ (by omega),marks_vac _ _ (by omega)];rfl
    have zero (v : List Bool) (x : Int) : mix v (fun _ => false) x=false := by
      induction v generalizing x with
      | nil => rfl
      | cons b v ih => simp [mix,ih]
    change xor (stencil v (Z 0) j) (corr && W 0 (j-1))=false
    rw [stencil, mix_congr v (Z 0) (fun _ => false) j (by intro i lo _;exact zw i (by omega)),
      zero, zw _ (by omega),zw _ (by omega),wh];simp
  have early (h : Nat) (ph : 0<h) :
      ∃ V, ∀ s≥V, ∃ t, s≤t ∧ t+D<2*s ∧ pulse 0 (t+2*(Q*h))≠pulse 0 t := by
    apply earlyPulse 0 T _ D (by exact Nat.mul_pos (by decide) (Nat.mul_pos qp ph))
    intro t late
    rw [show 2*(Q*h)=P*(p*h*2) by dsimp [Q];ac_rfl]
    exact repeat_add cper t late _
  obtain ⟨V,force⟩:=bounded_late _ early B
  let k:=V+D+B+2
  let H:=2^k
  let M:=H-L-3
  have hp2 : k<H:=Nat.lt_two_pow_self
  have enough : V+D+B<H:=by dsimp [k] at hp2;omega
  let c (n : Nat) (x : Int):=Z (H+n) x
  have cuts (n : Nat) (cap : n<M) : stencil v (c n) 0=false ∧ stencil v (c n) 1=false := by
    have room : n+L+1<H:=by dsimp [M] at cap;omega
    have w0:=packet_hush W L k n (-1) wlaw wvac (by decide) room
    have w1:=packet_hush W L k n 0 wlaw wvac (by decide) room
    have y0:=wall (H+n)
    have y1:=packet_hush (fun u x => Y u (if x<0 then -x else x)) L k n 1
      (reflect_law Y wall ylaw) yvac (by decide) room
    change Y (H+n) 1=false at y1
    change W (H+n) (-1)=false at w0
    change W (H+n) 0=false at w1
    change xor (stencil v (c n) 0) (corr && W (H+n) (-1))=false at y0
    change xor (stencil v (c n) 1) (corr && W (H+n) 0)=false at y1
    exact ⟨by simpa [w0] using y0,by simpa [w1] using y1⟩
  obtain ⟨h,ph,hb,eq⟩:=collar_echo v c M
    (fun n x nx => by change Z (H+n+1) x=_;exact zlaw _ _ nx) cuts
  change h≤B at hb
  let s:=S+H+B+1
  obtain ⟨t,st,cap,ne⟩:=force h ph hb s (by dsimp [s];omega)
  apply ne
  apply rectLag
  intro i yi
  let r:=t+i-(S+H+1)
  have hb' : Q*h≤Q*B:=Nat.mul_le_mul_left _ hb
  have rb : B≤r:=by dsimp [r,s] at *;omega
  have rr : r+h<M:=by dsimp [M,r,D,s] at *;omega
  have e:=eq r rb rr
  have hw (u : Nat) (uu : u<M) : W (H+u) (-1)=false :=
    packet_hush W L k u (-1) wlaw wvac (by decide) (by dsimp [M] at uu;omega)
  have pulseAt (u : Nat) (uu : u<M) : c u (-1) =
      xor (pulse 0 (S+(H+u)+Q+1)) (pulse 0 (S+(H+u)+1)) := by
    dsimp only [c,Z,packet];rw [tap_source,tap_source,xorLag]
    change xor (W (H+u) (-1)) _=_
    rw [hw u uu];simp
  rw [pulseAt _ rr,pulseAt _ (by omega)] at e
  rwa [show S+(H+(r+h))+Q+1=t+i+h+Q by dsimp [r];omega,
    show S+(H+(r+h))+1=t+i+h by dsimp [r];omega,
    show S+(H+r)+Q+1=t+i+Q by dsimp [r];omega,
    show S+(H+r)+1=t+i by dsimp [r];omega] at e

/-- Empty spatial stencil recovers the actual signed complementary bulk
at the physical source timing. In particular the two irregular signals
cannot cancel even up to an arbitrary eventually periodic error. -/
theorem no_direct_cancellation (hc : EventuallyPeriodic center) :
    ¬EventuallyPeriodic (fun n => xor (bulk n) (pulse 0 (n+1))) := by
  intro alleged
  have no := no_marked_link hc [] true
  obtain ⟨A,P,pos,per⟩:=hc
  obtain ⟨B,Q,qpos,other⟩:=alleged
  have link (n : Nat) : markedLink [] true n =
      xor (center (n+2)) (xor (bulk n) (pulse 0 (n+1))) := by
    change xor (xor (xor (packet n (-1)) false) (packet n 0)) (freeMarks n (-1))=_
    rw [packet_center]
    unfold packet
    rw [tap_source,Nat.zero_add]
    generalize freeMarks n (-1)=a;generalize pulse 0 (n+1)=b
    generalize center (n+2)=c;generalize bulk n=d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl
  apply no
  refine ⟨A+B,P*Q,Nat.mul_pos pos qpos,?_⟩
  intro t late
  have c:=repeat_add per (t+2) (by omega) Q
  have o:=repeat_add (f:=fun n => xor (bulk n) (pulse 0 (n+1))) (T:=B) (P:=Q) other t (by omega) P
  rw [Nat.mul_comm Q P] at o
  rw [link,link,show t+P*Q+2=t+2+P*Q by omega,c]
  exact congrArg _ o

/-- The hard collision: the difference of the other genuine lanes agrees
with the finite transfer from the known-irregular lane at one mixed pair.
The targets may choose their checkerboard tags separately. k=0 is legal:
all sufficiently late noncritical ages are then available; higher k retains
the exact growing-collar deletion when it helps. There is no independence
assumption between pulses or cones. -/
theorem L1 (P N : Nat) (hP : 0<P) (marked : IrregularPulse) (annuli : AnnularPulse P N)
    (bulkVaries : ¬EventuallyPeriodic bulk)
    (nonlocal : ∀ v corr, ¬EventuallyPeriodic (markedLink v corr)) :
    ∃ (k a v d : Nat) (evA evB : Bool), 0<d ∧
      let A := tagAge k (2^a) evA
      let B := tagAge k ((2*d+1)*2^v) evB
      N+4≤A ∧ N+4≤B ∧ A%P=B%P ∧ xor (shellOff k A) (shellOff k B) = xor (shellTap k A) (shellTap k B) := by
  sorry

theorem close_step4 (hcenter : EventuallyPeriodic center) : False := by
  obtain ⟨T,P,hP,period⟩ := hcenter
  obtain ⟨k,a,v,d,evA,evB,hd,earlyA,earlyB,hs,he⟩ := L1 P T hP (pulse_filters ⟨T,P,hP,period⟩) (pulse_annuli P T hP period) (bulk_nonperiodic ⟨T,P,hP,period⟩) (no_marked_link ⟨T,P,hP,period⟩)
  let A := tagAge k (2^a) evA
  let B := tagAge k ((2*d+1)*2^v) evB
  change A%P=B%P at hs
  change xor (shellOff k A) (shellOff k B) = xor (shellTap k A) (shellTap k B) at he
  change T+4≤A at earlyA;change T+4≤B at earlyB
  have va : 0<2^a := Nat.pow_pos (by decide)
  have vb : 0<(2*d+1)*2^v := Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
  have big (b : Nat) (ev : Bool) (late : T+4≤tagAge k b ev) : 1<b*2^k := by
    have cap : tagAge k b ev≤b*2^(k+1) := by cases ev <;> simp [tagAge,shellAge]
    rw [Nat.pow_succ,←Nat.mul_assoc] at cap;omega
  have fa : xor (fringe A 0) (westFringe A 0)=true := by
    rw [two_marks k (2^a) (big _ _ earlyA) evA]
    change fringe (2^a*2^(k+1)-1) 0=true
    rw [←Nat.pow_add]
    exact (L2 (a+(k+1)) 1 (by decide)).1
  have fb : xor (fringe B 0) (westFringe B 0)=false := by
    rw [two_marks k ((2*d+1)*2^v) (big _ _ earlyB) evB]
    change fringe ((2*d+1)*2^v*2^(k+1)-1) 0=false
    rw [Nat.mul_assoc,←Nat.pow_add]
    exact (L2 (v+(k+1)) d hd).2
  have ca : interior A 0=core k A 0 := tag_cut k _ va evA
  have cb : interior B 0=core k B 0 := tag_cut k _ vb evB
  have same : shellRead k A = shellRead k B := by
    rw [shell_seam k A (by omega),shell_seam k B (by omega)]
    generalize shellOff k A=u at *;generalize shellOff k B=w at *
    generalize shellTap k A=z at *;generalize shellTap k B=y at *
    cases u <;> cases w <;> cases z <;> cases y <;> first | rfl | contradiction
  have hpair : center A=center B := repeat_mod period (by omega) (by omega) hs
  unfold center at hpair
  rw [row_split A 0,row_split B 0,fa,fb,ca,cb,shellRead_eq k A (by omega),
      shellRead_eq k B (by omega),←same] at hpair
  cases hh : shellRead k A <;> simp [hh] at hpair

end OpenProblem.BoundsBlueprint
