import Statement
import QuantifiedSplit

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

/-- Glue the two constructions, not two snapshots: this is a full spacetime
for any candidate sequence, including a candidate that fails the singleton test. -/
def world (c : Trace) (t : Nat) : Int → Bool
  | .ofNat j => east c t j
  | .negSucc j => (pair c (j+1)).1 t

theorem east_wall (c : Trace) (t : Nat) : east c t 0 = c t := by cases t <;> rfl

theorem world_nonpos (c : Trace) (t j : Nat) :
    world c t (-(j:Int)) = (pair c j).1 t := by
  cases j with
  | zero => exact east_wall c t
  | succ j => rfl

private theorem reapply (x y z : Bool) : rule (xor x (y || z)) y z = x := by
  cases x <;> cases y <;> cases z <;> rfl

theorem world_step (c : Trace) (t : Nat) (x : Int) :
    world c (t+1) x = rule (world c t (x-1)) (world c t x) (world c t (x+1)) := by
  cases x with
  | ofNat j =>
    cases j with
    | zero =>
      change east c (t+1) 0 = rule ((pair c 1).1 t) (east c t 0) (east c t 1)
      rw [east_wall,east_wall]
      exact (reapply _ _ _).symm
    | succ j =>
      change rule (east c t j) (east c t (j+1)) (east c t (j+2)) = _
      rw [show ((Int.ofNat (j+1))-1) = Int.ofNat j by change (↑(j+1):Int)-1=↑j; omega,
          show ((Int.ofNat (j+1))+1) = Int.ofNat (j+2) by change (↑(j+1):Int)+1=↑(j+2); omega]
      rfl
  | negSucc j =>
    rw [show Int.negSucc j = -((j+1:Nat):Int) by omega,
        show -((j+1:Nat):Int)-1 = -((j+2:Nat):Int) by omega,
        show -((j+1:Nat):Int)+1 = -(j:Int) by omega,
        world_nonpos,world_nonpos,world_nonpos,world_nonpos]
    exact (reapply _ _ _).symm

def ray (c : Trace) (j t : Nat) : Bool := world c t ((t:Int)-(j:Int))

private theorem ray_zero (c : Trace) (t : Nat) : ray c 0 t = c 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold ray at *
    simp only [Int.natCast_zero,Int.sub_zero] at *
    rw [world_step,show ((↑(t+1):Int)-1)=(t:Int) by omega,ih]
    change rule _ (east c t (t+1)) (east c t (t+2)) = _
    rw [east_outside _ _ _ (by omega),east_outside _ _ _ (by omega)]
    cases c 0 <;> rfl

private theorem ray_one_step (c : Trace) (t : Nat) :
    ray c 1 (t+1) = xor (ray c 1 t) (ray c 0 t) := by
  unfold ray
  simp only [Int.natCast_one,Int.natCast_zero,Int.sub_zero]
  rw [show (↑(t+1):Int)-(1:Int)=(t:Int) by omega,world_step]
  change rule _ _ (east c t (t+1)) = _
  rw [east_outside _ _ _ (by omega)]
  simp [rule]

private theorem ray_step (c : Trace) (j t : Nat) :
    ray c (j+2) (t+1) = xor (ray c (j+2) t) (ray c (j+1) t || ray c j t) := by
  unfold ray
  rw [world_step]
  unfold rule
  congr 1
  · congr 1 <;> omega
  · congr 1 <;> congr 1 <;> omega

private theorem double_integral {f g : Trace} (p : Nat)
    (law : ∀ t, f (t+1) = xor (f t) (g t))
    (period : ∀ t, g (t+p) = g t) : ∀ t, f (t+2*p) = f t := by
  have incr (t : Nat) : xor (f (t+p)) (f t) = xor (f p) (f 0) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show t+1+p = t+p+1 by omega, law (t+p),law t,period,bxCancel,ih]
  intro t
  have h := (incr (t+p)).trans (incr t).symm
  rw [show t+p+p=t+2*p by omega] at h
  generalize f (t+2*p)=a at *
  generalize f (t+p)=b at *
  generalize f t=z at *
  cases a <;> cases b <;> cases z <;> simp_all

theorem ray_period (c : Trace) (j t : Nat) : ray c j (t+2^j) = ray c j t := by
  induction j using Nat.strongRecOn generalizing t with
  | ind j ih =>
    cases j with
    | zero => rw [ray_zero,ray_zero]
    | succ j =>
      cases j with
      | zero =>
        exact double_integral 1 (ray_one_step c) (fun s => by rw [ray_zero,ray_zero]) t
      | succ j =>
        let p := 2^(j+1)
        have lo (s : Nat) : ray c j (s+p) = ray c j s := by
          have a := ih j (by omega) (s+2^j)
          have b := ih j (by omega) s
          rw [show s+p=s+2^j+2^j by dsimp [p]; rw [Nat.pow_succ]; omega,a,b]
        have per (s : Nat) :
            (ray c (j+1) (s+p) || ray c j (s+p)) = (ray c (j+1) s || ray c j s) := by
          rw [lo,ih (j+1) (by omega)]
        have h := double_integral p (ray_step c j) per t
        simpa [p,Nat.pow_succ,Nat.mul_comm] using h

/-- Exact reading of a WEST row-zero coefficient inside the independently
initialized EAST cone. The strobe is derived, never a presumed row return. -/
theorem origin_east_read (c : Trace) (j : Nat) :
    origin c j = east c (2^j) (2^j-j) := by
  have cap : j ≤ 2^j := Nat.le_of_lt Nat.lt_two_pow_self
  have h := ray_period c j 0
  simp only [Nat.zero_add] at h
  unfold ray at h
  rw [Int.ofNat_zero,Int.zero_sub,world_nonpos] at h
  rw [show (↑(2^j:Nat):Int)-(j:Int)=((2^j-j:Nat):Int) by omega] at h
  exact h.symm

/-- Every depth through N can be read at the SAME positive multiple of 2^N.
In particular the multiplier can be P, even when P has an odd factor. -/
theorem common_strobe (c : Trace) (j N k : Nat) (hj : j ≤ N) (hk : 0 < k) :
    east c (2^N*k) (2^N*k-j) = origin c j := by
  have rep (m t : Nat) : ray c j (t+2^j*m) = ray c j t := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ,←Nat.add_assoc,ray_period,ih]
  have dt : 2^N*k=2^j*(2^(N-j)*k) := by
    rw [←Nat.mul_assoc,←Nat.pow_add]
    congr 2
    omega
  have cap : j ≤ 2^N*k := by
    have h := Nat.lt_two_pow_self (n:=N)
    have hm := Nat.mul_le_mul_left (2^N) (show 1≤k by omega)
    simp only [Nat.mul_one] at hm
    omega
  have h := rep (2^(N-j)*k) 0
  rw [Nat.zero_add,←dt] at h
  unfold ray at h
  rw [Int.natCast_zero,Int.zero_sub,world_nonpos,
      show (↑(2^N*k:Nat):Int)-(j:Int)=((2^N*k-j:Nat):Int) by omega] at h
  exact h

/-- Independent west half. Unlike pair, it is initialized white on every
strict-west site even when the supplied candidate has a bad inverse seed. -/
def west (c : Trace) : Nat → Nat → Bool
  | 0, 0 => c 0
  | 0, _+1 => false
  | t+1, 0 => c (t+1)
  | t+1, d+1 => rule (west c t (d+2)) (west c t (d+1)) (west c t d)

private theorem west_wall (c : Trace) (t : Nat) : west c t 0 = c t := by cases t <;> rfl

private theorem west_vac (c : Trace) (t d : Nat) (h : t < d) : west c t d = false := by
  induction t generalizing d with
  | zero => cases d <;> simp_all [west]
  | succ t ih =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
    change rule (west c t (j+2)) (west c t (j+1)) (west c t j) = false
    rw [ih _ (by omega),ih _ (by omega),ih _ (by omega)]
    rfl

theorem west_tip (c : Trace) (mark : c 0 = true) (t : Nat) : west c t t = true := by
  induction t with
  | zero => exact mark
  | succ t ih =>
    change rule (west c t (t+2)) (west c t (t+1)) (west c t t) = true
    rw [west_vac _ _ _ (by omega),west_vac _ _ _ (by omega),ih]
    rfl

private theorem pair_step (c : Trace) (t d : Nat) :
    (pair c (d+1)).1 (t+1) =
    rule ((pair c (d+2)).1 t) ((pair c (d+1)).1 t) ((pair c d).1 t) := by
  exact (reapply _ _ _).symm

/-- Finite anchoring, not an assumption that the inverse seed vanishes
at all depths. It suffices to check through the far endpoint of this cone. -/
theorem finite_west (c : Trace) (t d : Nat)
    (blank : ∀ j, 0<j → j≤t+d → origin c j=false) :
    (pair c d).1 t = west c t d := by
  induction t generalizing d with
  | zero =>
    cases d with
    | zero => rfl
    | succ d => exact blank (d+1) (by omega) (by omega)
  | succ t ih =>
    cases d with
    | zero => exact (west_wall c (t+1)).symm
    | succ d =>
      rw [pair_step]
      change rule _ _ _ = rule (west c t (d+2)) (west c t (d+1)) (west c t d)
      rw [ih (d+2) (by intro j j0 jj; exact blank j j0 (by omega)),
          ih (d+1) (by intro j j0 jj; exact blank j j0 (by omega)),
          ih d (by intro j j0 jj; exact blank j j0 (by omega))]

def gate (c : Trace) (t : Nat) : Bool := c t || east c t 1

/-- A finite vertical gate record decodes the whole west end of a chosen
sideways diagonal. Black-wall times require no strict east information. -/
theorem finite_decode (c : Trace) (d s u : Nat)
    (wall : ∀ i, i≤d → c (s+i)=c (u+i))
    (gates : ∀ i, i<d → gate c (s+i)=gate c (u+i)) :
    (pair c d).1 s = (pair c d).1 u := by
  induction d using Nat.strongRecOn generalizing s u with
  | ind d ih =>
    cases d with
    | zero => simpa [pair] using wall 0 (by omega)
    | succ d =>
      cases d with
      | zero =>
        change xor (c (s+1)) (gate c s) = xor (c (u+1)) (gate c u)
        rw [wall 1 (by omega),show gate c s = gate c u by simpa using gates 0 (by omega)]
      | succ d =>
        change xor ((pair c (d+1)).1 (s+1)) ((pair c (d+1)).1 s || (pair c d).1 s) =
          xor ((pair c (d+1)).1 (u+1)) ((pair c (d+1)).1 u || (pair c d).1 u)
        rw [ih (d+1) (by omega) (s+1) (u+1)
              (by intro i hi; simpa [Nat.add_assoc] using wall (1+i) (by omega))
              (by intro i hi; simpa [Nat.add_assoc] using gates (1+i) (by omega)),
            ih (d+1) (by omega) s u
              (by intro i hi; exact wall i (by omega))
              (by intro i hi; exact gates i (by omega)),
            ih d (by omega) s u
              (by intro i hi; exact wall i (by omega))
              (by intro i hi; exact gates i (by omega))]

/-- Two separately initialized, finite certificates on opposite sides give
a positive right strobe. The match lasts d samples, ending at ANY later
black strictly beyond the older rim, not necessarily the later rim u. -/
theorem crossing_strobe (c : Trace) (s u d k : Nat) (su : s < u) (old : s < d)
    (newer : west c u d = true) (hk : 0<k)
    (wall : ∀ i, i≤d → c (s+i)=c (u+i))
    (gates : ∀ i, i<d → gate c (s+i)=gate c (u+i)) :
    ∃ j, 0<j ∧ j≤u+d ∧ east c (2^(u+d)*k) (2^(u+d)*k-j)=true := by
  by_cases hit : ∃ j, 0<j ∧ j≤u+d ∧ origin c j=true
  · obtain ⟨j,hj,hn,h⟩ := hit
    exact ⟨j,hj,hn,(common_strobe c j (u+d) k hn hk).trans h⟩
  · have blank (j : Nat) (p : 0<j) (n : j≤u+d) : origin c j=false := by
      cases e : origin c j with
      | false => rfl
      | true => exact False.elim (hit ⟨j,p,n,e⟩)
    have same := finite_decode c d s u wall gates
    rw [finite_west c s d (by intro j p n; exact blank j p (by omega)),
      finite_west c u d blank,west_vac _ _ _ old,newer] at same
    contradiction

/-- A marked finite crossing uses equality at two actual phases of the
candidate gate stream. No repetition of full rows or masks is posited. -/
def Seam (c : Trace) : Prop :=
  ∃ s u d, s<u ∧ s<d ∧ west c u d=true ∧
    (∀ i, i≤d → c (s+i)=c (u+i)) ∧
    (∀ i, i<d → gate c (s+i)=gate c (u+i))

private theorem rule_left_inj {a b x y : Bool} (e : rule a x y = rule b x y) : a = b := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all [rule]

/-- At two clock-aligned cuts, the first differing strictly western bit
travels one site toward the wall on every tick until it reaches depth one. -/
theorem west_first_split (c : Trace) (r s u : Nat)
    (wall : ∀ i, i≤r → c (s+i)=c (u+i))
    (lower : ∀ j, j<r+1 → west c s j=west c u j)
    (split : west c s (r+1) ≠ west c u (r+1)) :
    west c (s+r) 1 ≠ west c (u+r) 1 := by
  induction r generalizing s u with
  | zero => simpa using split
  | succ r ih =>
    have sub (j : Nat) (hj : j<r+1) : west c (s+1) j = west c (u+1) j := by
      cases j with
      | zero => exact wall 1 (by omega)
      | succ j =>
        change rule (west c s (j+2)) (west c s (j+1)) (west c s j) =
          rule (west c u (j+2)) (west c u (j+1)) (west c u j)
        rw [lower (j+2) (by omega),lower (j+1) (by omega),lower j (by omega)]
    have diff : west c (s+1) (r+1) ≠ west c (u+1) (r+1) := by
      change rule (west c s (r+2)) (west c s (r+1)) (west c s r) ≠
        rule (west c u (r+2)) (west c u (r+1)) (west c u r)
      rw [lower (r+1) (by omega),lower r (by omega)]
      exact fun h => split (rule_left_inj h)
    have h := ih (s+1) (u+1)
      (by intro i hi; simpa [Nat.add_assoc] using wall (1+i) (by omega)) sub diff
    simpa only [show s+1+r=s+(r+1) by omega,show u+1+r=u+(r+1) by omega] using h

/-- Only ONE eastern OR reading is needed. There is no premise that right
neighbours or gate blocks repeat. At a black arrival this equality is free. -/
theorem first_split_strobe (c : Trace) (s u r k : Nat) (su : s<u) (hk : 0<k)
    (wall : ∀ i, i≤r+1 → c (s+i)=c (u+i))
    (lower : ∀ j, j<r+1 → west c s j=west c u j)
    (split : west c s (r+1) ≠ west c u (r+1))
    (oneGate : gate c (s+r)=gate c (u+r)) :
    ∃ j, 0<j ∧ j≤u+r+1 ∧ east c (2^(u+r+1)*k) (2^(u+r+1)*k-j)=true := by
  by_cases hit : ∃ j, 0<j ∧ j≤u+r+1 ∧ origin c j=true
  · obtain ⟨j,pos,le,h⟩ := hit
    exact ⟨j,pos,le,(common_strobe c j (u+r+1) k le hk).trans h⟩
  · have blank (j : Nat) (p : 0<j) (n : j≤u+r+1) : origin c j=false := by
      cases e : origin c j with
      | false => rfl
      | true => exact False.elim (hit ⟨j,p,n,e⟩)
    have diff := west_first_split c r s u (fun i hi => wall i (by omega)) lower split
    rw [←finite_west c (s+r) 1 (by intro j p n; exact blank j p (by omega)),
      ←finite_west c (u+r) 1 blank] at diff
    apply False.elim
    apply diff
    change xor (c (s+r+1)) (gate c (s+r))=xor (c (u+r+1)) (gate c (u+r))
    rw [oneGate,show c (s+r+1)=c (u+r+1) by simpa [Nat.add_assoc] using wall (r+1) (by omega)]

def HeadFork (c : Trace) : Prop :=
  ∃ s u r, s<u ∧ (∀ i, i≤r+1 → c (s+i)=c (u+i)) ∧
    (∀ j, j<r+1 → west c s j=west c u j) ∧
    west c s (r+1) ≠ west c u (r+1) ∧ gate c (s+r)=gate c (u+r)

/-- Every aligned pair, not a pair supplied by an unproved return theorem:
the later west tip creates a first split by depth u. If no fork exists,
its mandatory arrival is white and the two independently evolved east bits
are opposite at that very tick. -/
theorem every_pair_splits (c : Trace) (mark : c 0=true) (noFork : ¬HeadFork c)
    (s u : Nat) (su : s<u) (wall : ∀ i, c (s+i)=c (u+i)) :
    ∃ r, r<u ∧ (∀ j, j<r+1 → west c s j=west c u j) ∧
      west c s (r+1) ≠ west c u (r+1) ∧
      c (s+r)=false ∧ east c (s+r) 1 ≠ east c (u+r) 1 := by
  let f (j : Nat) := west c s j ≠ west c u j
  have tip : f u := by simp [f,west_vac c s u su,west_tip c mark u]
  have minimal (n : Nat) (hn : f n) : ∃ d, d≤n ∧ f d ∧ ∀ j, j<d → ¬f j := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases early : ∃ j, j<n ∧ f j
      · obtain ⟨j,lt,h⟩ := early
        obtain ⟨d,dj,fd,first⟩ := ih j lt h
        exact ⟨d,by omega,fd,first⟩
      · exact ⟨n,Nat.le_refl _,hn,fun j lt h => early ⟨j,lt,h⟩⟩
  obtain ⟨d,cap,fd,early⟩ := minimal u tip
  cases d with
  | zero =>
    exact False.elim (fd (by simpa only [west_wall,Nat.add_zero] using wall 0))
  | succ r =>
    have lower (j : Nat) (lt : j<r+1) : west c s j = west c u j := by
      exact Classical.byContradiction (early j lt)
    have gateDiff : gate c (s+r) ≠ gate c (u+r) := fun e =>
      noFork ⟨s,u,r,su,fun i _ => wall i,lower,fd,e⟩
    have white : c (s+r)=false := by
      cases h : c (s+r) with
      | false => rfl
      | true => exact False.elim (gateDiff (by simp [gate,←wall r,h]))
    have other : c (u+r)=false := (wall r).symm.trans white
    exact ⟨r,by omega,lower,fd,white,by simpa [gate,white,other] using gateDiff⟩

/-- A present-time equality collar of k strict eastern cells can lose its
innermost dependency guard only across a white outer cell. Follow it in
one independently initialized east orbit; no future gate matches are input. -/
def guard (c : Trace) (s k : Nat) : Nat → Nat
  | 0 => k
  | i+1 => let d := guard c s k i
           if east c (s+i) d then d else d-1

private theorem guard_one (c : Trace) (a b n : Nat) (wa : c (a+1)=c (b+1))
    (same : ∀ j, j≤n → east c a j=east c b j) :
    ∀ j, j≤(if east c a n then n else n-1) → east c (a+1) j=east c (b+1) j := by
  intro j bound
  cases j with
  | zero => exact wa
  | succ j =>
    have cap : j+1≤n := by split at bound <;> omega
    change rule (east c a j) (east c a (j+1)) (east c a (j+2)) =
      rule (east c b j) (east c b (j+1)) (east c b (j+2))
    rw [same j (by omega)]
    by_cases interior : j+2≤n
    · rw [same (j+1) cap,same (j+2) interior]
    · have edge : j+1=n := by omega
      have black : east c a n=true := by
        cases h : east c a n with
        | true => rfl
        | false => simp [h] at bound; omega
      have black' : east c b n=true := (same n (Nat.le_refl _)).symm.trans black
      rw [edge,black,black']
      simp [rule]

theorem guard_sound (c : Trace) (s u k i : Nat)
    (initial : ∀ j, j≤k → east c s j=east c u j)
    (wall : ∀ h, h≤i → c (s+h)=c (u+h)) :
    ∀ j, j≤guard c s k i → east c (s+i) j=east c (u+i) j := by
  induction i with
  | zero => simpa [guard] using initial
  | succ i ih =>
    exact guard_one c (s+i) (u+i) (guard c s k i)
      (by simpa only [Nat.add_assoc] using wall (i+1) (by omega))
      (ih (fun h small => wall h (by omega)))

/-- A quantitative obstruction at every pair of distinct ages. A first
west split is guaranteed; every matched present east collar must be gone
by that actual finite arrival. This compares the two marked cones without
supposing there is a present or future return of any prescribed width. -/
theorem every_pair_exhausts (c : Trace) (mark : c 0=true) (noFork : ¬HeadFork c)
    (s u : Nat) (su : s<u) (wall : ∀ i, c (s+i)=c (u+i)) :
    ∃ r, r<u ∧ (∀ j, j<r+1 → west c s j=west c u j) ∧
      west c s (r+1) ≠ west c u (r+1) ∧ c (s+r)=false ∧
      east c (s+r) 1 ≠ east c (u+r) 1 ∧
      ∀ k, (∀ j, j≤k → east c s j=east c u j) → guard c s k r=0 := by
  obtain ⟨r,le,lower,split,white,ne⟩ := every_pair_splits c mark noFork s u su wall
  refine ⟨r,le,lower,split,white,ne,?_⟩
  intro k common
  by_cases z : guard c s k r=0
  · exact z
  · exact False.elim (ne (guard_sound c s u k r common (fun h _ => wall h) 1 (by omega)))

/-- Local period on a single bounded observation interval; no infinite
return or ultimately periodic east column is assumed. -/
def ClockWindow (f : Trace) (a p last : Nat) : Prop :=
  ∀ i r, a+p*i+r≤last → f (a+p*i+r)=f (a+r)

/-- Quantitative two-clock obstruction, extending FixedColumnPair's
infinite-column argument. Only d unknown interior cells can vary. A finite
strip through the stated horizon either forks or contradicts the west tip. -/
theorem finite_cavity (c : Trace) (mark : c 0=true) (a p d : Nat) (pos : 0<p)
    (wall : ∀ i r, c (a+p*i+r)=c (a+r))
    (right : ClockWindow (fun t => east c t (d+1)) a p (2*(a+p*2^d))) :
    HeadFork c := by
  apply Classical.byContradiction
  intro noFork
  let f (i j : Nat) := east c (a+p*i) (j+1)
  let bits (i : Nat) := FiniteWindowRecurrence.window (f i) d 0
  let code (i : Nat) := FiniteWindowRecurrence.encode (bits i)
  obtain ⟨i,j,lt,cap,e⟩ := QuantifiedSplit.repeat_le (2^d) code
    (fun n _ => by simpa only [code,bits,FiniteWindowRecurrence.window_len] using
      FiniteWindowRecurrence.encode_bound (bits n))
  have words : bits i=bits j := FiniteWindowRecurrence.same_encode_eq
    (by simp [bits,FiniteWindowRecurrence.window_len]) e
  let s := a+p*i
  let u := a+p*j
  have su : s<u := Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left lt pos) a
  have ub : u≤a+p*2^d := Nat.add_le_add_left (Nat.mul_le_mul_left p cap) a
  have same (h : Nat) : c (s+h)=c (u+h) := (wall i h).trans (wall j h).symm
  have outer (h : Nat) (ht : h≤u) : east c (s+h) (d+1)=east c (u+h) (d+1) := by
    exact (right i h (by change s+h≤_; omega)).trans
      (right j h (by change u+h≤_; omega)).symm
  have band (h : Nat) (ht : h≤u) (x : Nat) (hx : x≤d+1) : east c (s+h) x=east c (u+h) x := by
    induction h generalizing x with
    | zero =>
      cases x with
      | zero => simpa [east_wall] using same 0
      | succ x =>
        by_cases top : x=d
        · subst x; exact outer 0 (by omega)
        · have inside : x<d := by omega
          have val := congrArg (fun q : List Bool => q[x]?) words
          change (FiniteWindowRecurrence.window (f i) d 0)[x]? =
            (FiniteWindowRecurrence.window (f j) d 0)[x]? at val
          rw [List.getElem?_eq_getElem (by simpa [FiniteWindowRecurrence.window_len] using inside),
            List.getElem?_eq_getElem (by simpa [FiniteWindowRecurrence.window_len] using inside),
            FiniteWindowRecurrence.window_at _ _ _ _ inside,
            FiniteWindowRecurrence.window_at _ _ _ _ inside,Nat.zero_add] at val
          exact Option.some.inj val
    | succ h ih =>
      cases x with
      | zero => rw [east_wall,east_wall,same]
      | succ x =>
        by_cases top : x=d
        · subst x; exact outer (h+1) ht
        · change rule (east c (s+h) x) (east c (s+h) (x+1)) (east c (s+h) (x+2)) =
            rule (east c (u+h) x) (east c (u+h) (x+1)) (east c (u+h) (x+2))
          rw [ih (by omega) x (by omega),ih (by omega) (x+1) (by omega),
            ih (by omega) (x+2) (by omega)]
  obtain ⟨r,ru,_,_,_,ne⟩ := every_pair_splits c mark noFork s u su same
  exact ne (band r (by omega) 1 (by omega))

/-- The two inputs are the wall and its effective OR gate. Separating them
allows a cyclic test gate to be compared with the true one, not confused
with the independent half-line that supplies the actual observations. -/
def invertGate (m g : Trace) : Nat → Trace
  | 0 => m
  | 1 => fun t => xor (m (t+1)) (g t)
  | n+2 => unleft (invertGate m g (n+1)) (invertGate m g n)

theorem invert_step (m g : Trace) (d t : Nat) :
    invertGate m g (d+1) (t+1) =
    rule (invertGate m g (d+2) t) (invertGate m g (d+1) t) (invertGate m g d t) :=
  (reapply _ _ _).symm

private theorem invert_agree (m g h : Trace) (d t : Nat)
    (common : ∀ i, i<d → g (t+i)=h (t+i)) : invertGate m g d t=invertGate m h d t := by
  induction d using Nat.strongRecOn generalizing t with
  | ind d ih =>
    rcases d with _|d
    · rfl
    rcases d with _|d
    · have e := common 0 (by omega)
      simpa [invertGate,Nat.add_zero] using congrArg (xor (m (t+1))) e
    · simp only [invertGate,unleft]
      rw [ih (d+1) (by omega) (t+1)
            (by intro i hi; simpa only [Nat.add_assoc] using common (1+i) (by omega)),
          ih (d+1) (by omega) t (fun i hi => common i (by omega)),
          ih d (by omega) t (fun i hi => common i (by omega))]

private theorem invert_true (c : Trace) (s d t : Nat) :
    invertGate (fun i => c (s+i)) (fun i => gate c (s+i)) d t=(pair c d).1 (s+t) := by
  induction d using Nat.strongRecOn generalizing t with
  | ind d ih =>
    rcases d with _|d
    · rfl
    rcases d with _|d
    · rfl
    · let m := fun i => c (s+i)
      let g := fun i => gate c (s+i)
      change xor (invertGate m g (d+1) (t+1)) (invertGate m g (d+1) t || invertGate m g d t) =
        xor ((pair c (d+1)).1 (s+t+1)) ((pair c (d+1)).1 (s+t) || (pair c d).1 (s+t))
      rw [ih (d+1) (by omega),ih (d+1) (by omega),ih d (by omega),Nat.add_assoc]

def cyclicWest (c : Trace) (s Q : Nat) : Nat → Trace :=
  invertGate (fun i => c (s+i)) (fun i => gate c (s+i%Q))

private theorem cyclic_earlier (c : Trace) (s Q d : Nat) (cap : d≤Q) :
    cyclicWest c s Q d 0=(pair c d).1 s := by
  have e := invert_agree (fun i => c (s+i)) (fun i => gate c (s+i%Q)) (fun i => gate c (s+i)) d 0
    (by intro i hi; simp only [Nat.zero_add,Nat.mod_eq_of_lt (show i<Q by omega)])
  simpa only [cyclicWest,invert_true,Nat.add_zero] using e

private theorem inv_period (m g : Trace) (Q : Nat) (mp : ∀ t,m (t+Q)=m t)
    (gp : ∀ t,g (t+Q)=g t) (d t : Nat) :
    invertGate m g d (t+Q)=invertGate m g d t := by
  induction d using Nat.strongRecOn generalizing t with
  | ind d ih =>
    rcases d with _|d
    · exact mp _
    rcases d with _|d
    · change xor (m (t+Q+1)) (g (t+Q))=xor (m (t+1)) (g t)
      rw [show t+Q+1=t+1+Q by omega,mp,gp]
    · simp only [invertGate,unleft]
      rw [show t+Q+1=t+1+Q by omega,ih (d+1) (by omega),ih (d+1) (by omega),ih d (by omega)]

/-- If the initial phase row agrees up to the cone endpoint, it advances
as the independent west half within that cone. -/
private theorem inv_west_cone (c g : Trace) (s d t : Nat)
    (init : ∀ j, j≤d+t → invertGate (fun i => c (s+i)) g j 0=west c s j) :
    invertGate (fun i => c (s+i)) g d t=west c (s+t) d := by
  induction t generalizing d with
  | zero => exact init d (by omega)
  | succ t ih =>
    cases d with
    | zero => exact (west_wall c (s+(t+1))).symm
    | succ d =>
      rw [invert_step]
      change rule _ _ _ = rule (west c (s+t) (d+2)) (west c (s+t) (d+1)) (west c (s+t) d)
      rw [ih (d+2) (by intro j hj; exact init j (by omega)),
        ih (d+1) (by intro j hj; exact init j (by omega)),ih d (by intro j hj; exact init j (by omega))]

/-- A finite cyclic inverse must manufacture an extra west mark. If the
actual seed has no positive coefficient through s+Q, this mark lies strictly
beyond Q; it is a mark of the CYCLIC inverse, not of the true origin. -/
theorem cyclic_mark (c : Trace) (s Q : Nat) (mark : c 0=true) (pos : 0<Q) (start : s≤Q)
    (clock : ∀ i,c (s+(i+Q))=c (s+i))
    (blank : ∀ j, 0<j → j≤s+Q → origin c j=false) :
    ∃ b, Q<b ∧ b≤s+2*Q ∧ cyclicWest c s Q b 0=true ∧
      ∀ j, j<b → cyclicWest c s Q j 0=west c s j := by
  let v := cyclicWest c s Q
  have upto (j : Nat) (hj : j≤Q) : v j 0=west c s j :=
    (cyclic_earlier c s Q j hj).trans (finite_west c s j (fun n hn hcap => blank n hn (by omega)))
  have cyc (j : Nat) : v j Q=v j 0 := by
    have e := inv_period (fun i => c (s+i)) (fun i => gate c (s+i%Q)) Q clock
      (by intro t; simp) j 0
    simpa only [v,cyclicWest,Nat.zero_add] using e
  let bad (j : Nat) := v j 0≠west c s j
  have any : ∃ j, j≤s+2*Q ∧ bad j := by
    apply Classical.byContradiction
    intro no
    have same (j : Nat) (hj : j≤s+2*Q) : v j 0=west c s j :=
      Classical.byContradiction (fun ne => no ⟨j,hj,ne⟩)
    have ray := inv_west_cone c (fun i => gate c (s+i%Q)) s (s+Q) Q
      (fun j hj => same j (by omega))
    change v (s+Q) Q=west c (s+Q) (s+Q) at ray
    rw [cyc,same (s+Q) (by omega),west_vac _ _ _ (by omega),west_tip _ mark] at ray
    contradiction
  have least (n : Nat) (b : bad n) : ∃ j, j≤n ∧ bad j ∧ ∀ i, i<j → ¬bad i := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases prior : ∃ i, i<n ∧ bad i
      · obtain ⟨i,lt,badI⟩ := prior
        obtain ⟨j,ji,e,low⟩ := ih i lt badI
        exact ⟨j,by omega,e,low⟩
      · exact ⟨n,Nat.le_refl _,b,fun i hi bi => prior ⟨i,hi,bi⟩⟩
  obtain ⟨n,cap,badn⟩ := any
  obtain ⟨b,bn,err,low⟩ := least n badn
  have large : Q<b := by
    by_cases le : b≤Q
    · exact False.elim (err (upto b le))
    · omega
  have white := west_vac c s b (by omega)
  have one : v b 0=true := by
    cases e : v b 0 with
    | false => exact False.elim (err (e.trans white.symm))
    | true => rfl
  exact ⟨b,large,by omega,one,fun j hj => Classical.byContradiction (low j hj)⟩

/-- Direct transfer, with a bound on the actual coefficient. A cyclic
extra mark survives if its corresponding TRUE sideways bit is also black,
even if there have been earlier true/cyclic differences. -/
theorem true_mark_strobe (c : Trace) (s b k : Nat) (beyond : s<b) (hk : 0<k)
    (real : (pair c b).1 s=true) :
    ∃ j, 0<j ∧ j≤s+b ∧ east c (2^(s+b)*k) (2^(s+b)*k-j)=true := by
  apply Classical.byContradiction
  intro miss
  have blank (j : Nat) (pos : 0<j) (le : j≤s+b) : origin c j=false := by
    cases e : origin c j with
    | true => exact False.elim (miss ⟨j,pos,le,(common_strobe c j (s+b) k le hk).trans e⟩)
    | false => rfl
  rw [finite_west c s b blank,west_vac c s b beyond] at real
  contradiction

/-- The newest gate appears exactly once. This provides both directions:
a first gate error cannot disappear, and a first inverse-bit error cannot
be attributed to some unspecified earlier mismatch. -/
private theorem invert_tip (m g h : Trace) (r t : Nat)
    (before : ∀ i, i<r → g (t+i)=h (t+i)) :
    xor (invertGate m g (r+1) t) (invertGate m h (r+1) t) = xor (g (t+r)) (h (t+r)) := by
  induction r generalizing t with
  | zero =>
    change xor (xor (m (t+1)) (g t)) (xor (m (t+1)) (h t))=xor (g t) (h t)
    cases m (t+1) <;> cases g t <;> cases h t <;> rfl
  | succ r ih =>
    have now := invert_agree m g h (r+1) t before
    have near := invert_agree m g h r t (fun i hi => before i (by omega))
    have ahead := ih (t+1) (fun i hi => by
      simpa only [Nat.add_assoc] using before (1+i) (by omega))
    change xor (xor (invertGate m g (r+1) (t+1)) (invertGate m g (r+1) t || invertGate m g r t))
      (xor (invertGate m h (r+1) (t+1)) (invertGate m h (r+1) t || invertGate m h r t)) = _
    rw [now,near,bxCancel,ahead,show t+1+r=t+(r+1) by omega]

/-- Under the no-hit alternative the first manufactured black is removed
by exactly the last gate of its diagonal. All prior cyclic reads, including
those past a complete Q-cycle, agree with the actual east response. -/
theorem first_cyclic_tear (c : Trace) (s Q r : Nat) (old : s<r+1)
    (extra : cyclicWest c s Q (r+1) 0=true)
    (first : ∀ j, j<r+1 → cyclicWest c s Q j 0=west c s j)
    (blank : ∀ j, 0<j → j≤s+(r+1) → origin c j=false) :
    (∀ i, i<r → gate c (s+i)=gate c (s+i%Q)) ∧
      gate c (s+r) ≠ gate c (s+r%Q) := by
  let m := fun i => c (s+i)
  let g := fun i => gate c (s+i)
  let h := fun i => gate c (s+i%Q)
  have real (j : Nat) (le : j≤r+1) : invertGate m g j 0=west c s j := by
    rw [invert_true,finite_west _ _ _ (fun j' pos jb => blank j' pos (by omega))]
    rfl
  have prior (i : Nat) (hi : i<r) : g i=h i := by
    induction i using Nat.strongRecOn with
    | ind i ih =>
      have t := invert_tip m g h i 0 (fun k hk => by simpa only [Nat.zero_add] using ih k hk (by omega))
      simp only [Nat.zero_add] at t
      have eq : invertGate m g (i+1) 0=invertGate m h (i+1) 0 :=
        (real _ (by omega)).trans (first _ (by omega)).symm
      rw [eq,Bool.xor_self] at t
      exact bx0 t.symm
  have tip := invert_tip m g h r 0 (fun k hk => by simpa only [Nat.zero_add] using prior k hk)
  simp only [Nat.zero_add] at tip
  have left0 : invertGate m g (r+1) 0=false := (real _ (by omega)).trans (west_vac c s (r+1) old)
  have right1 : invertGate m h (r+1) 0=true := extra
  rw [left0,right1] at tip
  refine ⟨prior,?_⟩
  intro same
  change g r=h r at same
  rw [same,Bool.xor_self] at tip
  contradiction

private theorem inv_west_tip (c g : Trace) (s d t : Nat) (pos : 0<d)
    (first : ∀ j, j<d+t → invertGate (fun i => c (s+i)) g j 0=west c s j) :
    xor (invertGate (fun i => c (s+i)) g d t) (west c (s+t) d) =
    xor (invertGate (fun i => c (s+i)) g (d+t) 0) (west c s (d+t)) := by
  induction t generalizing d with
  | zero => rfl
  | succ t ih =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
    let m := fun i => c (s+i)
    change xor (invertGate m g (n+1) (t+1)) (west c ((s+t)+1) (n+1)) = _
    rw [invert_step]
    change xor (xor (invertGate m g (n+2) t) (invertGate m g (n+1) t || invertGate m g n t))
      (xor (west c (s+t) (n+2)) (west c (s+t) (n+1) || west c (s+t) n)) = _
    rw [inv_west_cone c g s (n+1) t (fun j hj => first j (by omega)),
      inv_west_cone c g s n t (fun j hj => first j (by omega)),bxCancel,
      ih (n+2) (by omega) (fun j hj => first j (by omega)),
      show n+2+t=(n+1)+(t+1) by omega]

/-- The first cyclic excess has a second, independent location formula.
Read only the WEST halves at ages s and s+Q: the first split there is
exactly Q sites closer to the wall than this mark reconstructed from the
first Q EAST gate samples. No later east reads enter this comparison. -/
theorem cyclic_offset (c : Trace) (s Q b : Nat) (pos : 0<Q) (large : Q<b)
    (old : s<b) (clock : ∀ i,c (s+(i+Q))=c (s+i))
    (extra : cyclicWest c s Q b 0=true)
    (first : ∀ j, j<b → cyclicWest c s Q j 0=west c s j) :
    (∀ j, j<b-Q → west c s j=west c (s+Q) j) ∧
    west c s (b-Q) ≠ west c (s+Q) (b-Q) := by
  let g := fun i => gate c (s+i%Q)
  let v := cyclicWest c s Q
  change v b 0=true at extra
  change ∀ j, j<b → v j 0=west c s j at first
  have cyc (j : Nat) : v j Q=v j 0 := by
    have e := inv_period (fun i => c (s+i)) g Q clock (by intro t; simp [g]) j 0
    simpa only [v,g,cyclicWest,Nat.zero_add] using e
  constructor
  · intro j hj
    have e := inv_west_cone c g s j Q (fun i hi => first i (by omega))
    change v j Q = west c (s+Q) j at e
    rw [cyc,first j (by omega)] at e
    exact e
  · have t := inv_west_tip c g s (b-Q) Q (by omega) (fun i hi => first i (by omega))
    change xor (v (b-Q) Q) (west c (s+Q) (b-Q)) =
      xor (v (b-Q+Q) 0) (west c s (b-Q+Q)) at t
    rw [show b-Q+Q=b by omega,cyc,first (b-Q) (by omega),extra,west_vac _ _ _ old] at t
    intro eq
    rw [eq,Bool.xor_self] at t
    contradiction

/-- A white wall latches its actual eastern head once it is black. The
next effective gate is then one even if the wall switches to black. -/
private theorem gate_latched (c : Trace) (t : Nat) (white : c t=false)
    (high : gate c t=true) : gate c (t+1)=true := by
  have one : east c t 1=true := by simpa [gate,white] using high
  have nxt : east c (t+1) 1=true := by
    change rule (east c t 0) (east c t 1) (east c t 2)=true
    rw [east_wall,white,one]
    simp [rule]
  simp [gate,nxt]

/-- Keep the measured cyclic input before the tear, then insert one
threshold. Nothing here reads a genuine gate after the initial Q block. -/
def repairedInput (c : Trace) (s Q r a i : Nat) : Bool :=
  if i<r then gate c (s+i%Q) else decide (r+a≤i)

def Cleans (c : Trace) (s Q r n a : Nat) : Prop :=
  a≤n ∧ ∀ j, r+1≤j → j≤r+n+1 →
    invertGate (fun i => c (s+i)) (repairedInput c s Q r a) j 0=false

private theorem clean_unique_aux (c : Trace) (s Q r n a b : Nat)
    (ca : Cleans c s Q r n a) (cb : Cleans c s Q r n b) : ¬a<b := by
  intro lt
  let m := fun i => c (s+i)
  let f := repairedInput c s Q r a
  let g := repairedInput c s Q r b
  have prior (i : Nat) (hi : i<r+a) : f (0+i)=g (0+i) := by
    simp only [f,g,repairedInput,Nat.zero_add]
    split
    · rfl
    · simp [show ¬r+a≤i by omega,show ¬r+b≤i by omega]
  have tip := invert_tip m f g (r+a) 0 prior
  rw [ca.2 (r+a+1) (by omega) (by have := ca.1; omega),
      cb.2 (r+a+1) (by omega) (by have := ca.1; omega),Bool.xor_self] at tip
  simp [f,g,repairedInput,show ¬r+a<r by omega,show ¬r+b≤r+a by omega] at tip

theorem clean_unique (c : Trace) (s Q r n a b : Nat)
    (ca : Cleans c s Q r n a) (cb : Cleans c s Q r n b) : a=b := by
  have lo := clean_unique_aux c s Q r n a b ca cb
  have hi := clean_unique_aux c s Q r n b a cb ca
  omega

/-- Keep the inlet low until further notice. The first black left by this
probe identifies the forced eastern rise time without searching thresholds. -/
def lowProbe (c : Trace) (s Q r i : Nat) : Bool :=
  invertGate (fun k => c (s+k)) (fun k => if k<r then gate c (s+k%Q) else false) (r+i+1) 0

theorem first_low_probe (c : Trace) (s Q r n a : Nat) (clean : Cleans c s Q r n a) :
    (∀ i, i<a → lowProbe c s Q r i=false) ∧ lowProbe c s Q r a=true := by
  let m := fun k => c (s+k)
  let f := fun k => if k<r then gate c (s+k%Q) else false
  let g := repairedInput c s Q r a
  have same (i : Nat) (hi : i<r+a) : f (0+i)=g (0+i) := by
    simp only [f,g,repairedInput,Nat.zero_add]
    split
    · rfl
    · simp [show ¬r+a≤i by omega]
  constructor
  · intro i hi
    exact (invert_agree m f g (r+i+1) 0 (fun j hj => same j (by omega))).trans
      (clean.2 _ (by omega) (by have := clean.1; omega))
  · have tip := invert_tip m f g (r+a) 0 same
    rw [clean.2 _ (by omega) (by have := clean.1; omega)] at tip
    simpa [lowProbe,m,f,g,repairedInput,show ¬r+a<r by omega] using tip

/-- This is the whole white suffix of the tear followed by the first
black. The cutoff is determined before looking at any post-cycle eastern
sample: the finite inverse strip has at most one threshold cleaning it. -/
def Repairs (c : Trace) (s Q r : Nat) : Prop :=
  ∀ n, (∀ i, i<n → c (s+r+i)=false) → c (s+r+n)=true →
    ∃ a, Cleans c s Q r n a ∧ (a=0 ↔ gate c (s+r%Q)=false) ∧
      (∀ i, i<a → lowProbe c s Q r i=false) ∧ lowProbe c s Q r a=true

theorem actual_repair (c : Trace) (s Q r n : Nat) (old : s<r+1)
    (prior : ∀ i, i<r → gate c (s+i)=gate c (s+i%Q))
    (tear : gate c (s+r)≠gate c (s+r%Q))
    (white : ∀ i, i<n → c (s+r+i)=false) (black : c (s+r+n)=true)
    (blank : ∀ j, 0<j → j≤s+r+n+1 → origin c j=false) :
    ∃ a, Cleans c s Q r n a ∧ (a=0 ↔ gate c (s+r%Q)=false) := by
  let z := fun i => gate c (s+r+i)
  have endone : z n=true := by simp [z,gate,black]
  have least (k : Nat) (hk : z k=true) : ∃ a, a≤k ∧ z a=true ∧ ∀ i, i<a → z i=false := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      by_cases found : ∃ j, j<k ∧ z j=true
      · obtain ⟨j,lt,jx⟩ := found
        obtain ⟨a,le,ax,lower⟩ := ih j lt jx
        exact ⟨a,by omega,ax,lower⟩
      · refine ⟨k,by omega,hk,?_⟩
        intro j lt
        cases e : z j with
        | false => rfl
        | true => exact False.elim (found ⟨j,lt,e⟩)
  obtain ⟨a,cap,hit,low⟩ := least n endone
  have above (i : Nat) (ai : a≤i) (bound : i≤n) : z i=true := by
    induction i with
    | zero => have av : a=0 := by omega
              simpa [av] using hit
    | succ i ih =>
      by_cases av : a=i+1
      · simpa [av] using hit
      · exact gate_latched c (s+r+i) (white i (by omega)) (ih (by omega) (by omega))
  have common (i : Nat) (capI : i≤r+n) : repairedInput c s Q r a i=gate c (s+i) := by
    by_cases lt : i<r
    · simpa [repairedInput,lt] using (prior i lt).symm
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show r≤i by omega)
      have e : s+(r+j)=s+r+j := by omega
      by_cases aj : a≤j
      · have one := above j aj (by omega)
        simpa [repairedInput,e,show ¬r+j<r by omega,show r+a≤r+j by omega,z] using one.symm
      · have zero := low j (by omega)
        simpa [repairedInput,e,show ¬r+j<r by omega,show ¬r+a≤r+j by omega,z] using zero.symm
  refine ⟨a,⟨cap,?_⟩,?_⟩
  · intro j lo hi
    have eq := invert_agree (fun i => c (s+i)) (repairedInput c s Q r a)
      (fun i => gate c (s+i)) j 0
      (by intro i h; simpa only [Nat.zero_add] using common i (by omega))
    rw [eq,invert_true,Nat.add_zero,finite_west c s j (fun i p le => blank i p (by omega)),
      west_vac c s j (by omega)]
  · have firstbit : a=0 ↔ gate c (s+r)=true := by
      constructor
      · intro eq; simpa [eq,z] using hit
      · intro one
        by_cases eq : a=0
        · exact eq
        · have h := low 0 (by omega)
          simp [z,one] at h
    rw [firstbit]
    cases h : gate c (s+r) <;> cases k : gate c (s+r%Q) <;> simp_all

/-- One failed run repair already returns an actual positive origin
coefficient; no true post-Q eastern sample enters the left-hand test. -/
theorem repair_or_strobe (c : Trace) (s Q r n k : Nat) (hk : 0<k) (old : s<r+1)
    (extra : cyclicWest c s Q (r+1) 0=true)
    (first : ∀ j, j<r+1 → cyclicWest c s Q j 0=west c s j)
    (white : ∀ i, i<n → c (s+r+i)=false) (black : c (s+r+n)=true) :
    (∃ a, Cleans c s Q r n a ∧ (a=0 ↔ gate c (s+r%Q)=false) ∧
      (∀ i, i<a → lowProbe c s Q r i=false) ∧ lowProbe c s Q r a=true) ∨
      ∃ j, 0<j ∧ j≤s+r+n+1 ∧ east c (2^(s+r+n+1)*k) (2^(s+r+n+1)*k-j)=true := by
  by_cases positive : ∃ j, 0<j ∧ j≤s+r+n+1 ∧ origin c j=true
  · obtain ⟨j,pos,cap,hit⟩ := positive
    exact Or.inr ⟨j,pos,cap,(common_strobe c j (s+r+n+1) k cap hk).trans hit⟩
  · have blank (j : Nat) (pos : 0<j) (cap : j≤s+r+n+1) : origin c j=false := by
      cases h : origin c j with
      | false => rfl
      | true => exact False.elim (positive ⟨j,pos,cap,h⟩)
    obtain ⟨prior,tear⟩ := first_cyclic_tear c s Q r old extra first
      (fun j p le => blank j p (by omega))
    obtain ⟨a,cleans,sign⟩ := actual_repair c s Q r n old prior tear white black blank
    exact Or.inl ⟨a,cleans,sign,first_low_probe c s Q r n a cleans⟩

/-- The survivor test is exact at the FIRST candidate mark, not just a
sufficient comparison of entire periodic right columns. If this arithmetic
synchronization fails at any Q then the true strobe already has a hit. -/
def TornCycles (c : Trace) (s Q : Nat) : Prop :=
  ∃ r, Q≤r ∧ r+1≤s+2*Q ∧ cyclicWest c s Q (r+1) 0=true ∧
    (∀ j, j<r+1 → cyclicWest c s Q j 0=west c s j) ∧
    (∀ i, i<r → gate c (s+i)=gate c (s+i%Q)) ∧
    gate c (s+r) ≠ gate c (s+r%Q) ∧
    (∀ j, j<r+1-Q → west c s j=west c (s+Q) j) ∧
    west c s (r+1-Q) ≠ west c (s+Q) (r+1-Q)

theorem tear_or_strobe (c : Trace) (s Q k : Nat) (mark : c 0=true) (pos : 0<Q)
    (hk : 0<k) (start : s≤Q) (clock : ∀ i,c (s+(i+Q))=c (s+i)) :
    TornCycles c s Q ∨
      ∃ j, 0<j ∧ j≤2*s+2*Q ∧ east c (2^(2*s+2*Q)*k) (2^(2*s+2*Q)*k-j)=true := by
  by_cases real : ∃ j, 0<j ∧ j≤2*s+2*Q ∧ origin c j=true
  · obtain ⟨j,pos,le,hit⟩ := real
    exact Or.inr ⟨j,pos,le,(common_strobe c j (2*s+2*Q) k le hk).trans hit⟩
  · have blank (j : Nat) (pos : 0<j) (le : j≤2*s+2*Q) : origin c j=false := by
      cases v : origin c j with
      | false => rfl
      | true => exact False.elim (real ⟨j,pos,le,v⟩)
    obtain ⟨b,large,cap,extra,first⟩ := cyclic_mark c s Q mark pos start clock
      (fun j p le => blank j p (by omega))
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b≠0 by omega)
    obtain ⟨prior,tear⟩ := first_cyclic_tear c s Q r (by omega) extra first
      (fun j p le => blank j p (by omega))
    have offset := cyclic_offset c s Q (r+1) pos large (by omega) clock extra first
    exact Or.inl ⟨r,by omega,cap,extra,first,prior,tear,offset⟩

/-- Every putative periodic wall can be specified by a finite onset/period word.
This is a sequence on TIME, never a spatial periodicization of a genuine age row. -/
def repeatWord (c : Trace) (T P i : Nat) : Bool :=
  if i < T then c i else c (T + (i-T) % P)

theorem repeat_return (c : Trace) (T P a : Nat) (ha : T≤a) (i r : Nat) :
    repeatWord c T P (a+P*i+r) = repeatWord c T P (a+r) := by
  simp only [repeatWord,ite_eq_right (show ¬a+P*i+r<T by omega),ite_eq_right (show ¬a+r<T by omega),
    show a+P*i+r-T=(a+r-T)+P*i by omega,Nat.add_mul_mod_self_left]

theorem L1 (c : Trace) (hmark : c 0 = true) (T P : Nat) (hp : 0 < P)
    (seedPrefix : ∀ j, 0 < j → j < T+P → origin (repeatWord c T P) j = false) :
    ∃ j, T+P ≤ j ∧ origin (repeatWord c T P) j = true := by
  let w := repeatWord c T P
  -- One full right-hand snapshot at wall phase zero, all prospective depths
  -- at once. Its tip is already marked. Show there is a SECOND black in a
  -- growing outer collar; no agreement/return of full rows is assumed.
  have hit : ∃ N j, 0 < j ∧ j ≤ N ∧ east w (2^N*P) (2^N*P-j) = true := by
    by_cases seam : Seam w
    · obtain ⟨s,u,d,su,old,newer,wall,gates⟩ := seam
      obtain ⟨j,pos,le,hit⟩ := crossing_strobe w s u d P su old newer hp wall gates
      exact ⟨u+d,j,pos,le,hit⟩
    · -- Remaining case: every common finite gate record forces the later
      -- independently initialized west row blank throughout its excess.
      by_cases fork : HeadFork w
      · obtain ⟨s,u,r,su,clock,lower,split,oneGate⟩ := fork
        obtain ⟨j,pos,le,hit⟩ := first_split_strobe w s u r P su hp clock lower split oneGate
        exact ⟨u+r+1,j,pos,le,hit⟩
      · have mark : w 0=true := by
          change (if 0<T then c 0 else c (T+(0-T)%P))=true
          by_cases t0 : T=0
          · simp [t0,hmark]
          · simp [show 0<T by omega,hmark]
        have forced := every_pair_exhausts w mark fork
        have no_cavity (a d : Nat) (ha : T≤a) :
            ¬ClockWindow (fun t => east w t (d+1)) a P (2*(a+P*2^d)) :=
          fun h => fork (finite_cavity w mark a P d hp (repeat_return c T P a ha) h)
        -- forced applies to EVERY pair of sufficiently late equal clock
        -- phases. Its first west split supplies the location and the white
        -- phase of an independently constrained single east comparison.
        by_cases all_torn : ∀ s q, T≤s → 0<q → s≤P*q → TornCycles w s (P*q)
        · -- The first manufactured mark on EVERY cyclic closure has to
          -- line up exactly with its first true (noncyclic) east tear.
          -- Each subsequent all-white suffix has only one possible repair.
          -- Its rise is the first black of an all-low probe; switching there
          -- must erase every candidate mark THROUGH the following black.
          by_cases all_clean : ∀ s q r, T≤s → 0<q → s≤P*q → P*q≤r →
              cyclicWest w s (P*q) (r+1) 0=true →
              (∀ j, j<r+1 → cyclicWest w s (P*q) j 0=west w s j) → Repairs w s (P*q) r
          · sorry
          · apply Classical.byContradiction
            intro nohit
            apply all_clean
            intro s q r _ _ start large extra first n white black
            rcases repair_or_strobe w s (P*q) r n P hp (by omega) extra first white black with ok|hit
            · exact ok
            · obtain ⟨j,pos,cap,one⟩ := hit
              exact False.elim (nohit ⟨s+r+n+1,j,pos,cap,one⟩)
        · apply Classical.byContradiction
          intro miss
          apply all_torn
          intro s q hs hq cap
          have clock (i : Nat) : w (s+(i+P*q))=w (s+i) := by
            rw [show s+(i+P*q)=s+P*q+i by omega]
            exact repeat_return c T P s hs q i
          rcases tear_or_strobe w s (P*q) P mark (Nat.mul_pos hp hq) hp cap clock with torn|ok
          · exact torn
          · obtain ⟨j,pos,le,one⟩ := ok
            exact False.elim (miss ⟨2*s+2*(P*q),j,pos,le,one⟩)
  obtain ⟨N,j,pos,hj,one⟩ := hit
  rw [common_strobe w j N P hj hp] at one
  refine ⟨j,?_,one⟩
  by_cases small : j < T+P
  · have zero := seedPrefix j pos small
    change origin w j = false at zero
    rw [zero] at one
    contradiction
  · omega

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
