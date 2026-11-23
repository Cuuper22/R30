# Bounds checkpoint after 64431c5: the alternating-center obstruction

**Status.** This is the final research record for the interval after `64431c5`. The new arguments below are mathematical derivations, not new kernel-checked Lean declarations. No new theorem `no_period2_alt` was completed; no changes to Solution, Statement, Audit or the blueprints are part of this checkpoint. In particular, neither the general center conjecture nor exclusion of the period-two tail follows from the results below.

## 1. Exact setting and where the extra hypotheses enter

Write (X_t(x)) for the singleton Rule 30 row and (C_t=X_t(0)). A putative alternating tail has (C_{t+1}=1-C_t). On the white strobes let (q=X_t(1)); a *positive* means a white strobe with (q=1). The physical time between successive positives is (k=2g), where (g) counts white strobes. At a black tick (W_1=X_t(-1)=1); at a white tick (W_1=1-q). The finite strict-west integer is (W_t=sum_{dge1}X_t(-d)2^{d-1}). Its left end really is the singleton's advancing mark, not an abstract infinite tape.

Much of the sharper work concerns the **58203 host**: here the positive-gap word uses 3 and 5, and a 3 is followed by a 5. “Short” and “long” below mean the *outgoing* 3- and 5-gap. The host language is a necessary condition in this branch, not a classification of all period-two right arms. A long/short-dependent result must not be applied to the other hosts without a separate argument. Many realizable finite and periodic right-channel words have no finite marked west, and the converse inference is equally invalid.

Two frames matter:
* (B_j(t)=X_t(j-t)) is normalized from the *left* mark. (B'_j=B_{j-2}\mathbin{\mathrm{xor}}(B_{j-1}\lor B_j)). (B_0=1) and the negative lanes are zero. Write (L_d) for the map truncated to (0,ldots,d-1).
* (A(w)=w\mathbin{\mathrm{xor}}(2w\lor4w)) is normalized from a *right* endpoint; bit 0 is the eastern end. It is a triangular isometry on the 2-adic integers. It permutes each fixed low-bit prefix and is invertible there. For an odd positive integer (w), (A) adds two to the highest occupied index. Its ordinary finite height is (h(w)=\max\{r:A^{-r}win\mathbb N\}), not the existence time of a clamped-west predecessor. A finite genuine full row of age (t) with right tip (t) is (A^t1), of degree (2t) and height (t). The zero-wall west map is (G_0(w)=A(w)\mathbin{\mathrm{div}}2).

For the P2 reduction the zero-wall step is justified: at white the actual center is zero, and at black the old west head is already one, so replacing the center by zero cannot change its OR. Thus on the alternating tail the strict west follows (G_0) at every tick. At white the next black lock requires the two low west bits opposite, i.e. (W\bmod4in\{1,2\}). This is an exact reduction, not a proof that every finite orbit of (G_0^2) escapes. The free white-head trace alone is not forced periodic by the west. The infinite checker and true periodic full-space right channels are important countercontrols.

## 2. Physical two-arm information retained from the P2 work

* On a black row write (a=X_t(-2)). Then (a=X_{t+1}(1)=\neg(X_t(1)\lor X_t(2))), (X_t(-3)=X_t(-5)=1-a), and (X_t(-4)=X_{t+2}(-2)). Successive black-strobe (a)'s cannot both be one. These are shared west/east constraints; arbitrarily copying them to a translated western cut is not legitimate.
* In the 3/5 host a common positive preceding the first genuine choice has the same three east bits on both branches. At a white cut the values of east bits 1,2,3 with (h=0,1,2,3,4) strobes remaining to the next positive are respectively 111, 000, 010, 001, 011. One strobe before a positive the fourth east bit is one; at a positive it is zero. The outgoing short/long decision at the positive is the *single* true east bit (X_t(5)=[g=3]=1-X_t(-7)). If two histories pick a different tile there, the first white pulse discrepancy at offset 3 strobes has the opposite signed discrepancy at offset 5 strobes, with a common zero between. These are physical correlations, not independent edits of the two q digits.
* The frozen west transfer at depth 9 can be read in reverse on this host. In white-strobe notation (q'_n=q_{n+2}\lor q_{n+4}); its pairs of zeros in the binary ternary-head description occur at stride four. The later white depth-12 bit is (q'_n q'_{n+1}=q_{n+2}q_{n+5}), the short-start signal shifted two strobes. The identity is a tag for a past source, not an all-depth renewal.
* Actual ordinary black-parent reconstructions can carry the short-decision bit from east +5 to west −7 several positives later. This does not make +5 a necessary unique ancestor of the new western black: there is a real older west input when the lineage merges near −6. An alternative arm with the same west may produce a local birth instead of this east admission. Conversely, a late east terminal packet can have an arbitrarily delayed contact with the true right tip. This does not bound the genealogical loss of every center pulse.
* Opposed checker parities can exchange labels through a real 1001 gate. A same-founder debit can repeat and a single surviving founder can branch; counting raw debits or label switches does not give a cumulative bound. On the true east, the ordered rightmost-parent reconstruction gives one nearest-line loss per short and three per long, with no central reinjection on these black strobes. This is not a bound on interior branching. The western ordinary ancestry and checker ancestry are different parent relations. Unconditional strict loss at each pulse, horizontal continuation of the same donor, and a permanent nonmerger from two adjacent labeled packets all failed.
* There is a sharp warning for any finite-width clock reader: an actual width-84, time-6 periodic R30 orbit admits the alternating center with different phase-labeled right heads. The generic west can also realize alternating readouts without the actual singleton initial west. Right-8 resets, a finite height contrast at a head, or entropy loss in a right projection alone do not eliminate P2. Opposed arrivals at one fixed lag still require physical, not merely XOR, ancestry.

## 3. The 3/5 protection and the actual finite initial cylinder

At a genuine long positive (S), keep the actual strict west and (C_S=0). **Every** replacement of the entire strict east then gives the same strict west for all future times. At a short positive one can start with the same protection if the first east bit is also kept equal to one. This is a statement about the strict west, not a statement that the alternate raw center stays alternating. Between positives the prescribed west head is one; this is why changing the raw center can leave the physical west unaffected. At a positive the old west head is zero and the common next west head forces the alternate center to be zero.

Consequently there is a finite original marked cylinder (U_s): initial (x<0) zero, (x=0) one, (1\le x\le s) zero and **all** sites (x>s) free. Take (s) large enough to reproduce the cone to one protected long cut. Every such initial row then shares the singleton's entire strict west at all subsequent ages, and its earlier west agrees by that same cone choice. Every continuation avoids adjacent black centers in the protected tail. This gives a direct sufficient refutation: one continuation that makes a late 11 defeats this host. No such continuation has been proved for arbitrary (s).

A raw distinction: with (W_1=1), either the alternate center continues to alternate or a white with (R_1=1) produces the locked pair ((C,R_1)=(0,1)), which persists while (W_1=1). A (W_1=0) tick breaks this simple locking rule. Canonical vacuum beyond an east tip does not generally preserve the P2 center. For example the clamped white-to-white east read starting at the bare first east mark has tapes (1,4,18,64,305) and starts with q=10001, not a legal first 3/5 interval. The real alternative may change its raw center while keeping west.

Two sharper entrance statements:

1. Suppose (s_0) is a long positive and (t) lies strictly after the preceding positive, up to and including (s_0). Knowing (W_t) and the true (C_t) suffices to protect the entire subsequent west, with the east free. While (W_1=1) the alternate either keeps the true alternating phase or locks to 0 before (s_0); either way (C_{s_0}=0), giving the known long entrance.
2. At (p+1), immediately **after** a long positive (p), even the center need not be kept. Fix the strict west and allow *every* center/east state. The nine consecutive unit west heads at (p+1,dots,p+9) force ((C,R_1)=(0,1)) at the next positive (p+10). If the center started in the opposite phase and failed to lock, this would require five consecutive zero white reads at (p+1,3,5,7,9) relative to (p). If the phase was correct but the landing had (R_1=0), the five zero white reads would be at offsets (2,4,6,8,10). Both contradict the earlier four-east-site no-five-zero-reads result under an alternating drive (its R30 survivor counts (16,10,8,6,4,0); R90 keeps all sixteen). At a short landing (R_1=1) is exactly the extra required inlet. Thus the strict west alone at this after-long black cut protects forever.

These statements require the true host itinerary for the reference west. They do not make that itinerary realizable from an arbitrary finite west.

## 4. A finite-graph necessary condition stronger than a second full-ray intersection

Fix a genuine protected long age (Q\ge s). Let (P_Q) be the true left-normalized row on indices (0,ldots,Q), including the center at absolute age (Q). In the finite graph of (L_{Q+1}):

[
  L_{Q+1}^{Q}(U_s)=\{P_Q\},\qquad
  \{n:\exists zin U_s, L_{Q+1}^{n}z=P_Q\}=\{Q\}.
]

The first assertion uses the shared strict west and the forced zero center at the positive. For the second, any proposed finite-prefix hit can be extended to a full marked ray. At age (n), it would give a second permanently protecting physical cut centered at (Q-n), in addition to the original one at zero. Their common western area forces the true mature left-normalized phase to agree at chronological offset (Q-n) on every fixed lane. The established unbounded dyadic record periods prohibit a nonzero offset. Do **not** replace this proof by an assumed global recurrence of an arbitrary predecessor.

In particular (P_Q) is transient. All (2^{Q-s}) extensions of the original marked prefix (within this finite graph) have the very same transient length, exactly (Q+\tau(P_Q)>Q). An extension already on a cycle by (Q), two different transient lengths, or one extra hit would suffice. The preceding entrance extension also gives the unique-hit conclusion at the intervening protected cuts; the center-free version uses the strict-west prefix at (p+1). No such obstruction was constructed at an arbitrary protected age. For a *fixed* nonzero temporal offset, sufficiently many low mature marked lanes already distinguish it; a successful growing-width construction must take this into account.

For the general P2 hypothesis, a useful even simpler test is independent of this host: every ultimately white normalized lane (j) beyond onset must be black at (t=j) or (t=j+1). If the former center is white, the latter row is black at the center and therefore at strict west −1. Thus a single ultimately white lane already settled before its own physical crossing refutes P2. Cofinal ultimately white lanes are known; a bound on their actual settling dates that gives this crossing is not.

## 5. Exact arithmetic at a positive

Let (v_e=4W_e+1) include the white center and positive eastern mark, and (y_e=(v_e-1)/8) be the crop with eastern tip at physical −2. It is an odd ordinary integer on the true finite west. For the next positive (u=e+k, k=6) or (10), write
[
 v_e=2^k z+a_g,qquad (a_3,a_5)=(25,345),qquad v_u=A^k z .
]
The local tile equality holds on 2-adic west data as well; finiteness is required for arithmetic height conclusions. In particular (z\equiv1\pmod8) since (A^2) fixes residues modulo 8 and (v_u\equiv1\pmod8).

The signed eraser gives, for each integer iterate (m),
[
 A^m(v_e-1)=2^k A^m(z)+(-1)^m(a_g-1).
]
Consequently (h(v_u)=k+h(v_e-1)). At the next reset the pair produced by evolving (v_e) versus its unit deletion can have identical subsequent strict west despite distinct finite eastern histories. This is not (h(v_e-1)=h(v_e)): the unit deletion is the unresolved arithmetic recoil. Multiple tiles do not concatenate as literal bit crops; in particular the old −15 site is blank in a 5-then-3 case where the naive two-cut substitution requires a mark. Equal total duration (35\leftrightarrow53) does not prove that the swapped predecessor has a finite history to a fixed initial cut. The alternate short predecessor compared with the long advanced four ticks has strict-west low residues (5\leftrightarrow6); the ensuing forced inverses can meet or split again when the positive history changes. Single-site compulsory loss is false.

**Unified checker arithmetic.** The two cap constants are not unrelated numbers: (a_g=(2^k+11)/3). Put (r=k-1) and (b_r=(2^r+1)/3), namely 11 or 171. In the stated 3/5 case,
[
 \nu_2(3y_e-1)=r,qquad y_e=b_r+2^k w,qquad
 A^k y_e=b_r+2^k y_u .
]
Indeed (z=1+8w); these equalities follow by substitution in the tile and signed-eraser identities. The 2-adic checker (1/3) satisfies (A(1/3)=-1/3), (A(-1/3)=1/3). Thus (r) is the first differing low index against a genuine checker orbit. This radius is invariant on even ticks of the free evolution of the same cap. It need not be invariant after the next cap is cropped.

Both delays use a single high-bit map. Define (mathcal B(w)) to be (A^2(w)) with its low two bits decremented modulo four, all higher bits unchanged. Exactly
[
  A^2(8w+1)=8mathcal B(w)+1,qquad
  y_u=mathcal B^{g}(y_e\mathbin{\mathrm{div}}2^{2g}),qquad
  g=(1+\nu_2(3y_e-1))/2 .
]
For the first identity (A(8w+1)=8A(w)+7); the next tick flips the new high section's bit zero and flips its bit one precisely when the original low bit was zero. Since (A^2) fixes the bottom two bits, these operations give exactly the stated decrement. The successor identity also follows from (v_u=A^{2g}(8w+1)). Equivalently (6A^k(y_e)-2=2^k(6y_u+1)). This removes the apparent separate short/long carry from the return map. It does **not** imply that arbitrary successive inverse sections preserve an ordinary finite predecessor, that the low correction commutes with arbitrary further stripping, or that every finite orbit escapes. No nested-height estimate was proved.

For comparison, the known finite right-padding map (D(w)=2w+1) for (w\equiv1\bmod4), and (D(w)=2w-1) for (w\equiv3\bmod4), commutes with free evolution on odd words in the previously established sense. It preserves finite height and the western phase; by itself it cannot bound the unit recoil. At a true long age (Q), (D^{Q-1}(v_Q)) and (A^Q1) can have the same two extreme positions and the same future west, with respective heights at most ((Q+1)/2) and exactly (Q). An eventual *bounded* normalized difference packet between a finite modified row of degree (2Q) and (A^Q1) would instead force equality of heights via the negative dyadic iterates, then force the original primitive to be the one-bit singleton. The discrepancy therefore cannot simply stay a bounded traveling packet.

A further narrow-width obstruction concerns attempting to export the right-end two-bit alias into the interior. At its first damaged right-normalized digit (j), write the next damaged-bit value as (d), and the reference bits at indices (j-1,j,j+1,j+2) as (b,p,s,c). No spill into (j+2,j+3) requires (d=0\Rightarrow s=1), and (d=1\Rightarrow s=1-p, c=1); the two-step constraints give (c'=1-c) and (d'=d\oplus(1-b)). Consecutive (d=0)'s or consecutive (d=1)'s contradict the required unspilled update. This forces (b=0) permanently, hence all lanes east are vacuum under the right-normalized rule. A width-two permanent alias cannot be transplanted to a nonvacuum interior checker cut. This is not a classification of wider damage packets.

## 6. Genuine returns, two-ended surgery, and gardens

In the **uniformly recurrent actual q** branch, fix an old protected long (S) and use later matching q words to reproduce its finite strict-west prefix to width (d>S+G) with a first additional black at (d). First fix that finite cylinder; then successively impose genuine, farther-west inverse resets (010 or 011110) in the appropriate order. This can give arbitrarily many marked reverse ticks with (S,d) fixed. For the isolated surplus (B=W_U\mathbin{\mathrm{div}}2^{d-1}) at a suitable later return (U), the resulting finite heights can be arbitrarily large. Uniform recurrence gives a dyadic phase ball for the chosen finite word by Baire: finitely many translates of the closures of its bounded-gap occurrences cover the dyadic integers. Nested choices can retain any prescribed finite precision before imposing further genuine resets. Bare recurrence alone does not imply that phase ball.

The opposite surgery, later west (W_U) with the old true eastern half at (S), can be rewound the (S) genuine marked ticks on these selected returns. At relative age zero it is the actual singleton plus an extra western donor no farther east than (-d-S). The two pieces cannot interact during the first (S) ticks. Restoring the remote true east gives a modified finite row at actual age (Q=U-S), with both true extreme marks, a fixed central edit, and future strict-west agreement after the protected landing. More directly, at a protected long date one can alter the finite east with the same two extreme marks. No arbitrary finite comparison is being called a second singleton history.

Let (Y_Q) be such a distinct equal-width repair, (h=h(Y_Q)<Q), and (Delta=Q-h) its ordinary right-normalized garden date. If (r_0) is the fixed physical rightmost site changed at date (Q), the rightmost changed lane in the genuine left frame at (Delta) is
[
 e=2Delta-Q+r_0 .
]
The original singleton and the independently reconstructed western donor first come into range at age ((Q-r_0)/2+O(1)). This goes to infinity at fixed (r_0); it is not the same as assuming an old cut is mature at unbounded lane depth. The time available from contact to the garden birth is about (e/2). In particular an argument that excludes only bounded (e) does not exclude the surviving large overlap.

In the bounded-(e) case, for a fixed scar of a true mature marked phase, a parity-matched doubling record erases the distinction between two opposed dyadic phases in the *modified* next lane while the genuine lane changes sign. At most one of the two digits can be compatible with restoration of the genuine phase. Infinitely many such matching records give a Haar-null set of compatible phases, not exclusion of any fixed ordinary phase. In the uniformly recurrent nested-return construction one can choose the parity of the fixed edit and a generic dyadic phase inside its return ball. This forces (e) unbounded there while the nested recovery already forces (h) unbounded; neither one gives a bound comparing their growth.

**Actual birth alternatives.** Measure lanes from the genuine mark at the garden date. The isolated finite donor's leftmost black is at physical (-Delta+ell), its rightmost at (-Delta+e). Just before its first finite-west row it is cofinite on the west. If the old cofinite row's first zero is at (z), the next row's first black is at (z) or (z+1), according to the next bit. Thus the old donor is black through its new left mark minus two. Along the unique extremal characteristic of the added original singleton,
[
 X_Delta(-Delta)
 =Y_Delta(-Delta)\mathbin{\mathrm{xor}}
      \prod_{0\le t<Delta}(1-Y_t(-t-1)),
]
where here (Y_t) denotes the isolated donor and (X_Delta) the combined row. The required combined mark forces **(ell=0) or (1)**. In the latter case every gate on this characteristic was open, and in the former at least one was shut. Odd (e) forces (ell=0): the isolated rightmost donor passes precisely through a gate at first contact. For even (e=2m), the open alternative requires the second rightmost bit of the finite donor at birth to equal (m\bmod2), using the exact toggle of the right-normalized bit one.

The open alternative can be classified before the genuine finite edit constraint is imposed. If (z) is its finite birthday garden and (p=A^{-1}z), then for (e=2m\ge4), (p_0=p_{e-2}=1, p_{e-1}=0, p_j=1) for (j\ge e). The open gates are
[
 [A^{1-r}p]_{e-2r+1}=0,qquad 2\le r\le m.
]
Each inverse iterate is triangular, with coefficient one on its highest input digit. In increasing index order this fixes the odd (p_j)'s from the lower inputs. The remaining even bits select the actual incident lane-zero drive ([A^{1-r}p]_{e-2r}). Every length-(m) word of the form (1u1) is realized: there are exactly (2^{m-2}) isolated open gardens (for (m=1) the separate garden is (z=3)). Thus the incident transient cannot be treated as a single fixed word.

There is still a necessary true-phase restriction. In this open case the combined lanes satisfy (X_0=1-Y_0), (X_1=1), (X'_2=Y_0), (X'_3=\neg(X_2\lor X_3)), in left-normalized notation. (Y_0(Delta-1)=1) then (Y_0=0) from (Delta) onward. Hence (X_3(Delta+1)=0) and it subsequently toggles. Matching the genuine lane-three phase requires **(Delta) odd**. This alone does not remove the closed-gate alternative. For the narrow (e=1) alternative, the low-depth necessary conditions instead give (Delta) even and then (Delta\equiv2\pmod4) from the lane-eight phase. No all-depth exclusion follows.

There is a physical test on the chosen cut edit. For (Q-r_0=2n), the open first gate requires
[
 D_Q(r_0-1)=\bigoplus_{t=n}^{Q-1}\neg X_t(t-2n+1),
]
using the actual true right-moving subleading discrepancy recurrence. Changing the second cut edit can exclude the open case for one of two choices; this does not force the closed case to fail.

## 7. Additional transfer tests, corrections and remaining gap

* In a fixed-old full-west return, the immersed past may be cofinite on the west before a finite landing. The true eight-bit left rim does rule out a cofinite immediate predecessor of an *exact genuine entire* (W_b) for (b\ge7); it does not rule out an earlier cofinite birth after two finite precursors have separated. Some actual orbit-closure alternatives give such a birth at a fixed (0\le k<S). The backward periodic sectors and the actual two-ended surgery give different information and must not be identified.
* A finite-right/cofinite-left example demonstrates why simply excluding the competing tail type is invalid. For (K>s+4), take old black sets (\{0\}\cup[K,\infty)) and ((( -\infty,K-3]\setminus\{-1,0\})\cup\{K-1\}). After one R30 tick both give the same finite black set (\{-1,0,1,K-1,K\}). A finite future does not specify the old west sector if the right boundary was not fixed.
* The exchange (35\leftrightarrow53) cannot use an arbitrary counterfactual inlet as if it had the actual finite past. At a first physical west-head fork the true subleading characteristic defines an actual cap parity (the earlier (H(f))); it is not an independently adjustable bit once two surplus-west bits on an old/new return are fixed. At the nearest possible equal-mark rewind a (0\bmod4) fork date is excluded, and the other residues require the proper parity (H(f)=0). There is no proof that an admissible opposite parity occurs cofinally at a swappable cut.
* Closely related obstructions from the companion analysis are worth distinguishing: unbounded pure-five runs give long *true* checker-independent inverse-reset collars via the spatial-155 reference, hence unbounded crop height, not an escape theorem. A bounded-height branch must bound successive fives. Long bands of input-output agreement, noncoalescence of two marked parities, and existence of a dyadic subsequence do not supply a bound uniform in the physical age. Nor is the source-current parity for a real cap fixed just by the gap length.
* The straight-echo test is legitimate but unresolved. If an initial (U_s) extension leaves a sufficiently long all-white left-moving normalized lane, flipping its eastern neighbor gives a real signal into the protected west. With a right-normalized right mark (y_0=1), the path conditions ([A^t y]_{2t+1}=0) are systematic: the even old bits are free and each odd old bit is forced triangularly. In particular (y_1=0,y_3=y_2,y_5=y_2y_4). This leaves the separate problem of fitting the actual (10^s) left mark with its vacuum behind it. An old permanent-white lane at fixed depth (e.g. the singleton's depth 7) supplies examples for short prefixes, not all (s).
* A pure truncation of an (n)-step preimage of an isolated singleton cannot realize an arbitrarily long preceding vacuum buffer for that straight line: any old black followed east by (2n) whites forces a new black (n) sites east at age (n), irrespective of its old west. A weaker, potentially effective criterion uses a periodic ancestor of the zero row: if the ancestor has a mark with at least (s) following whites and the previous black is at distance (D\ge H+3), where (H) is its vacuum time beyond onset, truncate the old row to the right half starting at that mark. The removed left part has a rightmost discrepancy traveling east at speed one, so the actual truncation at (H) has rightmost black (H-D\le-3), contradicting the true 3/5 west-head pair. The universal upper bound on zero-run length in such a nonzero periodic vacuum ancestor is (2H-1); no family meeting the required lower bound was established.
* For a pair of finite caps of unequal ordinary height, negative iterates and finite-prefix periodicity can force arbitrarily many consecutive discrepancies above any **fixed** normalized width, at dates in a dyadic progression. The width witnessed this way need not grow as fast as the date. It does not force passage through the center.
* Intermediate rate, trace-language, carrier and echo statements cannot be promoted from a theoretical right-arm host to a singleton result without the actual finite initialized west; likewise protection of the strict west alone cannot be promoted to simultaneous periodicity of raw (C,R_1) for all alternate arms. All statements here use nonlinear R30 gates; where a previously computed four-site falsifier is invoked, the actual R90 control is as stated. No new empirical sweep or Lean acceptance is claimed for this archive.

**Remaining proof step.** Even in 58203 it has not been shown that the authentic finite west cannot sustain the infinite 3/5 return. The checker-shell recurrence admits arbitrary 2-adic decoding; it needs a proof excluding ordinary finite marked input with the true initialized arms. The alternative protected-cube route needs one actual violation of its finite-graph unique hitting or of its permanent west agreement, for arbitrary prefix length. The surgery route still admits large-overlap, unbounded-height gardens and a closed incoming gate. For unrestricted P2, the other admissible hosts also remain. The shared Step 4 proof gap is unchanged.
