# The finite-parent link in the mixed-center contradiction

Use physical ticks. Set the origin of time at a positive-age cut of the
singleton, after the proposed periodic onset and after the actual path enters
one recurrent finite right host. Include clock phase in its vertices. The host
must describe genuine Rule 30 right-prefix transitions; distinct successors
with the same masked observation do not count as distinct readings.

**Chain.** Eventual center period implies a marked path in such a host,
with periodic center c and nonperiodic masked right read q (otherwise the
two-column theorem gives False). Its strict-west tape W at the cut is a
nonzero ordinary integer. The prescribed old head on an edge is
h(t)=c(t+1) XOR (c(t) OR q(t)). Given c and W the forward tape and h are
determined. Hence the west integer decoded from each prefix of n physical
ticks of this path is W mod 2^n. In particular the minimum over all admitted
prefixes cannot diverge for this host. Conversely, bounded ordinary minima
give an actual infinite finite-west/host path by nested cylinders. This
converse is for the stated finite host, not for an independently evolving
infinite eastern ray.

**The hereditary implication that would finish the chain.** Suppose such a
nonperiodic marked host path exists, with initial width d. It suffices to
derive the following fork: some landing at n>j>=d admits another physical
host path ending at the same vertex at n, with the same centers and old
heads before j, different head at j, and whose outward inverse scan from
the *same entire* W_n yields a finite marked tape at the cut 0. Requiring
this conclusion only for the actual singleton path is already sufficient
for the original contradiction. Requiring it for every finite-west/host
path would prove divergence of the corresponding host minima.

Here is the exact sign and width obstruction confronting this implication.
For target bit y, the old pair scans by
(a,b) -> (b,y XOR (a OR b)), starting with old center and old head.
After the last black target bit, 00 stays 00 and every other pair
eventually reaches 11. Thus at any one inverse step the old tape is
finite exactly when the pair entering this final zero ray is 00.
For any nonzero finite old tape the width grows by exactly one on
each forward step, regardless of the clamped center. Thus a nonzero
finite inverse at 0 of the landing W_n must have width exactly d.
For each tau<=j, equality of all earlier heads from tau until j means
that the first differing tape bit between the two histories at tau
is precisely index j-tau (zero-based at x=-1). This follows since
one step with common c advances the lowest differing index i>0 to
i-1: the other two contributing inputs at the first such site agree.
If both tapes at tau are finite and nonzero and have the common
landing W_n, both have width d+tau and their top bits agree (=1).
Consequently j-tau <= d+tau-2. In particular for every integer tau
with 2*tau < j-d+2 the alternative tape cannot be finite and nonzero.
A zero tape there would have width at n at most n-tau, below d+n,
so it is impossible too. This proves the contradiction once the
finite-marked fork exists. It also pins down why an inverse corridor
certified near n cannot be used at the old cut without a new argument.

There is a second way to express the same hereditary hurdle. Let D_t be
the minimum positive width of a finite marked host ancestor of the actual
landing (v_t,W_t), allowing the empty history. Every witness remains an
ancestor one tick later, so D_t is positive, nonincreasing and hence
eventually constant, say D. After that the finite set of (vertex,tape)
ancestors of width D increases by inclusion and eventually stabilizes.
Their start phase is fixed by the width difference, and each such tape
determines its whole masked future under the clock. This does not say an
arbitrary alternate incoming host edge preserves finite parenthood.
A finite-width nonzero garden can have no admissible previous edge.
Even a one-step universal rim reset guarantees the finiteness of one
inverse only; it does not assert it again for the new tape.

The marked fork above is the unresolved implication. The right8 proof
supplies cofinal eastern resets in the remaining Lean branch, but a
reset determines an old pair for the common observed row; it does not
make an entire alternative past finite back through tau=0. No entropy
inequality or finite-horizon lower bound discharges this step.

**Why an age-independent finite collar cannot provide that fork.**
Fix M,n,r in advance. Take an admitted physical host path of length M+n
and periodic c. Decode its initial near-west residue z modulo 2^(M+n).
Put exactly this residue near the wall and put a single additional black at
an arbitrarily larger depth D. Choose the intervening vacuum longer than
r+2(M+n). The whole west is finite. Its forward Rule 30 evolution, with
the prescribed wall, now realizes the same M+n heads. At the cut after M
ticks, it has M ticks of finite host ancestry, n ticks of host future, and
its outer r cells over this entire interval have followed the actual
normalized isolated-mark rule (the domains of dependence do not meet the
near-wall edit). If the chosen right path came from a genuine clamped
infinite east, use precisely that initial eastern ray: the computed heads
then produce the prescribed center in the full CA without clamping for
the entire interval. The starting complete row need not be a singleton.
Thus no finite M,n,r makes these hypotheses inconsistent; the spatial
separation D is free. Any hereditary lemma using the actual single origin
must relate the inverse depth to that separation, or use an unbounded
right-history condition. This is a symbolic gluing construction, not an
infinite finite-west survivor.

Nor does the eventual normalized mark exclude a loss of finite parenthood
in the remote past. Directly, Rule 30 maps the half-space x<0 to the single
black at x=0: all interior triples give zero and the triple at zero is
100. It also maps the all-black row with its one hole at x=-1 to this
same singleton. Their old (center,west-head) pairs are respectively
(0,1) and (1,0), and both old west rays are cofinite. Thus a cofinite
parent can land in the exact marked source, with its entire ensuing rim.
The missing implication must involve the prescribed host/read history
or the exact joint source rather than a ban on this sign transition.

**Genuine lag surgery test.** Compare two true ages at a common periodic
phase. Until the first unequal old west head at j they have the same
masked read. Cross-swapping their complete western and eastern halves at
the starting cut therefore preserves the true center through j, by
induction. At j the center is white and the two strict-east heads differ.
Both crossed full rows give the complement of the true center at j+1:
their update is the old west head of one donor XOR the opposite east bit.
Thus this swap between two genuine finite rows does not produce the
fixed-wall fork required above. If the donor with the *zero* east head
at j has a black at x=2, both original strict-east heads at j+1 are 1
and the two crossed centers rejoin the true center at j+2. Indeed
the west and east neighbor rows at j+1 are still their respective
donors, so the common saturated OR ignores the center flip. The
one-tick flip at j+1 remains.

**A fork that is forced by the actual orbit.** Write the periodic clock
phase and q as one finite symbol; let V be ANY additional finite color
of each genuine cut, including a prescribed east collar. The two-sided
limit set of the true tail has two histories with the same entire
nonnegative symbol sequence and the same color at zero, but different
symbol histories at negative times. No recurrence assumption on the
original old cut is necessary.

To prove this, project the compact limit set of (symbols,colors) onto
the two-sided symbol limit set X. If X contains a periodic point of
period l, take arbitrarily long matching periodic blocks in the real
non-eventually-periodic sequence. Extend them to the left up to their
first mismatch. The mismatch positions must be unbounded, since a
bounded family of starts could give arbitrarily long such blocks only
on an eventually periodic tail. Pass to a fixed period phase and take
a limit. Its nonnegative half is periodic but its symbol at -1 differs
from the periodic extension. Its forward shifts by multiples of l have
infinitely many distinct pasts (their last mismatch is at different
positions) and the same future. Infinitely many admit one common
color at the cut.

If X has no periodic point, take a minimal subsystem Y. Two distinct
histories in Y have the same nonnegative half. Otherwise compactness
makes the previous symbol a function of a fixed finite future block;
the finite block graph then has exactly one predecessor and at least
one successor per vertex, so all its components are cycles. This
would make Y periodic. For each color v, the histories in Y that
admit a lift with that color now form a closed set; these sets cover
Y. One contains a relative open cylinder U. Translate the two
right-asymptotic histories forward until both belong to U: every
positive orbit in Y meets U arbitrarily late, and finite cylinders
then see precisely their common future. These translated histories
still differ in the past, share the full future, and both admit v.

Since phase is part of the symbols, every discrepancy is in q, not
in the clock. Genuine spacetime subsequential limits realize the
two histories, using compactness again. Their strict western landing
rays are identical because their forward heads agree forever.
The color can include the last k observed ticks for any specified k;
their rejoined true-limit western history then includes those k past
ticks by uniqueness of the outward scanner with the old pair given.
This provides a same-host and same-west fork in the actual limit set,
rather than a freely invented host past. It does not certify either
western tape at the earlier cut as finite. The physical marks may
move to minus infinity along both sequences of genuine ages.

**Retaining the whole marked phase, not a finite sample of its lanes.**
Record the genuine age t also as an element of the compact additive group
G of dyadic integers. Under a tick this coordinate translates by 1.
For every fixed normalized western lane, the true marked-left subsystem
is eventually periodic with a power-of-two period (the known finite-lane
result). Thus a limiting phase g specifies the *entire* limiting
normalized marked front, at every fixed normalized lane and every signed
finite time offset. The forks above can have exactly the same g.

In the aperiodic-minimal case take a minimal joining J inside the actual
limit set projected to Y times G. It projects onto Y. Each vertical
translate J+b is minimal for the same transformation, so it is either
disjoint from J or equal to J. Put H={b:J+b=J}, a closed subgroup. The
fiber over any x in Y is one H-coset: subtract two points of the fiber
to find an intersecting translate; the reverse inclusion follows from
H-invariance. The resulting coset map Y -> G/H is continuous by
compactness (its graph is the projected compact joining) and commutes
with translation by 1. For right-asymptotic different-past x,y in Y,
the distances between their positive translates in Y tend to zero.
The quotient rotation preserves distance, so their cosets are equal.
Lift both with the *same* g. These lifts in J are right-asymptotic.
The closed sheets of J admitting each additional finite color still
cover J; a sheet contains a relative open cylinder and a common
sufficiently late forward translate puts both lifts inside. This
preserves equality of the entire phase, the common symbol future,
and the difference somewhere in their past.

In the periodic-future case lift the last-mismatch history to the actual
joint limit including the full marked phase and all finite colors at all
times. Along shifts by n*l, n>=0, the symbol future stays periodic.
Color these integers n by their actual shifted finite color. The sets of
dyadic limit points of the color classes along n tending to infinity
are closed and cover G: every dyadic residue has arbitrarily late integer
representatives. One color's limit set contains a dyadic residue ball.
Choose a member n0 of this color inside the ball, and arbitrarily late
members n_i of the same color converging dyadically to n0. A convergent
subsequence of the shifted full histories has the completely periodic
two-sided symbols, while the shift by n0*l has its last mismatch a
fixed distance in the past. Their current colors and their phases
g+n0*l coincide. This also gives the desired fork.

These are genuine limits of the one singleton orbit, sharing its
complete normalized marked source phase as well as the entire physical
strict-west landing. The distance in cells between the source frame
and the physical wall still tends to infinity. Equality of these two
limits is not uniform in the intervening, growing spatial depth.

The same age phase also fixes every true normalized *eastern* lane.
In the frame j=t-x the update is E'_j=E_j XOR (E_(j-1) OR E_(j-2))
with vacuum for j<0. Each lower-prefix period from time zero is dyadic:
over one period the next coordinate toggles by one fixed parity.
Consequently the forks above agree at both normalized source edges to
all fixed depths. This does not identify the physical eastern ray at
the center, since its normalized depth is the moving age t rather
than a fixed j.

**Fixed lag before moving the observation late.** In the minimal case
choose at the outset a minimal subsystem of the *full* actual joint
limit above Y, including the finite color. Take J as its projection
to (symbols,phase), and use this same full subsystem to form the
closed color sheets. The two selected lifts then belong to one
minimal full subsystem. For each finite matching window of length r
and phase precision 2^r, choose finite cylinder neighborhoods of the
two lifts prescribing these data, their common color, and the symbols
back through the fixed last discrepancy at -k. One forward orbit in
this minimal system visits the first neighborhood and then the second,
with one fixed positive lag Q_r divisible by 2^r and aligned in the
clock; increase the separation if necessary. The resulting one finite
block is in the actual omega-limit language, so it occurs at
arbitrarily late genuine ages with that SAME lag. In the
periodic-future case choose instead a sufficiently late n_i for the
same finite windows and phase precision in the pinned-shift construction;
the two neighborhoods are again realized by one finite block of a
genuine limit history. This lets the observation age tend to infinity
*after* fixing Q_r, so every marked lane of depth prescribed as a
function of Q_r is mature. There is no bound here of Q_r by r, nor
uniform agreement across a growing source-to-center interval.

**Finite support is not obtained by Baire.** In the periodic-point
construction the common west landing cannot itself be finite. The
periodic center and masked future give periodic temporal words in
every western column from one and the same cutoff by the outward
recurrence. A finite nonzero west grows in width at every step; a
zero west also becomes nonzero under a mixed self-consistent future.
So no finite west at any earlier clocked time can map to this landing.
In an infinite minimal symbol component the histories with a finite
physical west at *any* signed time form a meager set: at each named
time there are countably many finite tapes, and a fixed tape and
clock phase determine at most one entire future of symbols. Any one
such exact-future fiber is closed with empty relative interior:
otherwise a point in a cylinder contained in the fiber returns to the
cylinder in positive time by minimality, making its future periodic
and the entire minimal system periodic. Take the countable union
over tapes and times. Thus matching all dyadic source lanes cannot
by itself license replacing a limiting west by a finite tape.

**A compulsory black block on the genuine later orbit (finite-cut transfer).**
Fix an actual cut s with strict-west tape of finite positive width d. Suppose
at u the same clock phase and the next r>=d heads agree with those at s.
The previous d+P+1 ticks at u must also be inside the mixed period-P wall.
There exists b in [1,d+P+1] for which the genuine strict-west row at u-b
has at least r-d consecutive black bits, beginning at inner-to-outer bit
index at most d+1 (physical distance at most d+2). This conclusion uses
no return of the complete physical or normalized row.

Start with the *exact* finite tape at s, not a limit. Rewind it by the old
centers and heads supplied by the genuine later history at u. After b such
steps its reconstructed tape agrees with the true one at u-b on the first
r+b bits: at the first step the supplied head gives bit 0 and r common
output bits give old bits 1 through r by the scanner. Iterate. Until the
first nonfinite rewind, each nonzero finite parent drops one bit in width.
An old zero remains zero at the next tick only with old center zero;
with center one its next tape has width one, and all subsequent widths
increase by one. Thus at most d+P+1 backward steps can precede the first
nonfinite tape. At that first step let w be the width of the finite target,
allowing w=0. After scanning its last black, the input is all zeros and
the nonzero pair enters 11 within two transitions (10 -> 01 -> 11).
Therefore every reconstructed old bit of index at least w+1 is black.
The genuine row at u-b inherits this assertion through bit r+b-1. While
w>0 we have w=d-b+1, giving length at least r+2b-d-2; for w=0 the length
is at least r+b-1. Both imply the stated bound. At true age s>=8 the
known universal mark reset excludes b=1; the maximum starting physical
distance then improves to d+1. In particular a fixed genuine cut which
returns to arbitrary precision on the periodic tail forces arbitrarily
long solid-black intervals on genuine earlier rows with their near ends
in a *fixed* spatial window. Choosing a subsequence fixes b and the start
index. No fixed-cut arbitrary-precision recurrence has been assumed for
an arbitrary nonperiodic q, and the lag-dependent late cuts of the fork
theorem do not supply it.

The inverse tails farther back also have a genuine finite-window implication.
After leaving the vacuum class the first tail is all black, its predecessor
has spatial primitive period three, and every subsequent primitive period
is the old value or its double (the spatial preimage theorem). These
periods diverge on every infinite such past: otherwise the periodic far
fields would belong to a finite deterministic forward system, and an
arbitrarily long transient ending at vacuum cannot visit a state twice.
More quantitatively, a spatially periodic far field first entering vacuum
k ticks later with current primitive period m must have k+1<=2^m,
by considering those distinct aligned states on the m-site circle. For
any *fixed* rewind length k and fixed original d the finite set of possible
old heads has a finite maximum spatial transient and period. Hence if r
tends to infinity at a fixed s, genuine earlier rows contain arbitrarily
long blocks of the prescribed periodic ancestor tails; subsequences fix
the prior heads. No uniform bound on the spatial transients as k grows
is asserted. The unsolved estimate remains an incompatibility for these
blocks on the marked approximants, or an argument furnishing a sufficiently
long recurrence relative to the varying genuine cut.

The first cofinite depth b can enter the *existing* quantitative marked
spatial-patch theorem, not just a single-bit endpoint ceiling. For singleton
d=s set Q=u-s, D=u-r. At physical age u-b, a strict-west bit i has normalized
left depth j=u-b-i-1. Thus the forced solid-black block includes the whole
nonempty interval [max(0,D-2b), Q-3] when w>0. When w=0 the upper endpoint
is u-b-2, still >=Q-P-3. If the untruncated lower endpoint is negative,
the protrusion into vacuum itself is impossible. Apply the period-one
spatial-patch estimate in RUN_RESULT.md to this genuine row at u-b: an
interval [a,e] of black cells cannot occur if k=ceil(a/2), K=4^k,
u-b>=k+K+20 and e>=3(K+5)^2. Since u-b>=e here, this bounds Q-P-3 by
O(4^max(0,D-2b)) in the large-Q regime, or equivalently strengthens the
return deficit to D>=2b+(1/2)log2(Q-P-3)-O(1). The exact interval
statement is the useful one when constants or boundary cases matter.
The gain 2b is allowed even when most of the older heads differ: b measures
actual finite inverse survival, not the length of an identical past word.

**Why the east restriction is necessary at halfway.** Fix a landing of
positive width w, k<w, and all k earlier center bits. Distinct possible
k-bit head words give distinct old tapes, by deterministic forward
replay. Any finite one has width exactly w-k, so there are at most
2^(w-k-1) finite choices among the 2^k words. In particular once
2k>w-1, an assertion of finiteness for every old head word is impossible
for *every* such landing, including every actual marked landing. The fraction
is at most 2^(w-2k-1). Prescribing a common length-m initial head segment
also fixes the lowest m ancestor bits by triangularity; while m<=w-k-1 it
divides both counts by 2^m. The obstruction threshold from the first fork
cannot be crossed by adding an all-head collar theorem. What is required
is an additional *legal eastern* history inside the sparse finite-parent
fiber, on top of the one true history already known.

**The first nonfinite rewind separates actual physical founders.** Compare
true ages s and u=s+Q inside the same period. Suppose the masked reads
differ at s-1, agree the next r ticks starting at s, then differ at s+r;
use s as the time coordinate of the older copy. Let b be the first
nonfinite inverse of its W_s using the newer copy's preceding centers and
heads. At s-j for each 1<=j<b with s-j>=max(1,T), the two finite donors
(the true older W and the synthetic rewind) both have width s-j, while
the true newer donor agrees with the synthetic on its first r+j bits.
In particular, whenever r+j>=s-j, both actual copies are black at the
older mark of physical depth s-j and are white throughout the trench of
physical depths s-j+1,...,r+j, wherever that interval is nonempty.

For r>=s, use the ordered genuine discrepancy pedigree (TRUE_LAG_CHAIN):
the dying head at s-1 has a discrepancy ancestor at s-j at depth at most
j. It must be on the inside of the common mark, thus has depth at most
min(j,s-j-1). Every western discrepancy after the gap descends from the
outside: at s the first r depths are clear, and moving a discrepancy at
most one cell per tick cannot overtake the older mark to the west. An
inside ancestor of depth <s-j can never reach depth >=r+1 at s. Hence
every such surviving ancestor at s-j has depth at least r+j+1. The black
slab one tick before the earliest positive finite island has no children
in its strict interior, since the two old triples there are uniform black
versus uniform white. If the dying and surviving heads descend from one
stabilized western founder, their common ancestor must be no later than
s-j-ceil((r+j+1-min(j,s-j-1))/2). This improves the elementary bound
at the terminal head itself by the finite rewind corridor. The two
sources at s-j are strictly ordered, irrespective of stabilization.

There is a genuine extension below r=s. Put e=s-r>0, and let H(e) be
the maximum transient of the finite left-mark-normalized Rule 30 map on
lanes 0,...,e-1 with lane zero marked. If some integer j satisfies

    1<=j<=s-T,   2j>=e,   j+H(e)<=min(b-1,s-e),

then the two finite donors at s-j necessarily agree on those e rim
lanes: at s-j-H(e) they each had positive width at least e, so at s-j
each e-prefix is cyclic. Both prefixes evolve to the identical original
W_s in j steps, and a finite map is injective on its cyclic core. Since
r+j>=s-j, the actual later orbit shares this entire rim collar and the
trench at s-j. Every inside discrepancy now has normalized older lane
at least e. This coordinate cannot decrease along any physical temporal
parent/child line: the older mark advances west exactly one cell per
tick, while the child moves at most one cell west. But the next head
mismatch at s+r has as its ancestor at s precisely the discrepancy of
physical depth r+1, normalized lane e-1. Indeed it is the first differing
west bit at s by the exact r common and next unequal heads, and propagates
at full speed to the head with the west summand the sole active parent.
Consequently even in this r<s case its ancestor at s-j is OUTSIDE the
older mark, at depth >=r+j+1. In fact its depth is exactly r+j+1: only
r+j steps remain to the physical head, so the entire segment consists of
eastward unit steps with equal old OR outputs in the two copies (individual
input bits need not agree). The previous head's
ancestor at that cut is still at depth <=j and inside, so this is an actual
strict founder drop.
The cyclic-core condition is on a genuine finite approximant, not on a
limiting row on which the mark might have escaped. The remaining gap is
to force such separations back to one fixed cutoff on a fixed lag, or to
bound the supply of the outside founders with their legal east histories.
Fixed-length repeats at arbitrarily late ages do neither.

**Exact supply from the newer marked boundary.** Use the normalized spatial
coordinate i=x+t+Q, so the newer true mark is lane 0. Write D_i(t) for the
lag discrepancy there, and label the individuals at a fixed cutoff S by
their ordered spatial positions. Every physical parent/child edge moves
normalized lane by 0, 1, or 2. Remaining at lane i>0 means the child took
the easternmost possible old spatial parent: the west XOR term must have
vanished, and the westernmost differing member of the old OR must be the
east member. Consequently D_(i-2)=D_(i-1)=0 on that tick. For i=1 this
contradicts D_0=1. For i>=2, i-1 consecutive such ticks are impossible.
Indeed two adjacent all-zero lag columns through n consecutive times give
the column immediately west zero through n-1 of those times, by the
normalized update B'_k=B_(k-2) XOR (B_(k-1) OR B_k). Iteration would give
D_0=0. This works also in the overlap of the two source cones; it does not
assume the older copy is blank at i-2 or i-1.

Thus a lineage starting at any positive lane can remain in lanes 1..J
for at most J+(J-2)(J-1)/2 elapsed edges (J>=2 suffices). After more
time than this, every true D in 0..J has the single newer mark as its
founder at S. This time bound is uniform in Q and in the initial ages;
in particular no second stable founder at any fixed western normalized
lane can refute the trench. At s-j the trench's outside ancestry belt
has newer normalized depth at most J=u-r-2j-1. Therefore, if that cut
is later than the displayed extinction bound from S, the next physical
head has the outermost newer mark at S as its actual temporal founder.
The ordered western heads then cannot later recover an intervening more
easterly founder while the actual center never differs. This identifies
the source exactly but does not bound repetitions by siblings of the
same surviving mark. Neither does the square-root-width basin by itself
reach the physically fixed wall, whose normalized lane grows linearly.

Genuine symbolic Rule 90 control: take any odd Q in its single-seed
orbit. Each raw row is white at every odd normalized lane. In the newer
frame lane Q is therefore always the older mark alone, with D_Q=1 there
and zero at lane Q-2 (negative older coordinate, odd newer coordinate).
The Rule 90 update at lane Q takes the preceding same-lane discrepancy
at every tick. This second founder stays at fixed lane Q forever, directly
violating the Rule 30 attraction conclusion. The middle input in the
Rule 30 OR gate is necessary for the adjacent zero-pair reconstruction.

**Fixed-lag ceiling for this particular founder test.** At fixed Q the
true normalized rim of the smaller age cannot reappear at offset Q in
the larger age on unbounded widths at arbitrarily late cuts. Otherwise
subsequence compactness at the older marked edge gives an entire marked
normalized front F with F(0,n)=F(Q,n+Q) for all n>=0. Unnormalize the
Q rows on the eastern ray. This equation lets them repeat as a lawful
temporal Q-cylinder, away from its left boundary. Adjacent physical
Q-bit columns determine the preceding column by Rule 30's west
permutivity. The entire eastern ray supplies arbitrarily long inverses
under this finite column-pair map, hence each pair is on a cycle. The
original marked front would have a spatially periodic eastern tail in
one phase, which the marked-front theorem forbids. In particular the
below-width test cannot be obtained cofinally for fixed Q just by
waiting longer: when e grows, its conclusion already yields these
impossible embedded matches. The still-needed implication is that the
actual periodic center (in particular Q=P), together with its coupled
physical pedigree and eastern past, forces such growing widths or an
equivalent loss of the persistent founder. No recurrence of clipped
physical observations establishes that implication.
