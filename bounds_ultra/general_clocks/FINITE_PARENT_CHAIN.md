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

**The fixed-Q head-supplying path.** For Q=P (or any fixed positive
multiple), the true west has infinitely many mismatch heads: otherwise the
masked read would eventually have period Q. At each fixed cutoff S>=T,
let p(S) be the stabilized founder of its rightmost western discrepancy
in sufficiently late rows. Taking a single sufficiently late head for
cutoffs S and S+1 simultaneously shows p(S) is the temporal parent of
p(S+1). Thus these founders form one genuine infinite western path. It
either follows the outermost newer mark at every cutoff, or at some S0
it occupies a positive newer normalized lane and can never return to 0.
In the latter case every sufficiently late head has a nonmark founder at
S0. At a late cut s, if the next r heads agree and the next differs, the
rightmost western D at s, of depth r+1, supplies the head at s+r at full
speed. Its newer normalized lane is J=s+Q-r-1. Therefore outside the
mark-backbone case the quantitative mark-basin result requires

    s-S0 <= J+(J-2)(J-1)/2   (for J>=2)

at every sufficiently late s; bounded J=0,1 are already excluded by the
same basin. This gives a square-root lower bound on the return deficit
in that branch with no cofinite-rewind or embedded-rim hypothesis. In
the mark-backbone case the head-supplying launch ages tend to infinity:
for every fixed S, all sufficiently late heads descend from the specific
outer mark at S. Different generations of that true mark can supply
different head bursts. No periodicity of their arrival times follows.

**Real three-row source gate.** At lag P>=2 write A,B,C for the genuine
rows of ages t,t+P,t+2P. In the newest normalized coordinates BC and AC
have identical local pedigree upstream of the B mark, since both older
rows are vacuum there. Lanes P,P+1 of B are both black after maturity,
while A is still vacuum at both. Hence the AC and BC discrepancies are
complements on two consecutive whole lanes. A material edge increments
lane by at most two. No one chronological path from the C mark can pass
that doublet in both pedigrees. Traffic across it is partitioned: for
k=P or P+1, if the old C bit at k-2 is black, it differs in both pairs.
The next discrepancy at k exists in exactly one pair, and in that pair
its active parent is k-2. AC receives this child when the old C bits at
k-1 and k have OR zero; BC receives it when their OR is one.

There is a single birth-parity restriction for every P>=2. For Q=P>=4,
lane 2 of the newer comparison is permanently clear, and positive lane
1 comes freshly from the mark. Every family leaving the first two lanes
must take 1->3 exactly when the actual newer lane 3 is zero. Its last
mark time n (in the older comparison clock) therefore has n+Q odd. At
Q=3 the middle mark reverses this condition, and n is odd. At Q=2 the
two actual eight-bit rim phases give D_5=0; D_4 is always from D_2 and
D_2 from the mark, and 4->6 passes exactly at odd t, again n odd. This
tracks actual source generations, not the parity of a later head.

For P=3 the newborn C bud must pass newest lane 2 by its single 1->3
edge. The two comparisons select opposite raw phases on that edge, so
one such bud cannot enter the interior in both. This disjointness of
families does not generalize: for P=5 choose the genuine even C rim
phase 0x13. Its lane 4 is black, lanes 3,5,6 are white, and both older
copies are vacuum at lane 4. The common lane-4 individual has a staying
lane-4 child and a direct lane-6 child in AC. At the next phase 0x7b
the SAME staying child sends a direct lane-6 child into BC, since now
C_5 OR C_6=1. One real family supplies both sides one tick apart.
No XOR of parent labels or global head-routing claim is used.

There is nevertheless a source-to-wall ordering consequence. At an
actual newest-outlier western head at time v (A=B differ from C), assume
the AC and BC parent paths each come from the newest C mark. Let n_AC
and n_BC be their last mark times in the common oldest-row clock, both
after the periodic onset T (as holds for late heads in the mark-spine
case for both lags). Trace
their common terminal path backward to its first parent split, at target
(tau,x). The target has newest normalized index i>=P+2: the local gates
coincide strictly upstream of P and a newest outlier cannot occupy lanes
P,P+1. Thus max(n_AC,n_BC)+ceil((P+2)/2)<=tau. The split has exactly
two possible mechanisms. If the old A and B west inputs differ, their
OR outputs must differ too since their new values agree; this is an AB
cancellation, with one of AC/BC taking the west input and the other an
OR input. Otherwise both pairs can split only if all three old west bits
agree, the two old C OR inputs are 00, and both older ORs are 1 with
different westernmost black inputs. If both older ORs were 0, or both
pairs took the west input, the parents would be the same.

In either mechanism there is a genuine AB west-head mismatch at some
t in [tau-1,v-1]. Otherwise all AB heads agree on [tau-1,v], so their
strict-west agreement at tau-1 includes v-tau+2 sites by triangularity.
Every old gate input at this split lies in that prefix or at the common
center: its child (tau,x) can get to the head in v-tau unit-radius steps.
Equal old A,B data cannot split these parents. In particular

    max(n_AC,n_BC)+ceil(P/2) <= t < v.

In this statement birth dates belong to actual material paths, and the
intervening AB event belongs to a third true lag comparison. Nothing
yet says the AB head inherits the same founder as either path.

**An eventually periodic physical material path is impossible.** Work at
fixed Q=P and after periodic onset. Let p(t)<0 be any infinite physical
parent path in the actual lag diagram. Suppose its position is eventually
K-periodic for some K>0, with no relation between K and P. Set
g(t)=t-p(t); its increments are 0,1,2. A visited g has observation
D_P(t,p(t))=1. An omitted g is g(t)+1 at a westward move p(t+1)=p(t)-1.
At this move the eastern input p(t) was selected in the differing OR:
the middle input p(t)-1 is common, and must be WHITE for its OR to differ.
Thus the missing ray carries the observation D_P(t,p(t)-1)=0. Choose
the first visit for a repeated ray; after a finite prefix these choices
commute with (t,g)->(t+K,g+K). Every sufficiently large g now has an
observation at (g-d,-d) of value z_g. Both d and z are K-periodic in g,
and d is positive and bounded.

Writing h_t=X_t(-1), the west inverse triangle gives
X_t(-d)=h_(t+d-1) XOR F_d of strictly earlier heads and the prescribed
center (for d=1 the residual is zero). Indeed the new extremal head comes
only from X_(t+1)(-d+1) in the inverse update; neither old OR input
reaches it. Subtracting this identity at t and t+P, the lag observation
on ray g determines h_(g+P-1) from a bounded window of earlier h,
the given centers, and d,z. Hence h obeys a deterministic finite-memory
recurrence with periodic coefficients; h is eventually periodic. This
contradicts the checked two-column consequence for the true marked west.
The covered path need not be the extremal founder for this exclusion. In
particular every bounded head-supplying spine has a genuinely aperiodic
position sequence. The selection of its actual next step from earlier
heads alone, or the impossibility of such an aperiodic spine, remains open.

The aperiodic geometry alternative is real for the west-only relaxation,
even with genuine same-history comparison and extremal founder selection.
Clamp center identically white; fix P>=3. Set h_(kP+j) to k mod 2 on
every phase j != i, for i=P-1; at i use a non-eventually-periodic
binary sequence a_k with no adjacent ones. Thus d_t=h_t XOR h_(t+P)
is 1 except for the isolated times t=kP+i with a_k=a_(k+1)=0 (at
least P ticks apart). The causal inverse triangle reconstructs a single
genuine west half-history, though not necessarily a finite whole west.
The physical material path stays at -1, except that around every such
zero its positions at t-2,t-1,t,t+1 are -1,-2,-2,-1. Indeed the raw
depth-two bit y_s=h_s XOR h_(s+1). At t-2 it is common white, so the
new depth-two disagreement takes the old head; at t-1 both raw pairs
(y,h) are 00 versus 11 since h_t=0, so the new depth-two difference
takes old depth two; at t the new head takes depth two since h_t agrees.
All other successive differing heads take the previous one. The omitted
head at each t-1 is also a child of the spine's head at t-2. Thus this
is exactly the stabilized head-supplying founder, with aperiodic bounded
position. Any finite prefix is also compatible with an ordinary finite
initial west, by truncation beyond its inverse triangle. No infinite
finite-west realization or physical east is asserted. The true white
wall's eastern latch forbids this entire example.

There is also a sharp local obstruction to replacing the moving geometry
by a fixed two-lag path. If p is bounded but not eventually P-periodic,
p(t+P)-p(t) has both signs cofinally by telescoping: if eventually
one-signed, each residue subsequence would stabilize. Thus AB and BC
meet or pass on opposed neighboring edges repeatedly. On a meeting A=C
differs from B. A strict swap need not transport AC to either target:
take the old words at x-1..x+2 to be A=1110,B=0010,C=0000. The new
bits at x,x+1 are respectively 00,11,00. AB takes x->x+1 while BC
takes x+1->x. Three such window prescriptions can be realized in one
west-clamped lag-P history whenever the three needed finite head windows
are disjoint; the true singleton prehistory is not asserted. For the
real mixed wall there is a recurring two-site cut: whenever c_t=1 and
c_(t+1)=0, h_t=1 in both copies, so no D exists at -1 at t. The old
OR at -2 at t-1 is common (if c_(t-1)=0, y_(t-1) and h_(t-1) are
complements; if c_(t-1)=1 both agree pairwise). Thus any D at -2 at
t has its material parent at -3; no path is confined forever to these
first two cells. The fixed-Q bridge still requires a growing depth or a
strict source loss; the free-geometry west countermodel does not provide it.

The actual obstruction is to causal finite memory, not merely to
periodic positions. If a bounded spine's next step at t were computed by
a fixed finite-state reader of prior steps, clock phase, and finitely many
h values through t+P-1, the same ray decoder would be finite and
deterministic: in order to choose a real/virtual site on g, positions
need be advanced no later than t=g-1 (p<0). Even that last step reads
only through h_(g+P-2). Increasing g then determines the new h bit and
the joint bounded decoder state. All sufficiently late equal finite
input/memory states would have the same future, forcing eventual
periodicity. The west-only detour construction needs the fresh bit
across this cutoff, consistent with its aperiodic output.

For an isolated black exit c_(t-1),c_t,c_(t+1)=0,1,0, the genuine
east forces one more old OR to agree: the depth-two discrepancy at t
copies depth three at t-1 and depth four at t-2. Write y_s=X_s(-2),
z_s=X_s(-3). If c_(t-2)=1, h_(t-2)=1 and y_(t-2)=1-h_(t-1);
then z_(t-2)=1-y_(t-2), so its OR with y is 1. If c_(t-2)=0, let
r0,r1 be the actual east heads at t-2,t-1. They are nondecreasing.
For (r0,r1)=00,01,11 respectively, the pairs (y,z) at t-2 are
(1,1),(0,1),(1,0); all ORs are 1. No common OR at the next diagonal
step is implied by even a genuine finite eastern initial ray. For two
repeats of the clock 0001 followed by 00, take initial strict east
all white. Its first and second white runs have R respectively all
zero and all one; the first nine demanded west heads are 001111010.
Decode them on a finite initial west (zero-extend). The full Rule 30
evolution then realizes this center segment. At ages 0 and 4 the raw
pairs (x=-4,-3) are (0,1) and (0,0): the depth-four discrepancy at
age 1 takes the age-zero depth-three parent, reversing the diagonal.
The physical path feeding the head has depths 3,4,3,2,1 at ages 0..4.
This finite marked-west control does not start from the singleton and
does not give an infinite return. The next step must control distinct
exit episodes by the common origin, rather than prolong this diagonal.

**Cofinal fork on the same marked orbit with both overlapping strips.**
Immediately upon visiting ray g=t-x at path site x=p(t), its known
D=1 supplies h_(g+P-1). Thus before deciding the next step the finite
decoder knows the ENTIRE older raw west from x-P through 0 and newer
raw west from x through 0, including center phase and all masked reads
through that head index. On a stationary move the next real ray supplies
one new head; on a westward move its skipped common-white ray and the next
real ray supply two. Eastward moves use the same already decoded ray and
can repeat only boundedly often in the band. Hence, for every finite k,
there are two arbitrarily late true same-phase times with the same last k
joint views and same path positions but different next moves. Otherwise a
finite lookup table for that suffix would advance the decoder and make h
eventually periodic. Cofinality follows by applying the argument after
any cutoff. Past moves may also be included in the matched views.

At such a fork the P-path child flags are elementary. Its east child
exists exactly when the OR at x+1 is common; its stationary child needs
a common west bit at x-1 and a differing OR at x; its westward child
needs x-1 common white AND a common west bit at x-2. Therefore all
differences between the instantaneous child sets depend on just the TWO
newer bits x-1,x-2 still outside the decoder. If the newer x-1 differs
between the two actual epochs, exactly one P-copy has a differing west
neighbor and is forced east to survive. This inter-epoch difference is
the rightmost strict-west discrepancy, travelling ballistically to the
true white head exactly -x ticks later in the newer row. If x-1 matches
and x-2 first differs, only the westward child can change, and the
inter-epoch head differs one tick later. If both match, the two paths
select different surviving children in identical current gates. The
missing step is to rule out the fresh true-right read or this future
branch selection on a marked bounded path; the c=0 clamp example shows
why the selector cannot be inferred from the overlapping west alone.

**True eastern supply of the fresh read.** Put R=X(1), E=X(2),
F=X(3). While c is black the pair (R,E)=01 locks. Until lock R
alternates: 00 goes to 10 or 11, 11 goes to 00, 10 goes to 00 or
01. Thus when two copies with the same drive are both unlocked in
opposite R phases, their hidden material D stays at x=1. If one is
locked and the other remains unlocked, that carrier goes 2->1->2
in each unlocked 00->1*->00 cycle. At the first edge its only active
OR input is x=2; on the second the two ORs at x=2 coincide at 1,
so the old x=1 is the material parent. A first visible difference on
the white following k black ticks, after a common high at the previous
white, requires k even, one locked copy, and the other still alternating.
A white mismatch following another matched white instead requires the
earlier R to be common zero and E to differ.

Bounded physical P-spine width M precludes M+P consecutive ticks on
which *all* white reads are zero, and precludes such an interval on
which all are one: h then has the P-clock on the first M comparisons,
so the initial M actual western sites all agree. Consequently every
long past of matched masked reads from a cofinal fork contains common
white highs with gaps <=M+P. Go back to the first high within each
common white run reaching 1. If it follows a black then the preceding
(R,E) is 00 in both copies (black NOR); if it rises from white zero
then the preceding pair is 01. These simultaneous two-cell agreement
rows occur with bounded gaps (allow one clock period for the run start)
through the interior of the matched past. The physical eastern material
ancestry of the first release must sit at x>=3 at every such row; it
cannot cross the synchronized center.

For every drive with no consecutive blacks the interior strengthens to
agreement of the FULL x=1 column, not solely on white ticks. For a 010
center window with black at b,
    R_b = R_(b-1) OR NOT R_(b+2).
Indeed the previous white high sets R_b=1. After previous white zero
the black-entry pair is (e,e OR f), hence 00,01,11. After black and
white, R_(b+2) is respectively 1,1,0. Iterating by +2 determines
every hidden black bit from later whites unless the drive remains
alternating and their earlier white readings remain zero. The bounded
P-spine excludes an arbitrarily long such string by the preceding
M+P bound. Matching a long masked past therefore gives matching raw
R throughout its interior with bounded terminal loss.

Lock reset cannot simply be iterated as irreversible loss of the east
source. In site order x=1..6 take the two finite strict-east rows
010001 and 100001, zeros beyond, and the common periodic drive 101000.
At tick 0 A has the black lock and B enters it; both pairs at tick 1
are 01. The old x=2 discrepancy has the material path
2->3->3->3->2->1 at ticks 0..5. At tick 1 the two x=3 bits are
1/0, and x=4,5 common 0,1. At tick 2 the x=3,4 pairs are respectively
00 and 11, giving the next x=3 difference; the following common 00
at x=1,2 permits its retreat to the observed white head. All earlier
white observations match. These are real finite right histories with
the same mixed drive, not two shifted ages of the single marked source.
They show why repeated source charges must retain that true shift.

The productive-column conclusion extends to all mixed clocks with black
runs of length at most TWO. On a double black b,b+1 bracketed by white,
    R_b = R_(b-1) OR R_(b+2).
After previous white zero the three possible black-entry states 00,01,11
give respectively 0,0,1 at the following white: before a lock the R-bit
alternates, and the 11 entry goes 11 -> 00 -> 1*. Previous white high
immediately fixes R_b=1. This recovers every first black bit, jointly
with the isolated-black +2 rule (if its unknown target is black, it is
the first black in a run). In a matched-past interior the *second*
black may still differ. But then the entry was common R=0, the two
entry pairs were 00 versus 01, and both reach R=0 at the following
white. The 01 copy stays locked, so has E=1 there. At the next tick
R is common, because this tick is either white or a first black. Therefore
the other copy must also have E=1 at the white after the doublet. The
disagreeing individual at x=1 on its second black has NO child: the
next center and x=1,2 all match. No physical eastern parent path feeding
the first fresh white release can touch x=1 in the matched interior.
This covers 01,011,0011,00101 and all larger periods in that class.

This inference may be applied at another column with its actual driver;
periodicity of the driver was not used, apart from the bound on unresolved
+2 chains along a perfectly alternating segment with no high observations.
For an alternating center, the full agreed x=1 column R has 1-runs of
length at most two (a high cannot survive a black center). It has bounded
alternating segments, since on such a segment it is 2-periodic and the
bounded west P=2 path forbids this across M+2 ticks. Whenever R=0,
the observed x=2 value is known as R_(t+1) XOR c_t. Apply the same
productive double-black classification with driver R to conclude that
the actual eastern source of a first fresh fork bit avoids x=1 AND x=2
through the matched-past interior (discard a bounded cap at either end).
This is a conditional depth result for the marked lag, not P=2 closure
or an induction across arbitrary successive drivers.

### Coupling a bounded physical lag path to actual checker material

Use the stationary checker with even raw black. Its genuine material paths
move east between boxes {y-1,y} (y even). Write L,M for those two raw
columns. A permanent material resident there forces M<=L and L with no
successive ones, as in `ancestry_ultra/TRUE_LAG_CHAIN.md`. A physical lag-P
material path can then never take the WEST edge within that same box: such
an OR edge needs both L bits white and the M bits unequal. Neither can the
physical path remain forever inside that very box. Common L=0 gives no D in
either cell; common L=1 gives common L'=0 at the next cut, also no D there.
Thus a forever path would force L(t+P)=1-L(t) eventually, making this true
western column periodic together with the center, excluded by the mark.

More generally an intrabox west step M->L in the physical D genealogy
compares the true checker box state empty (raw 01) versus occupied (00).
Infinitely many such steps at a fixed box force cofinally many absolute
cut intervals of length P with different occupancy at their ends. Both
directions of occupancy change occur cofinally in the full lag record
(by telescoping each residue mod P). Every empty-to-occupied interval
requires a fresh material arrival from a strictly western checker box.
This rules out feeding the required box forever by one resident's stay;
repeated admissions from descendants of one upstream founder remain possible.
On the other orientation of physical west step, from odd y+1 to even y,
the two actual copies have y commonly white and y-1 common (OR-parent
condition). When y-1 is white, both histories have the old even checker
vacancy at y. When y-1 is black both contain the odd checker defect at y-1.
The new even vacancy in the one copy retaining it has this already-shared
western-box material parent, rather than an arriving eastern checker
particle. Thus the two types of west move cannot both be charged as fresh
admissions. A bounded path visiting at least three sites infinitely often
crosses an intrabox edge west infinitely often; the exceptional two-site
range across a box boundary requires the second, shared-donor accounting.

### The two real suppliers and the directional reset on an outward excursion

On the bounded western lag-P spine branch there are syndetic white q highs.
A common high (C,R)=(0,1) at t makes the odd checker particle at t+1 a
fresh center admission in each copy. At t+2 a live even vacancy has that
odd as its parent (the west XOR term) and a live odd is another fresh input.
All earlier head-box stock has left or died. At a first high after a white
zero the true (R,N) states are successively 01,11,10: the shared entrant
is paired with a common vacancy. The first later raw R split necessarily
has a differing x=3 gate acting on a common vacancy, after this entry.
At a first high after black, (R,N) at t-1 is 00, and the exact entry bit
N(t+1)=NOT(X(t-1,3) OR X(t-1,4)) explains the other possibility: the
homologous entrant can already face an unmatched even gate.

Fix Q a multiple of P. At a late real white wall mismatch D_Q(t,1)=1
as well as D_Q(t,-1)=1. The east-head ancestors at any fixed cutoff S>=T
are nondecreasing in spatial order along these successive events: no D
path can cross the common center, so a later event's lineage is at or east
of the earlier +1 at that earlier time. The finite support stabilizes that
cutoff's label. As on the west, the stabilized labels at all S give a single
coherent true eastern path e(t)>=1 supplying arbitrarily late paired events.
The two paths are correlated by using these same events. If the h orbit
closure contains no periodic point, every fixed positive even checker box
flushes with bounded gaps: arbitrary intervals with its G_y constantly zero
would drive sites 1..y-1 by the periodic center and constant right G_y, so
finite-state cycling supplies arbitrarily long h factors with a common
bounded period, contrary to this case. It follows that occupants of each
fixed positive prefix at any cutoff are gone from that prefix after a
uniform number of ticks: concatenate the flush-gap bounds in directed
box order (round the right edge up to a box end). This concerns checker
material, not loss of alternative D_Q control through fresh cancellations.
In the other case a periodic point in the h orbit closure gives arbitrarily
long actual D_Q(t,-1)=0 intervals for one fixed multiple Q of P.

Suppose the actual east-supplying path has Q-periodic geometry. Its
boundary word b(t)=X_t(e(t)) is anti-Q, hence 2Q-periodic. Simulate the
finite interior between the periodic center and this boundary. A stay or
west step calls for no exterior input. During a maximal run of d east
steps put e_k=e(t+k), b_k=X(t+k,e_k), o_k=X(t+k,e_k+1), and let u_k be
the new interior value X(t+k+1,e_k). Let u_-1 be X(t,e_0-1). Then

    u_k = u_(k-1) XOR (b_k OR o_k),
    b_(k+1) = b_k XOR (o_k OR X(t+k,e_k+2)).

At the next non-east step the previous site e_(d-1) has D_Q=0, since
otherwise the path parent at e_d can take neither a stay nor a west step.
Thus the final u_(d-1), at this fixed phase of the Q-periodic geometry,
has ONE value common to every late cycle; use it as a fixed finite
parameter in the strip simulation. At b_k=1 the interior OR is known; at
b_k=b_(k+1)=0 it vanishes. For a rise b_k=0,b_(k+1)=1 the only unknown
is o_k. If the next step in the excursion has b_(k+2)=1 as well, that
step has both exterior bits zero; o_(k+1)=0 and the preceding exterior OR
one force o_k=1 (if o_k=0 its next raw value is one). Thus only an isolated
high 010, or an unguarded rise on the final edge, can supply an unknown
input. The displayed u recurrence and final constant determine the parity
of these unknowns. When at most one remains on EACH excursion and phase,
solve it before simulating the excursion. This gives deterministic
finite periodically driven dynamics for the actual interior, hence R and
h become periodic against the true west mark (if boundary is 1 use b at
that phase). In particular Q-periodic east geometry with at most two
consecutive east steps is impossible, regardless of Q. A survivor of this
periodic-geometry branch must contain at least two unresolved outward rises
on a single excursion/2Q-phase, not an arbitrary stepwise exterior stream.
The geometry or these residual parity-paired inputs may still be aperiodic
in the remaining cases; no periodic geometry follows from boundedness.

There is a genuinely marked crossing restriction on precisely those
outward gates, even when the two-rise parity leaves freedom. Take any K
multiple of 2Q. Along the Q-periodic D_Q material path every boundary
value is K-common. Every actual western-mark D_K crossing ray in
`ancestry_ultra/TRUE_LAG_CHAIN.md` eventually reaches the true eastern
mark, so it must overtake this bounded path. A stay is uncrossable: old
x=e-1 is Q-common (otherwise the selected D_Q parent e cannot stay), and
old and next x=e are K-common. A west step has old x=e-1 commonly white,
old x=e-2 Q-common and new x=e-1 K-common; the ray cannot get across
from the next possible old discrepancy at or west of e-3. At an east step
the sole possible crossing is the horizontal jump (t,e-1)->(t,e+1).
Indeed old e and new e+1 are K-common, and a jump may omit its intermediate
site only when it has no available discrepancy at either age (using the
extremal companion ray that takes the immediate neighbor if available).
So D_K(t,e-1)=D_K(t,e+1)=1, D_K(t,e)=D_K(t+1,e)=0. The raw gate at e
is white; the differing o_k and common next boundary force the raw b
rise 0->1. A 011 continuation during the outward excursion is impossible
by the previous o_k=1 constraint. Conversely, if an actual temporal D_K
path enters the interior *from* the outside at an outward step, its
west edge e+1->e requires D_K(t,e-1)=0 with exterior D_K(t,e+1)=1;
the new inner D_K is 1, rather than 0. Thus the compulsory marked
west-to-east crossing and any incoming eastern material cannot use the
same occurrence of an unresolved gate. A west-to-east ray exists for
every true western launch; it is not assumed injective in those launches.
Neither source is claimed to make the two opposite crossings simultaneous.
