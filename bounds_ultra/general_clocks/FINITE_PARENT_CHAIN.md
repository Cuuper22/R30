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
