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
