# The common source wire and its first failed transport

Strict-east input bit i−1 means original site +i. For the T30 G1 seam
obstruction, split the bad conjunction into west X_-15=1,X_-8=0 and east
X_0=X_1=0. The independently feasible original prefixes of the two
sides have just one common strict-east word at width 13: 0xc9c. At
width 14 they are disjoint. Defining b=s14, the actual age-30 four-cell
table (X_-15,X_-8,X_0,X_1), all completions allowed, is

    b=0: 1010;   b=1: 1100 or 1110.

For G2 the west side is X_-15=X_-4=0; the east side requires
X_2=X_4=0,X_5=1. The only common 13-bit prefix is 0xfcf, with
the age-30 five-cell table (X_-15,X_-4,X_2,X_4,X_5)

    b=0: 01001, 01100, 01111;    b=1: 00010,00011.

G1's two sides thus demand b=0/1, and G2's sides demand b=1/0.
Each side has a genuine original right ray. Their exhaustive true
prefix splits are in symbolic_common_origin.py and
symbolic_common_origin.txt; these are Boolean updates, not SAT output.

The opposite signs have an exact marked-source explanation:
with the original marker included, for b in {0,1},

    F(0x1939 + b*0x4000) mod 0x8000
        = 0x1f9f + (1-b)*0x4000,
    F(x)=4x XOR(x OR 2x).

Thus one *real* Rule30 update, re-rooted at its new leftmost black
site, always sends the first source cylinder into the second and toggles
the disputed input. The G1-west strict-east witness 0xc9c maps exactly
to G2-west strict east 0x2fcf. The other input is not free to splice:
G1-east 0x2c9c maps to 0xcfcf which fails G2-east. At the candidate
output the one-step relation is exact through normalized depths 0..29
and breaks at the center, depth 30:
F(0x6e1fb1e713) mod 2^39=0x464134737b; compare the three G2 target
words ending a0134737b. Full pair matching is not established.

Nor does a fixed 14-bit cut uniformize the measured thresholds. Two
scalar-replayed T60 strict-east seeds 0x1080152488a3d88,
0x2ac000800164b17d88 share the 14-bit prefix 0x3d88 and meet every
earlier core edge, but their terminal C(68) values are 0/1. A full
two-copy original cone does rule out such pairs at T30 and T120.

There is also a uniform reason the re-rooted target cannot naively
inherit either core. The new center is the old west neighbor W.
If the old center alternates, W is 1 on every black tick and equals
1−R on each white tick. A right bit R=1 on a white tick forces the
next R'=1 and then R''=0 on the following white tick. Thus zeros of
W have distance at least four; its flip edges occur in isolated pairs
with at least two missing edges between those pairs. It has neither
the T10 edge pattern {v−2,v,v+1} nor T30's four consecutive flips.
The cylinder synchrony is genuine but cannot by itself rule out an
alternating tail at an arbitrary T.

The correct translated observer has offset +1 in the new marked row, so
the relevant first-branch ages become 29 instead of 30. Testing the sparse
normalized observables under every continuation of the single unrestricted
0xfcf tag gives B22(29)=B26(30)=1-b, and if this common bit is zero then
B30(29)=B34(30)=1. Thus *both* west requirements now demand b=1, while
both east requirements demand b=0. Replacing the genuine previous
F-image by this whole tag adds one attainable second-branch word 01111;
that word cannot satisfy either required side. See symbolic_offset_wire.py.

The straight readout through depths 22,26,30,... at times 29,30,31,...
cannot continue: on the genuine original 0x2fcf the next pair
(B30(31),B38(31)) is 00; every one of the four pairs occurs on the
b=0 half. With the observer offset updated correctly (same normalized
observed sites), the 15-bit original tag suffices for offsets 0..6; its
first spurious wrong-side continuation is 0xe07fd at offset 7. It first
disagrees with the genuine prefix at normalized depth 15. Preserving that
additional bit resolves the cut. A growing resolved source prefix plus the
joint allowed values of the next two bits carries the finite proof across
all 31 possible cuts; a one-bit fringe fails at cut 13. These are finite
properties of this measured source fork.

At the two larger measured onsets, with the actual earlier deletion-minimal
edges imposed, the same physical onset clauses transfer differently: G1
holds at 60, while 0x28d3684c081774817c violates G2 and subsequently
passes those earlier edges. Both clauses hold at 120, but no earlier-core
history there has the original 0xfcf tag. Rule90 violates G1 at age 30
from black set {0,15,19}, and G2 from {0,32,35}.

## Later shared-past cuts (T=60,120)

Let X_i denote the physical bits at s=T+L(T)-5. At s=66 require the
four earlier flips E60,E61,E63,E64. At s=131 require E120,E121 and
E123 through E130. Both true marked cones obey

    X_-3=1, X_-2=0, X_0=X_1=1   implies X_3=0.             (H)

This also follows from the stronger previously derived X_1=0 clause
at s=34 under E32. It fails at s=13 with its own earlier observations
(empty), original strict east 0x18307. R90 exhibits the broken conjunction
at both later cuts, strict east 0x3cafffffffffffffff and
0x7b2effffffffffffffffffffffffffffff, respectively. At 60 all four prior
edges are essential to H; at 120 E120 can be dropped, while removing any
of the other nine admits a genuine counterexample after it has been dropped.

The west pair (X_-3,X_-2)=(1,0) and east triple (X_0,X_1,X_3)=(1,1,1)
individually occur. At 60 their last mutually compatible original prefix
has 19 bits. On the common tag 0x1f7c they demand s20=1 and s20=0:
west 0x10112f81f7c; east 0x1492c8d043d1c01f7c (strict-east integers).
In a solver-free forward Boolean prefix tree the incorrect west sign is
excluded at the very first node *even without the temporal conditions*;
the incorrect east sign is excluded after 443 nodes with those conditions.
Two other T60 OR alternatives split on s21 at tag 0x3d67 and on s19 at
0x1d09 (see symbolic_mature_fork_60_* and symbolic_mature_tags_60.txt).
Enumerating true marked nine-cell signatures yielded 73 possibilities; the
remaining three demanded flips admit 64, with empty intersection.
Keeping just positions -4..+2 leaves exactly two false spatial words:
1100110 and 1110000. They require the opposite +3 bits from their genuine
ancestors; 1110000 additionally constrains +4 in one branch.

At 120 a surviving common original prefix for H is 0x17c (11 bits).
On that prefix west demands s12=1, east s12=0. Independent genuine
strict-east witnesses: 0x2dc89d2e56f763c1e4aa7c1eccfcf4297c and
0x2aa25ab5d85ddddd7314c588b9c857e17c. The two opposite-sign conditions
are UNSAT on the full initial cone. This is not claimed as a globally
longest shared 120 prefix. The first eight strict-east bits 0x7c are
common to the displayed 60 and 120 forks; the particular 60 19-bit
prefix 0x1f7c already admits neither separate 120 wing. The other two
60 spatial clauses both fail at 120 on actual earlier-core histories.

In a continuously alternating history every black tick with X_1=1
already has X_-2=0,X_-3=1 (two-step gate and its next white read).
Thus a transported H would exclude on black phases the right word 1?1.
This rejects 429 of 2437 mature black 14-bit words but still admits a
variable-white-clock 665-state recurrent component in the 14-bit
projection; the same obstruction survives width 18, in components
of 2110 and 680 states. H has no all-onset derivation. These are
source-fork transfers and controls, not a Step 4 closure.

The location at which the two tagged wing histories first cease to overlap
in their *genuine normalized rows* is measurable, rather than inferred
from the distance to the center. At 66 the first distinguishing depth is
56 (physical x=-10). The two signs of s20 fix the full 61-bit prefix to
0x062e7e17e2f1e713 or 0x132e7e17e2f1e713 before any center-edge
conditioning; B56=s20. At 131 the first distinguishing depth is 29
(physical x=-102): both have the same B0..B28, west requires B29=1,
east requires B29=0. The known low-29 word cycles with period four.
B28 is permanently zero and B27 has odd weight in that cycle, so
B29(t+4)=1-B29(t); the singleton has the same persistent toggle.
The low-11 source tag does matter: merely fixing low8 to 0x7c still
admits west with B29=0. The east sign persists even on the 4-bit
tag 0xc; with no tag it too fails.

A same-source transport of the four-cell reading is false. The genuine
marked original strict east
0x91a9cb0cbe476c52f50b4b29f50730d6a00322c0ba5e2c0e802964bca81f5a46b2330797c
alternates at its center from rows 255 through 271. At 262 and 266
its same physical X_-3..X_4=10111111 meets both raw wing predicates,
but B29 is 0 and 1. At row 266 its actual right24 is 0x7c64ef in the
mature black channel. Its two right prefixes agree on only the first
four sites, so this is no counterexample to the 24-bit inverse guard.

At row 131 the seven genuine rooted exclusions (in order -4..4)
00*1*0***, 01*1*1***, 01**01***, 0**11*1**, *10***1*1,
*1*1**11*, **0100*** cover all 32 words passing the last four
flips; each exclusion is from the whole original cone after the
earlier core. Separately, a continuous 4-tick alternating center and
an exact same-history 24-bit strict-east return at lag 4 leave precisely
8 possible initial 28-bit east words in white phase and 7 in black.
All 15 fail the true left-marked original cone at T60 and T120, with
no transient or source-tag restriction, and R90 has genuine witnesses
at both phases and ages. This does not force lag 4 to occur on an
arbitrary infinite P2 history.

There is a second, permanently coupled T60 branch: on low18 tag 0x1d09
the west pair 10 vs east X0=X2=1,X3=0 choose opposite s19, and B29(66)
is identically NOT s19 on every completion. The corresponding T120 west
and east branches select exactly the same two time phases of a single
8-cycle on all B0..B29: at t=66 their prefixes are 0x22f1e713 and
0x02f1e713, and at 131 0x2c34737b and 0x0c34737b. Four true steps swap
the two phases. Under low11 0x17c at T120 a 16-node exact decision
diagram computes B29(131) from s12..s20; s12=1 OR s13=1 already forces
its west value 1. See symbolic_record_gate.py. All eight physical local
bits can repeat on opposite phases of this same clock in a genuine
finite alternating interval, as above.

The phase-four prefix specialization of the mature inverse also propagates
in time. For the four (phase,right24) labels
(0,0x81020),(0,0x264c99),(1,0x1c3870),(1,0xfbf7ef),
the first ambiguous earlier white q is 58,56,59,57 ticks before the
label. The forced readout extends respectively 97,99,100,98 ticks after
the lag-four return's first occurrence, using its second occurrence.
Thus, once the entire relevant earlier interval is mature, the real
west register at the earlier row has 155,155,159,155 forced consecutive
bits of the same spatial-width-seven ether. Two age-ordered returns
whose gap is <=150 share a white tick and select the same ether phase;
a syndetic chain at that spacing would force an eventually periodic
masked readout. The finite two-sided radius-188 fixture from Ancestry
(whole(34865,188,196)) alternates for 195 ticks and its 183 mature
phase-labeled right24 words at rows 12..194 are all different. It still
has the persistent B29 four-tick flip. Finite marked exterior at the
onset does not force a <=150-gap chain. A genuine marked R90 source
(right bits at sites 2,4 mod6, left vacuum) repeats all 24 east bits at
four-tick lags from rows 64,128,256 without the preceding ether readout.

At each mature black clock tick put A=(X1=X3=1) and B=(X1..X4
is 1101). Five consecutive black ticks cannot avoid both: the successive
backward viable right4 sets have sizes 11,6,5,2,0, with the two outside
east bits entirely free per strobe. On each A or B the two required
west cells X-3,X-2 are 10, provided the clock continues far enough.
The true 34/66/131 marked projections forbid both hazards together with
this west 10 under their respective earlier sparse clocks. The two raw
131 exceptions to the weaker B test have X4=0. A genuine marked-right
source with continuous 17-tick P2 nevertheless has A in the interior,
so the fixed-age bans cannot be transported on a short clock prefix.

Using the actual opposite-sign B return (the complete incoming subtype
is also cofinally repeatable, see Ancestry), exact finite cone tests in
symbolic_double_{b,wire,inputs,full}.py gave the following time-to-source
forks with T=120. Throughout, phase is chosen so the indicated endpoints
are black; all stated positive right inputs are original, not seam inputs.

* Clock continuously 120..131, B at 125 versus B at 131. Each separately
  occurs; both together are impossible. The largest common original
  strict-east prefix is five bits, and a witnessed common prefix = 4.
  There the 125 requirement forces s6=0 (e=0xa9f106d85d118e83fe2fe7b03ef58884),
  the 131 requirement forces s6=1 (e=0x2803dde6939e925ba1ddd467b95ef7b764).
  Among the mature prior-white five-bit subtypes, the first clock admits
  10, not 17 or 26, and the second admits 17 or 26, not 10.
* Clock continuously 120..128, B at 122 and 128: the pair forces the
  original s1 AND(s2 OR s3)=1. The two B's are individually feasible
  with s1=0; joint feasibility is UNSAT both for s1=0 and for the other
  false branch (s1,s2,s3)=(1,0,0). A pair exists with true seed
  0xac3605e22228962223feca10f58e41e65, previous white subtype 26
  at both events, and B15 flipping. Enforcing W10 at both endpoints
  makes this pair UNSAT also on the donor-1 branch, so it cannot
  distinguish a fully mature pair. Marked R90 admits the double B at
  the same age with s1=0 (0xb8505050505050505050505050505e1be).
* Clock continuously 120..126, B at 120 and 126, W10 twice and incoming
  26 twice: realizable (0x11430f5a714d7a08f7), but not with s1=0.
  Moving endpoints to 121,127 (same T=120 clock) does admit s1=0,
  e=0x577fe4921dbe61e924601c0a7773743ac. Ancestry's genuine 362,368
  full W10/incoming-26 pair has s1..30 zero and B3=0 at both events.
  Thus neither a literal s1 nor the elapsed B3 sign alone is a universal
  classification, even on the matched subtype.

The mature full B word X-3..4=10111101 is a one-step inverse reset:
scan the old eastern two-bit state right to left using
(old(x-1),old(x))=(new(x) XOR(old(x) OR old(x+1)),old(x)).
All four old incoming states yield old(-4),old(-3)=0,1. Actual R90
root e=0x3d00000000000000 has the same 8 spatial cells at t=60
and old(-4),old(-3)=0,0. In the opposite-direction, fixing an OLD B at
time u and a later opposite-sign B at u+Q allows Q arbitrarily large,
so the decoded initial west from the intervening q word must be exactly
zero beyond absolute depth u. For real clamped-east inputs duplicate B's
at lag 62 can allow an 11-zero final segment of the decoded west prefix
(east 0x1f249e37368e597c7fc1637781997b). Terminal O(1)-stencil black
injection has no such short uniform bound. A growth bound on the last
nonzero digit or a marked-source exclusion remains open.

Ordinary canonical ancestry cannot charge these events to new old labels:
at a black tick t the next black center's ancestor two ticks back is the
old center for q(t+1)=1, and the old x=-1 for q=0. Each white t has exactly
one black at -1,-2: call it Z(t), at -2 iff q=1. Z(t+2) descends from Z(t)
itself, using no11 q on the transition to q'=1. The resulting genuine
lineage is confined to two western sites. Real clamped east R=11 supplied
215 B events through 2,000 ticks, descending from just two black labels
at the fixed original row; the 84/6 ether gave 334 B's from one label.
On the true singleton the two-step center identity had 0 misses in 61
1,0,1 windows through age 500, versus a failure on the genuinely marked
alternating Rule90 control. See symbolic_b_ancestry.py.

The complete marked B-return decoder now uses one 2-adic reference.
At a black B, let W's bit j be the actual site −1−j, and let q start
on the first following white tick. The reference word
q=010000(10)^infinity has W=−1218287007101/16383 by exact
finite lateral iteration (spatial preperiod 29, period 14).
For any actual candidate W, H's left permutivity says that the first
physical tick on which its west-head trace disagrees with this reference
is v2(16383 W + 1218287007101). On Ancestry's complete
minimum-inclusion B dictionary Q=26 has valuation 17, and every standard
long fork Q>=30 has valuation Q−1. The shorter forks prescribe the
initial Q-bit west word. Run symbolic_fork_reflector.py, which reads
ancestry_ultra/p2_b_fork_words.json; the full decoded table is in
symbolic_fork_reflector.txt. None of these implications assumes that
a finite fragment is a full periodic tail.

One of the four initial q-variable eventual components has now been
eliminated for all onsets: the 221-state E25 component (paired 5-gaps).
Lifting every state by both choices of a true 26th east cell leaves one
q-variable recurrent component, size 229. Lifting that component by
both 27th-cell choices leaves two nontrivial SCCs with 140 and 128
states, in each of which q is a periodic function of strobe phase.
The missing current and next outermost bits are universally included
in each projected two-step edge. Any true infinite orbit in the original
component must eventually stay in a recurrent SCC at both widths.
Periodic q, together with the assumed alternating C, makes temporal
columns −1 and 0 periodic. The lateral update then puts all sufficiently
late west in the same unique time-periodic extension. This makes the full strict-west row
repeat after that temporal period, whereas its leftmost black is at
−t and moves one site west each tick. The temporal columns here are
periodic on a common tail with one cutoff, not cutoffs increasing
with spatial depth: left reconstruction uses future ticks only.
See symbolic_q221_lift.py and its .txt output. Other components survive.

For the nonabsorbing E25 host of 24,899 states, its one q-variable
successive lift has 38,337, 59,251, 91,029, 131,265, 203,375 and
315,078 states through E31. At E31 it sheds a 116-state SCC: all 464
outer-bit choices stay inside and its q has period 7. The two positive
finite right seeds 0x1727 and 0x5a0e permanently join it at strobes
187 and 186. All 24,899 finite zero extensions from E25 have their
coarse fate settled by strobe 1,992: 23,305 leave E25 host 24,899 and
1,594 enter that E31 periodic trap. An arbitrary higher original finite
suffix is not classified. The E31 variable SCC can shadow q7 for
arbitrarily many ticks. The other 82,754-state E34 host loses all
82,754 of its zero extensions by strobe 151, but has a 264,368-state
q-variable successor at E39. See symbolic_finite_host_traps.py,
symbolic_finite_attractors.py, symbolic_finite_host_escape.py and
symbolic_host_plateau.py. Host arrays used by these scripts are optional
caches: symbolic_q221_lift.gethost recomputes their exact genuine
components from the published 14-cell input and the physical R30 update.

The earlier same-source 362/368 counterfixture is not in an eventual
q-variable host before either B: its incoming whites 361 and 367 lie
outside all four. Its white 369 is in the absorbing 58,203 host.
At fixed T120 a genuine rooted history can put the NEW 126 hazard
alone in a surviving q-variable host at white 125
(east=0x2b98929b70f38a522d407a5df3dff4873bb912, E25=0x1b10bda);
the old 120 event is incompatible with its 119 host under the requested
clock and subtype 26. This finite obstruction is present at one endpoint,
so is not a new two-time contradiction. Reproduce the finite cone by
g++ -O2 -std=c++17 symbolic_double_host.cpp -o /tmp/r30b_doublehost ;
python symbolic_double_host.py. Rule90 also rejects the joint case
*if* one externally imposes the R30-specific E25 target; hence this
last comparison is not itself a rule-discriminating invariant.
