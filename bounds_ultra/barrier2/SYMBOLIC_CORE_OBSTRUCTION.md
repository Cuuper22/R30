# Rooted three- and five-edge obstructions

Write X_i(t+1)=X_{i-1}(t) XOR (X_i(t) OR X_{i+1}(t)). E_t means the
center changes from t to t+1. Initial x<0 is white, x=0 black; s_i, i>0,
are arbitrary original inputs. No transient center bits are clamped.

**T=10.** The deletion-minimal core is E13,E15,E16. At t=10 put
a=X_-7=X_-5=X_-4, u=X_-2, v=X_-1 and r=X_1. X_-6=1, X_-3=0.
The common initial donor is a=s1 AND (s2 OR s3). Directly advancing
the causal cones of u,v,r gives u=v=r=1 only for s1s2s3=111, and
v=0 only for s1s2s3=001 (not converses). The three demanded edges with
the fixed coexisting western prefix instead require uv r=111 when a=0,
or 001/100 when a=1. Both alternatives contradict original ancestry.
The seven-tick local expansion uses all unconstrained x=0 and x>=2 bits.
A direct standard-rule lattice enumeration can check the original donor table
with just the eleven relevant strict-east bits (symbolic_preproof.py).

The gate-level expression: at t=15 let A,B,C,D,E=X_-2,...,X_2.
After E13 and E15 the exact reachable five-bit patterns are 00011,
11000,11001,11110. When C=0, A=B,D=not B: center and left at t=16 are
1 and 0, so the final OR keeps 1. When C=1, A=B=D=1: left/center/right
at 16 are 000 and the center remains 0. Either phase violates E16.

**T=30.** The core is E32,E34,E35,E36,E37. At time 34, after E32, set
(a,b,d,e,c,r,s)=X_-4,...,X_2. The SAME marked history obeys:
(1) if a=0,b=1 then d=e;
(2) if a=b=0,e=1 then s=1;
(3) if b=1,d=0,c=1 then r=0.
These are joint ancestry conditions, not universal Rule-30 gates. Conversely,
the four remaining flips, expanded on arbitrary rows, have just six
prefix possibilities for (c,a,b,d,e), with (r,s) indicated:
00001:00; 00101:00/01; 00110:10/11; 10011:00; 10101:01/10/11;
11101:11. Thus a=0,b=1 breaks (1); a=b=0 breaks (2); a=1 breaks (3).

At t=36 after E32,E34,E35,E36 the exact five-bit rows are 11000,11001,
11111. They give precisely the same terminal two OR contradictions as at
10. Actual original strict-east witnesses (bit zero=x=1) respectively
0x3ffffff1f9, 0x30003226c4, 0x3fffffffff.

The numerical checks here are small symbolic spatial partitions, not SAT
proof logs. The normalized one-step map is F(q)=4q XOR(q OR 2q). Keep a
fixed low prefix and a SET of the next w words, split both choices when
needed, widen the rest to arbitrary. Such a cylinder always contains
every true extension. At age 30 the 39-bit symbolic cover has 796 words.
Four false positive complete words (hex) alone could pass the remaining
clock: 6e1fb1e713 (five-bit signature 01001), 4a0134737b, a0134737b,
2a0134737b (01110). All four have no true common original right input.
Split the ORIGINAL positive variables in order, applying F thirty times
with a seven-bit uncertain fringe and rejecting only provably mismatched
outputs. The exhaustive binary tree has 255 vertices, maximum fixed input
x=20; no original assignment survives. See symbolic_core_parent.py.
symbolic_core_interpolant.py checks (1)-(3) on the remaining rows and
checks all future rows, without a SAT call.

**Transfer.** Earlier flips in the respective forward-minimal cores force
A=B and C=1 => D OR E=1 at v=T+L-3 for all four tested T. The stronger
C=1 => D=1 from 10,30,60 fails at 120: strict east
0x57268542fbfc4e710022ff907767ff8f3 gives 11101 at t=133, with earlier
edges intact. The T10 three-edge stencil fails already at age 30:
0x3011f4b39c gives 01111 at t36 and all three translated flips.
The long-lived normalized donor a=s1 AND(s2 OR s3) does not uniquely
route to the terminal phase: at 10 and 30 C(v)=1 implies a=1; at 60
0x2d8a28ec99 has a=0, C(68)=1. At T60 even the SAME terminal 11110
occurs with both donor values. The 120 implication C(133)=1 => a=1
returns. Rule90 admits 01110 with the same required earlier edges at all
four ages; the scalar originals are in symbolic_five_transfer.txt.

There is no all-onset induction in these calculations. The paired terminal
OR formulas alone do not say that any future alternating run reaches a
blocked configuration; each marked-ancestry certificate retains its onset.

The four spurious T30 seam words have still shorter, literal named donor
proofs. At the *actual onset row* J=X_-15(30) is shared across them:
if J=1 and X_-8=X_0=0, then X_1=1; if J=0 and X_-4=X_2=X_4=0, then
X_5=0. The first clause rejects the 01001 candidate; the second rejects
all three 01110 candidates. These two clauses are separately deletion-minimal
as rooted spatial implications (concrete witnesses in
symbolic_donor_smallcuts.txt, order 51). Their exhaustive original seed
proofs have 153 and 355 nodes. In left-normalized coordinates the clauses
hold identically across all ages >=30 at these SAME moving-front offsets,
because F^t(odd) is a subset of F^30(odd). The first fails after a one-cell
spatial translation on strict east 0xc9185f005, the second on 0x107c26b47
at age 30. The latter failure also occurs at a two-cell shift with the
singleton's own 16-bit clock phase, strict east 0x13bf494a61. This
distinguishes time translation at the actual front from transport inward.

At t>=19 the normalized 16-bit prefixes of all genuine marked inputs
are phases of the same 4-cycle e713,737b,3a13,967b. All four phases occur;
the phase depends only on original x=1..8. Thus J is itself a persistent
higher phase bit, flipping every two ticks; it is not determined by the
depth-3 bit. Even the entire 16-bit phase does not uniformly route to
terminal C under the earlier core edges: at T=30 the phase e713 (measured
at absolute t=30) rules out C(36)=1, whereas at T=60 the same phase
allows C(68)=0 or 1. t36 and t68 are in the same mod-4 phase.

Nor is an exact restart with an eventually identical two-lane clock possible:
B_(i-2)(t)=B_i(t+1) XOR (B_(i-1)(t) OR B_i(t)). If adjacent pairs
at normalized depths j,j+1 and d,d+1 (j>d>=0) in two marked histories
match for L ticks with a temporal phase shift, their rth predecessor
columns match for L-ceil(r/2) ticks by induction. At r=j this would
identify B0=1 with B_(d-j)=0, so L<=ceil(j/2). Only a strictly weaker
cut observable can transfer; the actual periodic center supplies no
two-column restart. In the finite-window relaxation alone, freeing only
x=-1 from the original vacuum also destroys both core obstructions; the
scalar counterexamples have strict east 0x18a42 and 0x3ffc4f2ce7.
