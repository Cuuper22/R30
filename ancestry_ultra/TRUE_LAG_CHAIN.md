# Step 4, single true-orbit implication

Write (Z_s) for the canonical singleton spacetime, vacuum on the far west and the same absolute checker on the far east. Its actual marks at age (s) are its leftmost one at (-s) and its last discrepancy from that checker at (s-2). Write (D_Q(s,x)=Z_{s+Q}(x)\mathbin{\rm xor}Z_s(x)), always for two ages of THIS orbit. Fix a supposed period (P>0) and onset (T). For every positive multiple (Q) of (P), all (D_Q(s,0)) vanish from (T) onward.

**Target chain.** Find one such (Q) and (s\ge T) for which no later white center exposes an eastern lag difference. Then the local rule gives (D_Q(u,-1)=0) for every (u\ge s): on black the head is already independent of the east, and on white its lag difference equals the east difference. Two adjacent columns now agree at every future tick. Left permutivity forces agreement successively at every site to the west, at all ages (u\ge s). At (-(s+Q)) the second row is black at its true left mark, the first blank. False. The unproved implication is the existence of that one future-mask common tail, not the final descent.

**What exact same-orbit ancestry supplies.** A two-tick vertical pair is black precisely when the current site is black and its immediate west neighbor is white. Consequently, at every physical cell, with all operations over F₂,
$$
Z_t(x-1)=Z_t(x)+Z_{t+1}(x)+Z_t(x+1)Z_{t+1}(x+1).
$$
Subtract the same identity at age (t+1). This yields the exact two-lag constraint
$$
Z_t(x)+Z_{t+1}(x)=D_2(t,x+1)+Z_{t+1}(x+2)D_2(t,x+2).
$$
In particular on an alternating true center the nearest strict-east lag-two mismatch is always at distance one or two. This closes the attempted subimplication that the true tips could force arbitrarily long *lag-two* east agreements: they cannot even force width two. It does not forbid synchronous cancellation at every later white.

For arbitrary (Q\equiv0\pmod P), the first displayed identity at the two ages also gives
$$
D_Q(t,-2)=D_Q(t,-1)+D_Q(t+1,-1)\quad(t\ge T).
$$
A run of mismatch times of the western head therefore gives its two boundary times one column farther west. The product term at the next column is the difference of the two actual vertical western-head bonds; it cannot be replaced by an independent input. Preserving this term and the actual marked prehistory is essential. Neither the existence of indefinitely many head mismatches nor the fact that every signed lag difference telescopes on each absolute time residue contradicts the two true exterior marks by itself.

**Finite form of the hard implication.** Infinite masked agreement is stronger than needed. Fix true ages s and u=s+Q of the same clock phase, and let d be the least positive western depth at which those two rows differ. It exists by the real mark at −u; in particular d≤u. For every n≥0, the two rows agree on their first n strict-west bits if and only if the next n western-head samples agree. Forward direction: in one tick equality of a prefix of n western sites, under the common center, gives equality of its first n−1 sites. Reverse direction: the new prefix and the old first bit determine the next old bit successively, since the rule is permutive in the west input. Equivalently the first different head sample occurs exactly d−1 ticks after s. For the genuine common center this is exactly the first different strict-east reading at a WHITE time (the black-time west head is already fixed). Thus it is enough to obtain one pair s,u whose first d masked readings agree; agreement for u physical ticks is a source-independent sufficient threshold. This is a strict shortening of the required recurrence, not an existence claim about such a return. The later rightmost checker mark is u−2; the outer inequality d≤u uses the western mark and cannot on its own force the eastern return.
