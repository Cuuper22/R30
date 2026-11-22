"""Does the alternating host permit the five pure-ether phases to be
read from any finite genuine dyadic left collar? An odd-factor packing
argument forces a conflicting residue at every dyadic depth. Compute the
actual minimum separation of those comparator windows for the next
marked-source coupling, and keep the R90 control separate."""
from symbolic_58203_integer_cocycle import E,p
def H(x):return (x>>1)^(x|2*x)
def run():
 assert all(E[(a+2)%10][j]==E[a][(j+31)%p] for a in range(10) for j in range(p))
 r=E[0];cost={s:sum(r[j]!=r[(j+s)%p] for j in range(p))for s in range(1,p)if s%5}
 print('distinct mod5 phases: minimum/equal-shift count/max Hamming separation of complete 155 west digits',min(cost.values()),sum(v==min(cost.values())for v in cost.values()),max(cost.values()))
 # A genuine R30 cap's first 155 original left-normalized digits become
 # purely dyadic eventually by its triangular marked-front induction.
 # Establish periodic clock for this prefix directly from the R30 orbit.
 z=1;m=(1<<p)-1;seen={};t=0
 while z not in seen:
  seen[z]=t;z=(4*z^(z|2*z))&m;t+=1
 print('width155 singleton left marked cap: preperiod,period',seen[z],t-seen[z]);assert not((t-seen[z])&(t-seen[z]-1))
 # Black B times use strobe gaps 3,5. On a dyadic residue cycle each
 # edge <=5; 5 times its modulus is reached by a simple cycle only
 # if all its edges are 5. The separate genuine R90 P2 control cannot
 # take these hazard returns in the first place.
 from pathlib import Path
 import sys;sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'ancestry_ultra'))
 # reuse the actual marked P2 R90 check without performing new rim work
 N=500;O=N+8;v=(1<<O)|sum(1<<(O+j)for j in range(1,2*N+2)if j%6 in(2,4));c=hits=0
 for t in range(N+1):
  assert v>>O&1==1-(t&1)
  if not t&1:c+=1;hits+=(v>>(O+1)&15)==11
  v=2*v^(v>>1)
 print('R90 true marked P2 control B occurrences / black ticks',hits,c)
if __name__=='__main__':run()
