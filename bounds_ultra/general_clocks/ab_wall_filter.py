"""The locked mixed AB predicate is local in the center itself. Test the
new readout on genuine R30 data and independently configured R90 clocks,
including the four stress clocks that the shrinking Lean hole must retain.
A discrepancy inside a locked rooted tile invalidates the Lean premise.
"""
from controls import r90
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[2]/'ancestry_ultra'))
from general_characteristic_d4 import field
A='01100000001';B='10000001';M=0x1010101110101011
def pred(c,t):return int(not c[t] and not(c[t-1] and(c[t+1]or not c[t+6])))
def run():
 for p in ('01','011','0011','00101',A+B):
  N=501;C,R=r90(p,N);c=list(C);k=sum(pred(c,t)!=((not c[t])and R[t])for t in range(40,N-6));print('true R90 exact input',p,'wall-filter mismatches on 455 interior ticks',k);assert k
 f=field(30,None,500);count=0
 for x in range(-60,61):
  c=[f(t,x)for t in range(501)];s=''.join(map(str,c))
  for t in range(1,484):
   if c[t-1]!=1 or not(M>>sum(f(t,x+j+1)<<j for j in range(6))&1):continue
   for w in(A,B):
    if s.startswith(w,t):
     for k in range(len(w)):assert pred(c,t+k)==int(not c[t+k] and f(t+k,x+1));count+=1
 print('actual R30 rooted ticks in eligible tiles all match',count)
 for p in('01','011','0011','00101',A+B):
  c=[int(p[t%len(p)])for t in range(510)];r=0;dr=[]
  for t,b in enumerate(c):dr.append(r&1);r=(2*r+b)^(r|(r>>1))
  n=sum(pred(c,t)!=int(not c[t] and dr[t]) for t in range(40,495));print('true finite east under R30 clamped clock',p,'wall-filter mismatches',n);assert (n==0)==(p==A+B)
if __name__=='__main__':run()
