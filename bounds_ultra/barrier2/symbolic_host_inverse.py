"""Can the new complete recurring host force actual previous center clocks
without assuming them, so that a periodic tail extends backwards to the
origin? Compute every possible old eastern two-bit boundary, not an
incorrect vacuum fill. For surviving ambiguity identify the responsible
right-prefix patterns; a unanimous branch selects a genuinely forced step."""
from symbolic_q221_lift import *
def pre(S,n):
 F=[]
 for state in range(4):
  a,b=np.full(len(S),state&1,dtype=np.int64),np.full(len(S),state>>1,dtype=np.int64)
  for j in range(n-1,-1,-1):a,b=((S>>j)&1)^(a|b),a
  F.append(a)
 return np.min(F,axis=0),np.max(F,axis=0)
def run(n,d):
 from p2_past_head_invert import js
 S=gethost(n,d)
 for p,X in [(0,S),(1,js(S,0,n))]:
  for depth in(8,14,n):
   V=np.unique(X&((1<<depth)-1));mn,mx=pre(V,depth);amb=mn!=mx
   print(d,p,depth,'n,forcing previous unequal,ambiguous,forcing equal',len(V),int(np.sum((~amb)&(mn==1-p))),int(amb.sum()),int(np.sum((~amb)&(mn==p))),'eg amb',[hex(int(k))for k in V[amb][:1]],flush=True)
if __name__=='__main__':
 for n,d in [(25,58203),(25,24899),(34,82754)]:run(n,d)
