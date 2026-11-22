"""Do the *right* singleton rim clocks synchronize the absolute tip
contact times of deep east-packet sources (distinct from left-rim slots)?
An exact narrow image gives a mandatory collision class for actual B
launches; a broad image rules out trying to identify their labels by
dyadic rank alone. Iterate next-occupied normalized-depth gates."""
from symbolic_fixed_cut_rim import G,vf
import numpy as np
def go(rule=30,p=1<<18):
 z=1;w=[0]*p;bits=(1<<110)-1
 for t in range(p):w[t]=z;z=G(z,rule)&bits
 n=vf(z^1) if z!=1 else 109
 n=min(n,105)
 rows=[np.asarray([u>>j&1 for u in w],np.bool_) for j in range(n)]
 A=np.arange(p,dtype=np.int64);m=p-1
 print('rule',rule,'period',p,'safe normalized depth <',n)
 for j in range(2,n+1):
  good=rows[j-1]|rows[j-2]
  assert np.any(good)
  # f_j(t)=next tick at which the two cells directly east aren't both white.
  nexts=np.concatenate([np.full(p,p+np.flatnonzero(good)[0:1][0])])
  nexts[good]=np.flatnonzero(good)
  F=np.minimum.accumulate(nexts[::-1])[::-1];A=A[F&m]+(F&~m)
  admiss=np.zeros(p,np.bool_);admiss[A&m]=1
  lp=1
  while lp<p and not np.all(admiss==np.roll(admiss,lp)):lp*=2
  k=np.flatnonzero(admiss[:lp]);maxgap=max(np.diff(np.append(k,k[0]+lp)))
  if j<30 or j==n:
   print('depth',j,'image clock',lp,'occupied',len(k),'largest gap',maxgap,'max wait total',int(max(A-np.arange(p))),'slots',list(k[:8]),flush=True)
if __name__=='__main__':go();go(90,1024)
