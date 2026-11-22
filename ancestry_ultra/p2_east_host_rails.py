"""Seek a recurrence one column east of a sustained nonabsorbing host:
a periodic east rail, or a co-moving/transformed same drive, would drop
the finite right length. Failure selects the exact classes/clock maps
visible through the existing fixed host, without adding any width."""
from p2_b_recur_host import np,edges,cc
from math import gcd
def test(n,N):
 S=np.load('/tmp/r30a_bhost_%s_%s.npy'%(n,N));a,b,h=edges(S,n);G,_,_=cc(a,b,N)
 ds=np.full(N,-1,int);ds[0]=0;q=[0];p=0
 for x in q:
  for y in G.indices[G.indptr[x]:G.indptr[x+1]]:
   if ds[y]<0:ds[y]=ds[x]+1;q.append(y)
   else:p=gcd(p,abs(ds[x]+1-ds[y]))
 print('host',N,'strobe graph period',p)
 for offset in (0,1):
  F=S if offset==0 else (2*S)^(S|S>>1) # highmost bit uncertain on black step
  rates=[];const=[]
  for j in range(n-offset):
   u=(F>>j)&1;r=max(min(float(u[ds%p==r].mean()),1-float(u[ds%p==r].mean()))for r in range(p))
   if r==0:const.append(j+1)
   rates.append((round(r,3),j+1))
  print('offset',offset,'phase-determined',const,'closest',sorted(rates)[:5])
 for j in range(1,n):
  # Direct eastward factor via a fixed lag strobe or complementarity:
  # If equal along all edges, the two temporal drivers are exact translates.
  xs=(S&1);tgt=(S>>j)&1
  for u in (xs,(2*S^(S|S>>1))&1):
   if np.all(u[a]==tgt[b]) or np.all(u[a]!=tgt[b]):print('lag1 spatial factor',j)
 # Find any exact affine binary read of adjoining five sites equal to a
 # shifted q at the same strobe. This can yield a translated coding, not
 # merely a periodic second center.
 L=[int(x)for x in S];base=(S&1).astype(bool)
 for d in range(1,n-4):
  w=(S>>d)&31;ok=True
  for x in np.unique(w):
   bs=base[w==x]
   if min(bs)!=max(bs):ok=False;break
  if ok:print('5-bit right block recovers current q',d+1)
if __name__=='__main__':
 test(25,24899);test(34,82754)

def recovery(n,N):
 S=np.load('/tmp/r30a_bhost_%s_%s.npy'%(n,N))
 for name,m in [('white',S),('black',np.unique(np.concatenate([((2*S)^(S|S>>1|(b<<(n-1))))%(1<<n)for b in(0,1)])))]:
  R=[]
  for j in range(n-1):
   x=(m>>j)&1;d=(m>>(j+1))[x==0];e=(m>>(j+1))[x==1]
   z=next((k for k in range(1,n-j)if not np.intersect1d(d%(1<<k),e%(1<<k)).size),None);R.append(z)
  print('host',N,name,'minimal right cells recovering each individual raw bit',R)
if __name__=='__main__':recovery(25,24899);recovery(34,82754)
