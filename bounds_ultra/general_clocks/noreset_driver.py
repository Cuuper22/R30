"""Classify the possible recurrent wall clocks under a uniformly
non-synchronizing 16-site right prefix, with BOTH the wall and far boundary
free. A finite list gives a uniform forbidden-wall criterion for arbitrary P.
Positive branching demands projecting its actual wall labels before claiming that."""
import itertools, numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from spatial_certificate import trans
def allclocks(n,r):
 N=1<<n;mask=N-1;F=np.array([[trans(s,b,r) for b in(0,1)]for s in range(16)])
 X=np.arange(N);S=15*np.ones(N,np.int16)
 for j in reversed(range(n)):S=F[S,(X>>j)&1]
 ok=np.array([s.bit_count()>1 for s in map(int,S)]);A=X[ok];ids=np.full(N,-1,int);ids[A]=np.arange(len(A));k=len(A)
 es=[{}for _ in A]
 for c,b in itertools.product(range(2),repeat=2):
  sh=(A>>1)|(b<<(n-1));y=((2*A+c)^((A|sh)if r==30 else sh))&mask
  for i in np.where(ok[y])[0]:es[i][ids[y[i]]]=c
 u,v=zip(*[(i,int(j))for i,a in enumerate(es)for j in a]);G=coo_matrix((np.ones(len(u)),(u,v)),shape=(k,k)).tocsr();_,cc=connected_components(G,directed=True,connection='strong')
 D={}
 for i,a in enumerate(es):
  y={j:b for j,b in a.items()if cc[i]==cc[j]}
  if y:D.setdefault(cc[i],{})[i]=y
 out=[]
 for Q in D.values():
  if all(len(y)==1 for y in Q.values()):
   i=next(iter(Q));c='';q=''
   for _ in Q:
    q+=str(A[i]&1);i,a=next(iter(Q[i].items()));c+=str(a)
   w=min(c[h:]+c[:h]for h in range(len(c)));out.append((len(Q),w,c,q))
  else:out.append((len(Q),'branch',sum(map(len,Q.values())),None))
 print('free wall',n,r,'SCCs',sorted(out)[:25],flush=True)
 # Every long noreset word spends all but bounded many steps in these cores.
 return A,es,D,cc
if __name__=='__main__':
 for n in (4,5,6,7,8,12,16):allclocks(n,30)
 allclocks(8,90)
