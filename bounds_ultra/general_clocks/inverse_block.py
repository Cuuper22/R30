"""Can coupled true inside-column histories restore periodic-tail
synchronization when the one-step map admits alternate ether preimages?
Only entering pair states reachable from the allowed center and q histories
through a genuine spatial inverse of any finite target prefix are tested."""
from periodic_islands import ref
import numpy as np
from collections import defaultdict
def test(p,z,s,words):
 o,E=ref(p,z);D=len(E[0]);L=len(E);m=(1<<s)-1;N=(m+1)**2;assert s%L==0 and not o
 # layers at ages -1 .. -s; L_r at physical center, M_r at -1.
 def head(v):
  c=tuple(map(int,p))*len(v);y=[];i=0
  for x in v:
   obs=iter(map(int,format(x,'0%db'%p.count('0'))))
   for b in p:
    y.append(c[(i+1)%len(c)]^(c[i]|(next(obs)if b=='0'else 0)));i+=1
  return int(''.join(map(str,y)),2) # last past tick is bit0
 c=int(p*(s//len(p)),2);st=[(c<<s)|head(v)for v in words]
 def trans(v,b):
  a=v>>s;d=v&m;return (d<<s)|(((d<<1|b)&m)^(a|d))
 W=np.arange(N,dtype=np.int32);F=[trans(W,b)for b in (0,1)]
 # track exact spatial locations modulo D, not just the start of the first period.
 R=[set()for _ in range(D)];Q=[(0,v)for v in st]
 for j,v in Q:R[j].add(v)
 for j,v in Q:
  k=(j+1)%D
  for G in F:
   w=int(G[v])
   if w not in R[k]:R[k].add(w);Q.append((k,w))
 def expected(j):return (sum(E[-r%L][(j-1)%D]<<r0 for r0,r in enumerate(range(1,s+1)))<<s)|sum(E[-r%L][j%D]<<r0 for r0,r in enumerate(range(1,s+1)))
 # pull synchronizing classes backward from genuine reference states.
 T=np.zeros((D,N),np.bool_)
 for j in range(D):T[j,expected(j)]=True
 for i in range(N*D):
  A=np.stack([T[(j+1)%D, F[E[0][j]]]for j in range(D)])
  if np.array_equal(T,A):break
  assert np.all(A|~T);T=A
 non=[(j,v)for j,V in enumerate(R)for v in V if not T[j,v]]
 print(p,'s',s,'prefix-reachable',sum(map(len,R)),'nonlocking',len(non),'sync depth',i,'rival',non[:1],flush=True)
 return non
if __name__=='__main__':
 from itertools import product
 for s in (4,8):
  for q in (1,3):test('0011',(q,),s,list(product((1,3),repeat=s//4)))
