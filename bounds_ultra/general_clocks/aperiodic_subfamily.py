"""Do finite-host restrictions + the marked periodic-island ceilings force
vanishing word complexity? A pair of equal-length return words provides a
positive-entropy family having a uniform bound on powers of EVERY period.
This is a graph witness, not a realization in an infinite physical east."""
import json
from pathlib import Path
from collections import deque
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
import numpy as np
def loops(p,n):
 d=json.loads(next(Path(__file__).parent.glob('dfa_%s_n%d_*.json'%(p,n))).read_text());A=d['adjacency'];E=[(i,j)for i,v in enumerate(A)for j in v if j>=0];u,v=zip(*E);G=coo_matrix((np.ones(len(E)),(u,v)),shape=(len(A),len(A))).tocsr()
 _,cc=connected_components(G,directed=True,connection='strong')
 opts=[]
 for i,v in enumerate(A):
  I=[k for k,j in enumerate(v)if j>=0 and cc[i]==cc[j]]
  if len(I)>=2:opts.append((i,I))
 best=None
 for i,I in opts[::max(1,len(opts)//60)]:
  dist={i:''};Q=deque([i])
  while Q:
   j=Q.popleft()
   for k in G[:,j].nonzero()[0]:
    if cc[k]!=cc[i]or k in dist:continue
    dist[k]=str(A[k].index(j))+dist[j];Q.append(k)
   if all(A[i][u] in dist for u in I):break
  pairs=sorted((len(dist[A[i][u]])+1,str(u)+dist[A[i][u]])for u in I);x,y=pairs[0][1],pairs[1][1]
  t=(len(x)+len(y),i,x+y,y+x);best=t if best is None else min(best,t)
 L,i,U,V=best
 for e in (U,V):
  j=i
  for b in e:j=A[j][int(b)]
  assert j==i
 print(p,n,'dfa state',i,'length',L,'U,V',U,V,'family entropy lower bits/physical tick',1/(2*L*len(p)),flush=True)
if __name__=='__main__':
 for p,n in [('01',25),('011',18),('0011',18),('00101',18)]:loops(p,n)
