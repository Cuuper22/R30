"""Determine exactly what older 3/5 words the fixed 58,203-state true
east host remembers. No width is lifted. A small deterministic remainder
gives the full recurrent tile language for the marked-west argument; if
its branches proliferate, extract a certified shortest forbidden word
and the actual exclusions beyond isolated shorts."""
from symbolic_q221_lift import gethost,edges,np
from collections import deque
def run(cap=3500):
 S=gethost(25,58203);A,B,h=edges(S,25)
 N=len(S);D=B.reshape(4,N).T;haz=h[:N]>=0;assert all(np.array_equal(A[i*N:(i+1)*N],np.arange(N))for i in range(4))
 def step(V,k):
  v=V
  for i in range(1,k+1):
   if not len(v):return v
   v=np.unique(D[v]);v=v[haz[v] if i==k else ~haz[v]]
  return v
 first=np.flatnonzero(haz).astype(np.int32);sig=lambda v:v.tobytes()
 I={sig(first):0};Q=deque([(first,'')]);Z=[];missing=[];sz=[]
 while Q and len(I)<cap:
  V,w=Q.popleft();out=[];sz.append((len(V),w))
  for g in (3,5):
   u=step(V,g);p=w+str(g)
   if not len(u):
    if not w.endswith('3')or g!=3:missing.append(p)
    out.append(-1);continue
   k=sig(u.astype(np.int32))
   if k not in I:I[k]=len(I);Q.append((u,p))
   out.append(I[k])
  Z.append(out)
 print('complete',not Q,'subsets',len(I),'expanded',len(Z),'pending',len(Q),'shortest forbidden beyond isolation',sorted(missing,key=lambda s:(len(s),s))[:25],flush=True)
 print('range surviving state counts',min(sz),max(sz),'maximum BFS depth',max(len(w)for _,w in sz),flush=True)
 if not Q:
  # Minimize deterministic language; all nonempty subsets are accepting.
  Z.append([len(Z)]*2);Z=np.array(Z);Z[Z<0]=len(Z)-1;C=np.array([0]*(len(Z)-1)+[1]);
  while True:
   S1=[(int(C[j]),int(C[a]),int(C[b]))for j,(a,b)in enumerate(Z)]
   ids={};cc=np.array([ids.setdefault(u,len(ids))for u in S1])
   if len(set(cc))==len(set(C)):break
   C=cc
  print('minimal classes including reject',len(set(cc)), 'class representative transitions',[(int(cc[a]),int(cc[b]))for j,(a,b)in enumerate(Z) if j==np.flatnonzero(cc==cc[j])[0]],flush=True)
  import json
  trans=[(int(cc[a]),int(cc[b]))for j,(a,b)in enumerate(Z) if j==np.flatnonzero(cc==cc[j])[0]]
  return int(cc[0]),int(cc[-1]),trans
if __name__=='__main__':
 import json
 from pathlib import Path
 s,b,g=run();Path(__file__).with_suffix('.json').write_text(json.dumps({'start':s,'reject':b,'shortlong':g}))
