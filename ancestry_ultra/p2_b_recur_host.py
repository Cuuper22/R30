"""To force a bounded same-subtype opposite-B15 lag, remove transient and
q-periodic ultimate basins globally, then ask which remaining physical
components can shadow a phase-coded B cycle at all. Lift only the host that
still permits such excursions; emptiness upgrades cofinal to syndetic."""
from p2_two_tick_merger import mature,np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from collections import defaultdict,deque
from math import gcd
def edges(S,n,frozen=False):
 N=len(S);M=(1<<n)-1;A=[];B=[];H=[]
 for v in (0,1):
  x=((2*S)^(S|S>>1|(v<<(n-1))))&M; hv=np.where((x&15)==11,S&31,-1)
  for d in (0,1):
   y=((2*x+1)^(x|x>>1|(d<<(n-1))))&M;j=np.searchsorted(S,y);j=np.minimum(j,N-1);m=(S[j]==y);A.append(np.flatnonzero(m).astype(np.int32));B.append(j[m].astype(np.int32));H.append(hv[m].astype(np.int8))
 return tuple(np.concatenate(z)for z in(A,B,H))
def cc(a,b,N):
 G=csr_matrix((np.ones(len(a),np.uint8),(a,b)),shape=(N,N));_,C=connected_components(G,directed=True,connection='strong');return G,C,np.bincount(C)
def variable(S,G,C,sz):
 qq=[]
 for g in np.flatnonzero(sz>1):
  v=np.flatnonzero(C==g);D={int(v[0]):0};Q=list(D);p=0
  for a in Q:
   for y in G.indices[G.indptr[a]:G.indptr[a+1]]:
    y=int(y)
    if C[y]!=g:continue
    if y not in D:Q.append(y);D[y]=D[a]+1
    else:p=gcd(p,abs(D[a]+1-D[y]))
  H=defaultdict(set)
  for u,r in D.items():H[r%p].add(int(S[u])&1)
  if any(len(x)>1 for x in H.values()):qq.append(g)
 return qq
def test(S,n,level,cap):
 N=len(S);a,b,h=edges(S,n);G,C,sz=cc(a,b,N);qq=variable(S,G,C,sz);targets=[];res=[]
 for g in qq:
  m=(C[a]==g)&(C[b]==g);ia=a[m];ib=b[m];H=h[m];D=np.flatnonzero(C==g);I={int(u):i for i,u in enumerate(D)}
  j=np.array([I[int(u)] for u in ia],np.int32);k=np.array([I[int(u)]for u in ib],np.int32);d=len(D);bad=[];ttl=[]
  for z in range(4):
   # phase sign for subtype 10 fixed0; 17 and26 arbitrary; both marks overall reversible
   sg=np.where(H==10,0,np.where(H==17,z&1,z>>1));A=[];B=[]
   for p in (0,1):
    u=(H<0)|(sg==p);A.append(j[u]+d*p);B.append(k[u]+d*(1-p))
   ga,gb=np.concatenate(A),np.concatenate(B);GC,K,nums=cc(ga,gb,2*d);cy=np.flatnonzero(nums>1)
   if len(cy):bad.append((z,sorted(map(int,nums[cy]),reverse=True)[:3]))
   else:
    # Exact maximum black-strobe length of a path in this DAG.
    ind=np.bincount(gb,minlength=2*d);adj=[[]for _ in range(2*d)]
    for x,y in zip(ga,gb):adj[x].append(y)
    q=deque(np.flatnonzero(ind==0));dist=[0]*(2*d)
    while q:
     x=q.popleft()
     for w in adj[x]:
      dist[w]=max(dist[w],dist[x]+1);ind[w]-=1
      if not ind[w]:q.append(w)
    ttl.append(max(dist))
  print('n',n,'global q-variable host',d,'phase-coded B cycles',bad,'max transient among empty branches',max(ttl,default=None),flush=True)
  if bad:targets.append(S[D])
  np.save('/tmp/r30a_bhost_%d_%d.npy'%(n,d),S[D])
 return targets
def run():
 S=mature(25);V=test(S,25,0,0)
 for n in range(26,37):
  W=[]
  for s in V:
   X=np.sort(np.concatenate((s,s+(1<<(n-1)))))
   if len(X)>450000:print('host lift cap',len(X),flush=True);continue
   W+=test(X,n,0,0)
  V=W
  if not V:break
if __name__=='__main__':run()
