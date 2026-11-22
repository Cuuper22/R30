"""Test the complete paired-five host 221 by exact one-cell extension.
If every variable lift disappears, finite marked west eliminates this host
at any onset. Otherwise use the smallest persistent lift's actual path
language for the shared-west OR argument, not the unfiltered 3/5 code."""
from pathlib import Path
import sys
A=Path(__file__).resolve().parents[2]/'ancestry_ultra';sys.path.insert(0,str(A))
from p2_b_recur_host import edges,cc,variable,np,mature
from math import gcd
def host221():
 S=mature(25);a,b,h=edges(S,25);G,C,sz=cc(a,b,len(S));return S[C==next(g for g in variable(S,G,C,sz) if sz[g]==221)]
def lift(S,n):
 V=np.sort(np.concatenate((S,S+(1<<(n-1)))));a,b,h=edges(V,n);G,C,sz=cc(a,b,len(V));cs=variable(V,G,C,sz);return [V[C==j]for j in cs], sorted(map(int,sz[sz>1]),reverse=True)[:10]
# Cache files are optional; reconstruct every named component from the update.
from functools import lru_cache
CHAINS=[[16429,21859,19133,21138,26252,32780,41064,52480,66918,82754,101805,122857,157438,204086,264368],[24899,38337,59251,91029,131265,203375,315078],[221,229],[58203]]
@lru_cache()
def gethost(n,d):
 for f in (Path('/tmp/r30a_bhost_%d_%d.npy'%(n,d)),Path('/tmp/r30b_%d_%d.npy'%(n,d))):
  if f.exists():return np.load(f)
 if n==25:
  S=mature(25);a,b,_=edges(S,25);G,C,sz=cc(a,b,len(S));return S[C==next(j for j in variable(S,G,C,sz)if sz[j]==d)]
 prev=next(l[n-26]for l in CHAINS if len(l)>n-25 and l[n-25]==d)
 return next(s for s in lift(gethost(n-1,prev),n)[0] if len(s)==d)
def freq(V,n):
 a,b,_=edges(V,n);G,C,sz=cc(a,b,len(V))
 for k in np.flatnonzero(sz>1):
  D={int(np.flatnonzero(C==k)[0]):0};E=list(D);p=0
  for u in E:
   for v in G.indices[G.indptr[u]:G.indptr[u+1]]:
    if C[v]!=k:continue
    if v not in D:D[v]=D[u]+1;E.append(v)
    else:p=gcd(p,abs(1+D[u]-D[v]))
  q=[set()for _ in range(p)]
  for u,d in D.items():q[d%p].add(int(V[u])&1)
  if max(map(len,q))!=1:continue
  s=''.join(str(next(iter(c)))for c in q);pi=next(j for j in range(1,p+1)if p%j==0 and s==s[:j]*(p//j))
  print('states',int(sz[k]),'graph period',p,'least white q period',pi,'word up to rotation',s[:pi])
if __name__=='__main__':
 from p2_initialized_transfer import single,control
 S=host221();print('initial 221-state component first packed white row',hex(int(S[0])))
 for n in(26,27):
  W,Z=lift(S,n);print(n,len(S),'nontrivial SCCs',Z,'q-variable',[len(w)for w in W],flush=True)
  if W:S=W[0]
  else:freq(np.sort(np.concatenate((S,S+(1<<(n-1))))),n)
 single();control()
