"""General-P finite prefix vs temporal read entropy. Observed words include
R1 at EVERY white phase of a strobe, in chronological order; omitted black
phases cannot influence the required R30 west head. Multiplicities of
external-bit paths are never counted as distinct observed words. A finite
sofic projection is an upper model for the infinite rooted orbit.
If not determinized to completion, return explicit finite-word bounds,
not an alleged spatial or temporal entropy rate of the singleton."""
import sys,os,json,math
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix,csr_matrix
from scipy.sparse.csgraph import connected_components
import r30fast
RULES=('01','011','0011','00101')
def counts(widths=(8,12,16,18,20,22)):
 for p in RULES:
  for n in widths:
   m,H=r30fast.general_p_hosts(p,n=n,rule=30);hv=[v for v in H if v.q_variable]
   print('spatial',p,n,'finite mature count',m,'per-site log-count',round(math.log2(m)/n,5),'q-variable hosts (size,absorbing)',[(v.size,v.absorbing)for v in hv], 'R90 full',1<<n,flush=True)
def graph(p,n,d=None):
 m,H,S=r30fast.general_p_hosts(p,n=n,rule=30,return_states=True)
 V=next(a for a in H if a.size==d)if d else max([a for a in H if a.q_variable],key=lambda a:(a.absorbing,a.size))
 st=np.sort(np.frombuffer(S[V.comp_id],dtype=np.uint64));N=len(st);mask=(1<<n)-1
 F=len(p);X=[st];q=np.zeros(N,np.uint8)
 for c in map(int,p):
  if c==0:q=2*q+(X[0]&1).astype(np.uint8)
  Z=[]
  for x in X:
   l=2*x+c;k=x|(x>>1);Z.extend(((l^k)&mask,(l^(k|(1<<(n-1))))&mask))
  X=Z
 D=[]
 for x in X:
  t=np.minimum(N-1,np.searchsorted(st,x));D.append(np.where(st[t]==x,t,N))
 D=np.stack(D,axis=1).astype(np.int32);return st,D,q
def exact_dfa(p,n,d=None,cap=16000,mem=260):
 st,T,L=graph(p,n,d);N=len(st);B=1<<p.count('0');start=np.arange(N,dtype=np.int32)
 # This is a boundary-sensitive NFA with many duplicate paths; determinize once.
 # Capped subset caching is by literal set, with no hashing-only equality.
 z=start.tobytes();I={z:0};V=[start];A=[];layers=[0];reach=1;used=len(z);done=0
 while done<len(V) and len(V)<cap and used<mem*1024*1024:
  v=V[done];e=[]
  for ch in range(B):
   w=v[L[v]==ch]
   if not len(w):e.append(-1);continue
   w=np.unique(T[w]);w=w[w!=N];s=w.tobytes()
   if not len(w):e.append(-1);continue
   if s not in I:I[s]=len(V);V.append(w);used+=len(s)
   e.append(I[s])
  A.append(e);done+=1
  if done==reach:layers.append(done);reach=len(V)
  if done%2500==0:print('DFA building',p,n,N,'expanded',done,'known',len(V),flush=True)
 A=np.array(A,dtype=int);M=len(V);ii,jj=np.nonzero(A>=0);rows=ii;cols=A[ii,jj];G=coo_matrix((np.ones(len(ii)),(rows,cols)),shape=(M,M)).tocsr()
 # For lower bound, retain the known graph and use max f with G^k1>=2^m*1
 # on a cyclic SCC after compact numerical estimate when full; bounds below.
 _,C=connected_components(G,directed=True,connection='strong');sz=np.bincount(C)
 def pf(G,nit=1200):
  if G.shape==(1,1):return [float(G[0,0])]*2
  v=np.ones(G.shape[0]);lo=1;hi=B
  for i in range(nit):
   z=G.dot(v)+v;rat=z/v-1;lo=max(lo,min(rat));hi=min(hi,max(rat));v=z/max(z)
   if hi<lo+1e-10:break
  return lo,hi
 bd=[]
 for cc in np.flatnonzero(sz>1):
  vv=np.flatnonzero(C==cc);bd.append((pf(G[vv][:,vv]),len(vv)))
 loopmax=max(G.diagonal(),default=0);elo=max([loopmax]+[t[0][0]for t in bd]);ehi=max([loopmax]+[t[0][1]for t in bd]);full=(done==M)
 # All factor counts of the projected SCC start at the whole state set.
 wave={0:1};count=[]
 for k in range(1,32):
  if any(i>=done for i in wave):break
  new={}
  for i,z in wave.items():
   for j in A[i]:
    if j>=0:new[j]=new.get(j,0)+z
  wave=new;count.append(sum(wave.values()))
 upper=min([math.log2(z)/(i+1)for i,z in enumerate(count)]+[math.log2(B)])
 print('temporal',p,'width',n,'host',N,'complete DFA',full,'expanded/known',done,M,'word counts k=1..',count,'max SCC eigen brackets',round(elo,9),round(ehi,9),'log2 finite-word upper/strobe',round(upper,8),flush=True)
 if full or len(count)>3:
  Path(__file__).with_name('dfa_%s_n%d_%d.json'%(p,n,N)).write_text(json.dumps({'p':p,'n':n,'host':N,'complete':full,'expanded':done,'discovered':M,'alphabet':B,'factors':count,'adjacency':A.tolist()}))
if __name__=='__main__':
 if len(sys.argv)==1:counts()
 else:exact_dfa(sys.argv[1],int(sys.argv[2]),int(sys.argv[3])if len(sys.argv)>3 else None)
