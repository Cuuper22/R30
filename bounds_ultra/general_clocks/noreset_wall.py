"""Does a driven wall force a certified right inverse reset in every bounded
time window? Exclude all rows containing a synchronizer in a fixed 16-site
east prefix; compute the *entire* true R30 causal graph with free outer bit.
If a temporal cycle remains, classify its q variation instead of mistaking
an ether for a proof. R90 never resets, independently of the wall."""
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from spatial_certificate import trans
def analyze(p,n=16,r=30):
 N=1<<n;mask=N-1;P=len(p);S=15*np.ones(N,np.int16);X=np.arange(N)
 F=np.array([[trans(s,b,r) for b in(0,1)]for s in range(16)])
 for j in reversed(range(n)):S=F[S,(X>>j)&1]
 good=np.array([s.bit_count()>1 for s in map(int,S)]);A=X[good];ids=np.zeros(N,int)-1;ids[A]=np.arange(len(A));k=len(A);E=[[]for _ in range(k*P)];src=[];dst=[];at=np.arange(k)
 for u,v in enumerate(map(int,p)):
  for b in(0,1):
   sh=(A>>1)|(b<<(n-1));y=((2*A+v)^((A|sh)if r==30 else sh))&mask
   yes=good[y];src.append(at[yes]+u*k);dst.append(ids[y[yes]]+((u+1)%P)*k)
 u,v=np.concatenate(src),np.concatenate(dst);G=coo_matrix((np.ones(len(u),dtype=np.int8),(u,v)),shape=(P*k,P*k)).tocsr()
 _,cc=connected_components(G,directed=True,connection='strong');ix=cc[u]==cc[v];cores=np.unique(cc[u[ix]]);core=np.isin(cc,cores)
 if len(cores):
  sz=sorted([int((cc==a).sum())for a in cores],reverse=True)
  print('wall',p,'rule',r,'width',n,'bad row states',k,'temporal cyclic SCCs',len(cores),'sizes',sz[:10],flush=True)
 else:
  live=np.ones(P*k,np.bool_);D=0
  while live.any():old=live;live=(G@old.astype(np.int32))>0;D+=1
  print('wall',p,'rule',r,'width',n,'bad row states',k,'nilpotent: at most',D,'consecutive all-unsynchronized rows',flush=True)
if __name__=='__main__':
 for p in ('01','011','0011','00101','00111','0110000000110000001'):
  analyze(p);analyze(p,8,90)
