"""Compare the marked inverse-parser paths at neighboring physical ages.
If paths cross, a coherent dyadic return argument is invalid. If they are
ordered, identify genuine coalescences prior to midpoint, including all
four finite-right clamped drives and the original R30/R90 singleton."""
import numpy as np
from spatial_certificate import trans
def data(p,N,rule):
 c=None if p is None else [1]+[int(p[t%len(p)])for t in range(N)]
 x=1;R=[]
 for t in range(N+1):
  R.append(x)
  x=x^((2*x|4*x) if rule==30 else 4*x) # right-normalized full row
  if c is not None and t<N:
   # Only equal to true clamped right at normalized indices 0..t+1.
   # Whole baseline row first evolved with actual c[t] already present.
   x=(x&((1<<(t+1))-1))|(c[t+1]<<(t+1))
 return R
def run(p,rule,N=800):
 R=data(p,N,rule);start=np.arange(N+1);age=start.copy();S=np.full(N+1,15,int);hit=np.full(N+1,-1);merges=np.full(N,-1)
 F=np.array([[trans(s,b,rule)for b in (0,1)]for s in range(16)])
 # Restrict to the cohort still strictly EAST of the physical center.
 for j in range(N+1):
  valid=(age>j);hit[(hit<0)&~valid]=j
  if not np.any(valid):break
  b=np.array([(R[int(t)]>>j)&1 for t in age]);v=F[S,b];done=(v&(v-1))==0
  S=np.where(valid&done,15,np.where(valid,v,S));age-=valid&done
  assert np.all(np.diff(age)>=0)
  ix=(merges<0)&valid[:-1]&valid[1:]&(np.diff(age)==0)&(S[:-1]==S[1:])
  merges[ix]=j+1
 late=np.arange(N//2,N);m=merges[late];print('clock',p or 'singleton','rule',rule,'ordered shared-center first crossing all starts',bool(np.all(np.diff(hit)>=0)),'ratio landed-age/start t=200,400,800',[round(hit[k]/k,4)for k in (200,400,800)],'adjacent coalesced before center/later-half',int((m>=0).sum()),len(m),'not reached before center',int((m<0).sum()),flush=True)
if __name__=='__main__':
 for p in (None,'01','011','0011','00101'):run(p,30);run(p,90)
