"""Test all-depth, phase-aware inverse propagation on right q language.
If its entire cyclic envelope misses a mandatory true marked-front word,
we can eliminate that host for every onset residue. If it closes including
every marked word, the finite-height inverse factor does not separate the mark."""
import json,sys
from pathlib import Path
import numpy as np
def phase_init(p,k,A,rule):
 P=len(p);C=list(map(int,p));m=(1<<k)-1;U=[set()for _ in p]
 for a in range(P):
  c=sum(C[(a+j)%P]<<j for j in range(k));cc=sum(C[(a+j+1)%P]<<j for j in range(k))
  if rule==90:U[a].update((i<<k)|c for i in range(1<<k));continue
  V={(0,tuple())}
  for b in range((a+k+P-1)//P):
   Z=set()
   for v,w in V:
    for q,t in enumerate(A[v]):
     if t<0:continue
     e=tuple(map(int,format(q,'0%db'%p.count('0'))));i=0;h=[]
     for j in range(P):
      n=0
      if C[j]==0:n=e[i];i+=1
      h.append(C[(j+1)%P]^(C[j]|n))
     Z.add((t,w+tuple(h)))
   V=Z
  for _,w in V:
   b=sum(v<<j for j,v in enumerate(w[a:a+k]));U[a].add(c|(b<<k))
 return [np.array(sorted(v),dtype=np.int32)for v in U]
def slide(U,k,rule):
 m=(1<<k)-1;ps=[];AA=(m>>1)|((m>>1)<<k);N=1<<(2*k)
 for a,V in enumerate(U):
  W=U[(a+1)%len(U)];S=set();T=np.zeros(N,dtype=bool);T[W]=True
  e=V&m;b=V>>k;f=(b>>1)^((e|b)if rule==30 else e);lo=(V>>1)&AA
  Z=[]
  for c in (0,1):
   for d in (0,1):
    U0=lo|(c<<(k-1))|(d<<(2*k-1));yes=T[U0]
    Z.append(b[yes]|((f[yes]^(d<<(k-1)))<<k))
  ps.append(np.unique(np.concatenate(Z)))
 return ps
def go(p,k,n,rule,limit=140):
 a=next(Path(__file__).parent.glob('dfa_%s_n%d_*.json'%(p,n)));A=json.loads(a.read_text())['adjacency'];U=phase_init(p,k,A,rule);seen={};hist=[];full0=None
 for d in range(1,limit+1): # pair center at -d, east at 1-d
  sig=tuple(v.tobytes()for v in U)
  if sig in seen:break
  if sum(map(len,U))>1800000:print('cap',p,k,n,rule,d,flush=True);return
  seen[sig]=d;hist.append(U);U=slide(U,k,rule)
  if full0 is None and all(0 in set(x) for x in U):full0=d+1
 else:print('unclosed',p,k,n,rule,len(hist),'last sizes',[len(x)for x in U],flush=True);return
 s=seen[sig];l=d-s;H=[[(set(map(int,v)))for v in u]for u in hist[s-1:d-1]]
 # True normalized marked front: exact single-cell dynamics, in low k+4 normalized bits.
 # Every depth d, query windows at actual age d+i surrounding first arrival.
 # Saturated phase-zero coordinates from periodic Q don't prescribe onset residue, so test all.
 m=(1<<(k+8))-1;X=1;phase={};L=0;tt=0;rows=[]
 while X not in phase:
  phase[X]=tt;rows.append(X);tt+=1;X=((4*X)^((2*X|X) if rule==30 else X))&m
 mu=phase[X];pi=tt-mu
 from math import lcm
 cycles=lcm(l,pi,len(p));bad=[];start=max(s,mu+4)+5
 def row(t):return rows[t] if t<tt else rows[mu+(t-mu)%pi]
 def bit(t,x):j=t+x;return row(t)>>j&1 if j>=0 else 0
 for off in range(len(p)):
  bad.append(None)
  for dep in range(start,start+cycles):
   if bad[-1]:break
   for i in range(-3,3):
    t=dep+i;ev=sum(bit(t+j,1-dep)<<j for j in range(k));cv=sum(bit(t+j,-dep)<<j for j in range(k));u=ev|(cv<<k)
    if u not in H[(dep-s)%l][(t+off)%len(p)]:bad[-1]=(dep,i,u);break
 print('clock',p,'rule',rule,'n',n,'height',k,'eventual envelope predepth/period',s,l,'states/phase',[len(v)for v in U],'first all-vacuum throughout phases',full0,'rim excluding offsets',bad,flush=True)
if __name__=='__main__':
 k=int(sys.argv[1]);r=int(sys.argv[2]) if len(sys.argv)>2 else 30
 for p,n in [('01',25),('011',18),('0011',18),('00101',18)]:go(p,k,n,r)
