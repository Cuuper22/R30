"""Test if the four/few surviving mature finite-strip inverse merger labels
have a genuine complete finite eastern landing and a long *prior* clock.
Enumerate true periodic k-pasts of a vacuum and then scan candidate finite
targets left. Restrict the proposed target's far extension to nonsynchronizing
words before testing both full rays. A positive is an exact lift; failure of
the sample is not a bounded-maturity certificate.
"""
import numpy as np,sys,random
from functools import lru_cache
from infinite_east_fibers import pairs
def neck(x):return min(x[j:]+x[:j] for j in range(len(x)))
@lru_cache(None)
def ppre(s):return {neck(Y) for c in (0,1) for _,Y in pairs(((),s),30,c)}
def vac(k):
 new={(0,)};seen=set(new)
 for _ in range(k):
  new={S for z in new for S in ppre(z)}-seen;seen|=new
 out=[]
 for s in seen:
  n=len(s);z=s;A=[0]*n
  for j in range(k):
   for i in range(n):A[i]|=z[i]<<j
   z=tuple(z[(i-1)%n]^(z[i]|z[(i+1)%n]) for i in range(n))
  assert not any(z)
  out.extend((A[(i+1)%n],A[i]) for i in range(n))
 assert len(out)==len(set(out))
 return np.array(out,dtype=np.uint64).T
def scan(A,B,w,k):
 for b in w:A,B=B,(B>>1)^((np.uint64(1<<(k-1)) if b else np.uint64(0)))^(A|B)
 return A,B
def inside(p,phase,k):return sum(int(p[(phase-k+1+j)%len(p)])<<j for j in range(k))
def f(s,b):return ((s&1)<<1)|(b^((s&1)|(s>>1)))
def go(p,ph,low,k,it,nmax=74):
 assert k<=63
 a,b=vac(k);rng=random.Random(43111);want=inside(p,ph,k)
 lowwords=[list(map(int,format(z,'020b'))) for z in low];best=0;hit=None;candidates=0
 for _ in range(it):
  # Use a finite target, from vacuum. Starting the two old pair paths in
  # 00/11 covers its possibilities exactly and never loses a true q fork.
  h,i=0,3;w=[]
  for n in range(rng.randrange(nmax+1)):
   vs=[v for v in(0,1)if f(h,v)!=f(i,v)]
   if not vs:break
   v=rng.choice(vs);w.append(v);h=f(h,v);i=f(i,v)
  L=rng.randrange(len(low));W=lowwords[L];s,t=h,i
  for v in W:s,t=f(s,v),f(t,v)
  if not ((s&1)==(t&1)==0 and s>>1!=t>>1):continue
  candidates+=1;A,B=scan(a,b,w+W,k);last=(A>>(k-1))&1
  good=B==want
  if np.any(good&(last==0))and np.any(good&(last==1)):
   mask=(1<<k)-1;hit=(len(w)+20,hex(int(''.join(map(str,w+W)),2)),
    [tuple(hex(int(z))for z in(a[i],b[i])) for v in(0,1)for i in [int(np.flatnonzero(good&(last==v))[0])]])
   break
  # Characterize actual maximum suffix of the past clock obtained by both
  # distinct immediate-white full predecessors on this target.
  score=min(max((k-int(z).bit_length() for z in B[last==v]^want),default=-1) for v in(0,1))
  best=max(best,score)
 print('exact finite east merged pair',p,ph,'K',k,'vacuum pasts',len(a),'sampled eligible',candidates,'longest paired past checked (excluding exact hit)',best,'full witness',hit,flush=True)
if __name__=='__main__':
 for k in(12,20,32):
  go('011',0,[0x6fdb,0x3efdb,0x86fdb,0xbefdb,0xc6fdb,0xcefdb,0xe6fdb,0xf8fdb],k,5000)
  go('00101',1,[0x6063b,0x7063b,0xe063b,0xf063b],k,5000)
