"""Does the finite *whole* singleton row scatter all true vacuum-tail
antecedents into its marked western vacuum for a linear part of its age?
Unlike a free one-step scanner at each height, use the exact global k-tail
catalog. If the threshold moves toward the full old cone, seek induction;
when a non-vacuum escapes, keep its two tail labels and center clock.
"""
from finite_merge_probe import ppre
from functools import lru_cache
@lru_cache(None)
def vs(k):
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
 return tuple(out)
def root(t):
 z=1;C=[]
 for i in range(t+1):
  C.append(z>>i&1)
  if i<t:z=4*z^(2*z|z)
 return z,C
def step(S,w,k):
 h=1<<(k-1)
 for b in w:
  B=b*h
  S={(c, (c>>1)^B^(a|c)) for a,c in S}
 return S
def probe(t,k):
 z,C=root(t);seed=set(vs(k));w=[z>>j&1 for j in reversed(range(2*t+1))]
 s=step(seed,w[:t],k);mask=sum(C[t-k+j]<<j for j in range(k))
 # after target x=1, second word is the oldest..latest past center at x0.
 sf={v for v in s if v[1]==mask}
 o=step(s,w[t:],k);f=step(sf,w[t:],k)
 # once enough zeros read, each remaining pair is strictly in a spatially
 # periodic left tail; can use size 4^k as universal threshold, or the
 # exact tiny stabilization/known membership in the vacuum catalog.
 def close(V):
  for _ in range(max(5000,100*k)):
   if V<=seed:break
   V=step(V,[0],k)
  if not V<=seed:raise ValueError('remaining spatial transient')
  return V
 o=close(o);f=close(f)
 def last(V):
  # For non-vacuum left histories, first nonzero ancestor is all-black,
  # visible simultaneously at both stack sites at the most recent set bit.
  return k-max((a|b).bit_length()for a,b in V)+1
 return len(seed),len(s),len(sf),len(o),len(f),last(o),last(f)
if __name__=='__main__':
 for t in (12,20,40,60,80,120,250,500):
  for k in sorted(set(x for x in (min(12,t),min(20,t),min(40,t),min(60,t),min(80,t)) if x<=t)):
   print('marked scatter, true age,depth, (#unrestricted tails/#distinct center pairs/#actual-center pairs/#left tails/#left tails actual-center/first unconditioned nonvacuum depth/first matched nonvacuum depth; k+1=none)',t,k,probe(t,k),flush=True)
