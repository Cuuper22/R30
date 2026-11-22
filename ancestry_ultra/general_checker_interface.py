"""Test the two-sided marked phase via the infinite checker canonicalization
of the finite stripe seeds. If traces separate all finite interface defects,
seek a nonuniform observer. Otherwise isolate the first unresolved pair and
test whether its discrepancy forms an escaping traveling defect."""
from collections import defaultdict
from general_characteristic_d4 import field
def plane(D,s,k):
 off=k+D+5;
 full=sum(1<<(off+i)for i in range(D+1,k+D+3)if not i%2)
 return full|(s<<(off-D)),off
def trace(z,o,k,r=30):
 x=0
 for i in range(k):
  x|=(z>>o&1)<<i;z=(z<<1)^((z|z>>1)if r==30 else z>>1)
 return x
def classify(D,lim=(100,250,500,1000,3000)):
 batches=[list(range(1<<(2*D+1)))];last=0
 for k in lim:
  full,o=plane(D,0,k)
  out=[]
  for S in batches:
   bins=defaultdict(list)
   for s in S:bins[trace(full|(s<<(o-D)),o,k)].append(s)
   out.extend(T for T in bins.values()if len(T)>1)
  batches=out
  print('fixed vacuum-west/checker-east collar',D,'ticks',k,'distinct words',2**(2*D+1)-sum(len(a)-1 for a in out),'unresolved states',sum(map(len,out)),flush=True)
  if not batches:break
 return batches
def checks():
 N=500;C=field(30,None,N);full,o=plane(0,1,N);z=full
 for t in range(N+1):
  for x in range(-t,t+1):
   assert (z>>(o+x)&1)==(C(t,x) if x<t else 1-x%2)
  z=(2*z)^(z|z>>1)
 print('published stripe limit in all 251001 marked cone cells through 500; exact checker outside x<t')
 for p in ('01','011','00101'):
  R=field(90,p,N);D=7
  assert all(R(t,0)==int(p[(t-1)%len(p)])for t in range(1,N+1))
  # Actual perturbation on top of these actual same-pattern rooted R90
  # controls, and likewise on ANY common vacuum-checker background.
  z=(1<<(N+D))|(1<<(N-D))
  for t in range(N+1):
   assert not(z>>N&1);z=(2*z)^(z>>1)
  base,o=plane(D,0,N)
  assert trace(base,o,N,90)==trace(base^(1<<(o-D))^(1<<(o+D)),o,N,90)
  print('Rule90 true',p,'and separate checker-interface pair: symmetric +/-7 defects hide forever')
if __name__=='__main__':
 checks()
 for D in (5,7,8):classify(D)
