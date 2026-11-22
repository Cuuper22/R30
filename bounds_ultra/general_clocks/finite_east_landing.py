"""Compare genuine equal full-eastern landings with distinct remote east
tails. Tests whether the alternating outer preimage synchronizer can be
iterated through the lost outer bit; if not, compute actual ambiguity cones.
Physical coordinates of known target: x=1..R, zero at x>R.
For the four clamps start with strict right r=1 so rightmost is t+1.
"""
from spatial_certificate import trans
def prefixes():
 for r in (30,90):
  for d in(0,1):
   s=15
   for b in(0,0,1,0,d):s=trans(s,b,r)
   print('reset right-to-left 0010'+str(d),'r',r,'final pair mask',s)
   assert (s.bit_count()==1)==(r==30)
def partial(r,x,n,S=15):
 for j in range(n-1,-1,-1):
  S=trans(S,(x>>j)&1,r)
  if S.bit_count()==1:return j
 return -1
def runs(r,p,N=500):
 z=1;v=1;L=[];F=[]
 for t in range(N+1):
  if p:
   right=v;c=int(p[t%len(p)])
  else:
   right=z>>(t+1);c=z>>t&1
  if right.bit_length()>=2:
   n=right.bit_length();j=partial(r,right,n,9 if r==30 else 15)
   L.append((t,n,j))
   if not(right>>(n-2)&1)and n>=3 and r==30:assert j>=n-3
   # Rightmost real black moves right exactly one at each step for
   # an initial nonzero finite strict east (or full-space singleton).
   if len(L)>=2 and L[-2][1]+1==n:
    assert ((right>>(n-2))^(old>>(n-3)))&1==(1 if r==30 else 0)
   old=right
  if r==30:v=(2*v+c)^(v|(v>>1));z=4*z^(2*z|z)
  else:v=(2*v+c)^(v>>1);z=4*z^z
 ds=[n-1-j for t,n,j in L if j>=0]
 print('finite true east',p or 'singleton','r',r,'ages resolved through x1',sum(j>=0 for _,_,j in L),'/',len(L),'largest observed right-rim resolving depth',max(ds,default=None),'unresolved ages', [t for t,_,j in L if j<0][:14])
if __name__=='__main__':
 prefixes()
 for p in(None,'01','011','0011','00101'):
  for r in(30,90):runs(r,p)
