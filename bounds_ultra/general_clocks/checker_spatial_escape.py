"""A true finite-age cut of the canonical checker-right representative is
not recurrent through arbitrary eastern widths during a mixed periodic
wall. Validate the spatial inverse-window erosion and stress its four
true driven east patterns, not a claim their right traces choose the root.
"""
from spatial_certificate import trans
def inverse():
 for r in(30,90):
  for first in(0,1):
   s=15;l=[]
   for j in range(5):s=trans(s,first^(j&1),r);l.append(s)
   print('east-to-west checker pair masks',r,first,l)
   assert (s.bit_count()==1)==(r==30)
def test(p,r=30,N=500):
 n=N+10;M=(1<<n)-1;chk=sum((i&1)<<i for i in range(n));E=chk;v0=E
 # Isolate the true finite checker front by extending the buffer by n at start.
 E=sum((i&1)<<i for i in range(2*n));rows=[]
 for t in range(N+1):
  rows.append(E&M);c=int(p[t%len(p)]);E=(2*E+c)^((E|(E>>1))if r==30 else (E>>1))
 # Only physical right-rim point in these matched controls starts at first
 # deviation from constant-black wall; strict-east x=i+1, fixed χ_i=i mod2.
 hits=0;maxspan=0
 for t in range(2,N+1):
  d=rows[t]^chk
  for a in range(1,min(t,36)):
   sh=d>>(a-1);L=(sh&-sh).bit_length()-1 if sh else n-a+1
   edge=a+L-1
   if L and t>=a+len(p):
    hits+=1;maxspan=max(maxspan,edge-4*a)
    if r==30:assert edge<4*(a+len(p))
 print('clock',p,'rule',r,'checker-island eligible',hits,'max (b−4a)',maxspan)
if __name__=='__main__':
 inverse()
 for p in('01','011','0011','00101'):
  for r in(30,90):test(p,r)
def r90_infinite_counter(p,n=80,K=40):
 # Compute a finite projection of the genuine construction. At each
 # preceding time choose (old x0,old x1)=(given past p,0); for every
 # j>=1, old x(j+1)=current x(j) XOR old x(j-1). This defines ALL east.
 y=[int(p[0])]+[int(i%2==0) for i in range(1,n+1)]
 for k in range(1,K+1):
  x=[int(p[-k%len(p)]),0]
  for j in range(1,n+1):x.append(y[j]^x[j-1])
  assert all(x[j-1]^x[j+1]==y[j] for j in range(1,n+1))
  y=x[:n+1]
 print('R90 entire-checker eastern landing, mixed past explicitly lifted',p,'tested',K,'ticks',n,'sites')
if __name__=='__main__':
 for p in('01','011','0011','00101'):r90_infinite_counter(p)
