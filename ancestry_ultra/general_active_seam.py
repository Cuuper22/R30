"""Exact active observability of outgoing seam, not an extra fixed-onset
sweep. Can the complete finite right state be hidden from all center
drives as its captured tip clock varies? Use controllable erasure + first
arrival. Check true row500, matched R90 clocks, and OR-erased singleton caps."""
from general_characteristic_d4 import field

def step(x,c,r):return (2*x|c)^((x if r==30 else 0)|x>>1)
def cap(x,r):return x^(((x>>1)if r==30 else 0)|(x>>2) if r==30 else x>>2)
def spin(x,seq,r):
 for c in seq:x=step(x,c,r)
 return x
def val(x):return (x&-x).bit_length()-1 if x else 10**12
def seam(x):return (x&1,int(bool(x&3)))
def erase(x,n,r):
 w=[0]*n
 for j in range(n):
  if spin(x,w,r)>>(n-1-j)&1:w[j]=1
 assert not (spin(x,w,r)&((1<<n)-1))
 return w
def separation(x,y,r,nmax=2048):
 a,b=x,y
 for n in range(nmax):
  if seam(a)!=seam(b):
   w=erase(x,n,r);X,Y=spin(x,w,r),spin(y,w,r)
   assert X>>n==a and Y>>n==b
   assert val(X)==n+val(a) if a else X==0
   assert val(X)!=val(Y)
   return n,min(val(X),val(Y)),''.join(map(str,w))
  a,b=cap(a,r),cap(b,r)
def test():
 N=500;at=field(30,None,N);caps={i:sum(at(i,j)<<j-1 for j in range(1,i+1)) for i in range(5,40)}
 for t,E in caps.items():
  a=E
  for n in range(501-t):
   assert a&1==at(t+n,n+1);a=cap(a,30)
 pairs=[(t,t+p)for p in(2,3,5,9)for t in range(5,22)]
 fs=[separation(caps[t],caps[s],30)for t,s in pairs];assert all(fs)
 print('true singleton beyond age4, distinct active sections, max n and zero-tail first divergence',len(fs),max(x[0]for x in fs),max(x[1]for x in fs))
 for p in ('01','011','00101'):
  R=field(90,p,N);assert all(R(t,0)==int(p[(t-1)%len(p)]) for t in range(1,501))
  # Symmetric paired high-mark perturbations preserve this WHOLE center
  # on R90, but flipping +D toggles R1 at t=D-1.
  D=23;d=1<<((N+5)+D)|1<<((N+5)-D);delta=[]
  for t in range(501):
   assert not ((d>>(N+5))&1);delta.append(d>>(N+6)&1);d=(2*d)^(d>>1)
  assert delta.index(1)==D-1
  print('real R90 center unchanged',p,'right response changes at',delta.index(1))
  # Under R30 these highest-first stripe caps differ but the active
  # signatures agree, hence no possible input separates inner head.
  X,Y=0b11000000,0b01000000
  sx,sy=X,Y
  for t in range(501):
   assert seam(sx)==seam(sy)
   c=int(p[t%len(p)]);assert X&1==Y&1;X=step(X,c,30);Y=step(Y,c,30)
   sx,sy=cap(sx,30),cap(sy,30)
if __name__=='__main__':test()
