"""Test whether a single signed integer packs BOTH endpoints of every
cluster in the actual row, including the east and west extremal marks.
If unique, decode q from that one-step quantity; if not, isolate the
first colliding cluster pair before using it under an assumed wall."""
from general_characteristic_d4 import field
def ends(z):return z&~(z<<1)&~(z<<2),z&~(z>>1)&~(z>>2)
def decode(s):
 lmask=rmask=0
 while s:
  p=s&-s;k=(s+p)&-(s+p);r=k>>2
  if not r or p>r or s<12*r-p:return None
  lmask|=p;rmask|=r;s-=12*r-p
 return lmask,rmask
def tests():
 for p in ('01','011','00101'):
  for r in (30,90):
   v=field(r,p,500);z=1;err=cnt=0
   for t in range(500):
    g=(4*z)^((2*z)|z);L,R=ends(z)
    assert decode(g+4*z)==(L,R)
    z=g
    # Coefficientwise universal Laurent polynomial identity:
    # q(q-1)(X'+qX)=q²(2q-1)N-M. Works in full space,
    # including the genuine infinite eastern Rule90 controls.
    for x in range(-15,16):
     m=v(t,x)*(1-v(t,x-1))*(1-v(t,x-2))
     def n(y):return v(t,y)*(1-v(t,y+1))*(1-v(t,y+2))
     a=v(t+1,x-2)-v(t+1,x-1)+v(t,x-3)-v(t,x-2)
     err+=a!=2*n(x-3)-n(x-2)-m;cnt+=1
   print(r,p,'two-endpoint identity fails',err,'/',cnt)
   assert (err==0)==(r==30)
if __name__=='__main__':tests()
def hull(z):
 low,high=ends(z);p=low;out=0
 while p:
  l=p&-p;r=high&-high
  out|=2*r-l;p-=l;high-=r
 return out
def hullfrom(l,h):
 out=0
 while l:
  a=l&-l;b=h&-h;out|=2*b-a;l-=a;h-=b
 return out
def unseal(s,s1):
 # Both rows start at their own west rim: the new normalized index is
 # physical coordinate +1 relative to the old index. Read each old
 # (l,r) at new indexes l+2,...,r+1. First value at l+2 is zero.
 m,n=decode(s);mm,nn=decode(s1);I=hullfrom(mm,nn);z=0
 while m:
  l=m&-m;r=n&-n;m-=l;n-=r;z|=r
  new=0
  b=l
  while b<r:
   k=4*b # new normalized bit for the old physical b's eastern neighbor
   if k==4*l:new=0
   else:new=0 if not(k&I)else 1 if k&mm else 1-new
   if not new:z|=b
   b*=2
 return z
def full():
 g=lambda z:(4*z)^((2*z)|z)
 for z in range(1<<16):
  h=g(z);k=g(h);assert unseal(h+4*z,k+4*h)==z
 z=1
 for t in range(501):
  h=g(z);k=g(h);assert unseal(h+4*z,k+4*h)==z;z=h
 print('two consecutive east-weighted displacements reconstruct every raw 16-bit row and all 501 actual singleton rows')
if __name__=='__main__':full()
def sparse_shadow():
 # Each 5-cell old row window specifies whether its central 001 or its
 # corresponding three new bits 001 occur. Removing 16 cells at both
 # ends of a finite window supplies arbitrary extension on both sides
 # by repetition among the 16 four-bit de Bruijn states.
 def step(z,n,r):
  k=(1<<n)-1;l=(z*2&k)|(z>>(n-1));rr=(z>>1)|((z%2)<<(n-1))
  return l^((z|rr)if r==30 else rr)
 def mark(z,n):
  k=(1<<n)-1;l=(z*2&k)|(z>>(n-1));ll=(l*2&k)|(l>>(n-1));return z&~l&~ll
 z=0x37;n=7;h=step(z,n,90)
 assert not mark(z,n) and not mark(h,n)
 L=[]
 for t in range(500):L.append(z&1);z=step(z,n,90)
 print('genuine R90 torus seven-point initial 0x37: no mark in first two whole rows;',sum(a!=b for a,b in zip(L,L[1:])),'center flips by t499')
 for p in ('01','011','00101'):
  v=field(30,p,500);N=500;qual=0
  for t in range(N-15):
   h=next((j for j in range(4,16)if sum(v(t+i,0)!=v(t+i+1,0)for i in range(j))>=4),None)
   if h is None:continue
   q=h+19
   assert any(v(t+i,x)and not(v(t+i,x-1)or v(t+i,x-2))for i in(0,1)for x in range(-q,q+1))
   qual+=1
  print('genuine R30 two-time shadow',p,qual)
if __name__=='__main__':sparse_shadow()
