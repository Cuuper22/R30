"""Follow backward 3/5 tile insertions in the *correct* 155-cell pure-five
ether. Each inverse scan synchronizes to that ether, yielding an ordinary
integer correction rather than a new denominator. A subunit spatial
speed of these corrections would exclude finite W; a reproducible
superunit isolated defect tests the necessary rival directly."""
from symbolic_fork_reflector import ref,W
from fractions import Fraction
from itertools import product
F,o,p,r,ds=ref('','01000');assert(o,p)==(0,155)
E=[[ds[j]>>a&1 for j in range(p)] for a in range(10)]
re=[Fraction(sum(v<<j for j,v in enumerate(z)),1-(1<<p))for z in E]
def inverse(k,delta,h):
 # delta: spatial XOR difference (nonnegative, finite).
 old=(k-1)%10;curr=h;prev=0;out=(curr^E[old][0]);j=0;stop=delta.bit_length()
 while j<stop or prev!=(E[old][(j-1)%p] if j else 0) or curr!=E[old][j%p]:
  nxt=((delta>>j)&1)^E[k][j%p]^(curr|prev)
  prev,curr=curr,nxt;j+=1;out|=(curr^E[old][j%p])<<j
  assert j<stop+2*p+4
 return old,out
def tile(k,x,g):
 q='010'+'0'*(g-3)
 for b in q[::-1]:
  k,x=inverse(k,x,1-int(b));k,x=inverse(k,x,1)
 return k,x
def signed(k,x):return sum((1-2*E[k][j%p])<<j for j in range(x.bit_length()) if (x>>j)&1)
def run(N=90):
 gapmax=[]
 for k,a in enumerate(E):
  # Read target in exactly the orientation used by the spatial inverse:
  # measure worst-case convergence of both incoming old-pair bits.
  m=0
  for i in range(p):
   for state in range(4):
    u=state>>1;v=state&1;j=i
    while(u,v)!=(E[(k-1)%10][(j-1)%p],E[(k-1)%10][j%p]):
     u,v=v,a[j%p]^(u|v);j+=1
     assert j-i<2*p
    m=max(m,j-i)
  gapmax.append(m)
 print('max inverse tail synchronization lengths by temporal phase',gapmax,flush=True)
 for pat in ('5','35','355','3555','35555'):
  # A suffix is held pure five, appending each listed earlier tile.
  k=0;x=0;b=0;w=''
  for i in range(N):
   g=int(pat[i%len(pat)]);k,x=tile(k,x,g);b+=2*g
   w='010'+'0'*(g-3)+w
   if i in(0,1,4,9,19,49,N-1):
    n=signed(k,x);val=re[k]+n;J=W(w)
    assert (val.denominator*J-val.numerator)%(1<<b)==0
    print('periodic prepend',pat,'tiles',i+1,'clock ticks',b,'last ether discrepancy depth',x.bit_length()-1,'integer correction sign',int(n>0)-int(n<0),flush=True)
 # A single short embedded arbitrarily far back in a pure-five past:
 k,x=tile(0,0,3);b=6
 for i in range(N):
  k,x=tile(k,x,5);b+=10
  if i in(0,9,49,N-1):print('singleton short/preceding long tiles',i+1,'physical past',b,'depth',x.bit_length()-1,flush=True)
if __name__=='__main__':run()
