"""Can the entire type-10 return (not a single generic pulse gap) force
a strict decrease of the finite marked exterior's inverse-rank remainder?
A uniform decrease over the true E34 word family gives a well-founded
contradiction; signed counterexamples select the exact nonlocal obstacle."""
from symbolic_q221_lift import *
import json
def K(x,a,b):return x^((2*x+a)|(4*x+2*a+b))
def D(x):return K(K(x,0,0),1,1)
def ik(y,a,b,w=None):
 exact=w is None
 if exact:w=y.bit_length()
 out=0
 for j in range(w):
  n=(y>>j&1)^(a|b);out|=n<<j;b,a=a,n
 return out if(not exact or not(a|b))else None
def invD(y,w=None):
 q=ik(y,1,1,w);return ik(q,0,0,w)if q is not None else None
def rep(f,z,k):
 for _ in range(k):z=f(z)
 return z
def rank(x):
 n=0
 while (y:=invD(x))is not None:x=y;n+=1
 return n
def head(h):return (2*4**(h-1)+1)//3
def coding(gs):
 w=0;y=0
 for h in gs[::-1]:
  y=head(h)+(rep(lambda z:invD(z,w),y,h)<<(2*h));w+=2*h
 return y,w
def hmap(x,h):
 assert x%2**(2*h)==head(h);return rep(D,x>>(2*h),h)
def hs(w):
 I=[j for j,c in enumerate(w)if c=='1']+[len(w)+w.index('1')]
 return [b-a for a,b in zip(I,I[1:])]
def run():
 J=json.loads((A/'p2_b_next_words.json').read_text())['82754'];L=list(J['10']['10'])+[J['10']['17'][0]+J['17']['10'][0],J['10']['26'][0]+J['26']['10'][0]]
 for w in L:
  gg=hs(w);y,n=coding(gg);out=[]
  for k in(0,1,2,4,8,16,32,64):
   old=rep(lambda z:invD(z,n),y,k)
   for salt in(0,1,13):
    x=rep(D,old+(salt<<n),k);z=x
    for h in gg:z=hmap(z,h)
    r0=rank(x);r1=rank(z);dd=(z.bit_length()-4*r1)-(x.bit_length()-4*r0)
    out.append((dd,k,salt,r0,r1))
  print('return',len(w),'gaps',''.join(map(str,gg)),'extreme rank-remainder change',min(out),max(out),flush=True)
if __name__=='__main__':run()
