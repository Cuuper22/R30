"""Instead of a giant host BDD, extend only right words carrying both
opposing whole-right predecessor inputs. This 16-state inverse transducer
retains exact arbitrary finite completions at every depth (00/11 tails).
Emptiness proves a uniform all-width bound. Nonempty gives a concrete
finite counterfixture, checked with its whole untruncated clamped dynamics."""
from symbolic_q221_lift import *
from symbolic_nonmerge_host import pair
from functools import lru_cache
@lru_cache(None)
def move(mask,y):return sum(1<<s for s in range(16)if mask>>pair(y,s)&1)
REACH={12:''};Q=list(REACH)
for s in Q:
 for y in range(2):
  a=pair(y,s)
  if a not in REACH:REACH[a]=REACH[s]+str(y);Q.append(a)
RM=sum(1<<s for s in REACH)
def start(n,d,p):
 S=set(map(int,gethost(n,d)));m0=sum(1<<s for s in range(16)if s&5==p+4*(1-p));out=[]
 for v in S:
  m=m0
  for j in range(n):m=move(m,v>>j&1)
  if m&RM:out.append((v,m))
 return S,out
def clamp(r,h):
 for i in range(h):x=(2*r)^(r |(r>>1));r=(2*x+1)^(x|(x>>1))
 return r
def grow(V,S,n,h):
 W=[];K=(1<<n)-1;l=n+2*(h-1)
 for a,m in V:
  for i in range(4):
   mm=move(move(m,i&1),i>>1)
   if mm&RM:
    v=a+(i<<l)
    if clamp(v,h)&K in S:W.append((v,mm))
 return W
def ex(V,n,h,p,S):
 v,m=V[0];s=next(s for s in REACH if m>>s&1);tail=REACH[s];r=v+(int(tail,2)<<(n+2*h)if tail else 0)
 s=12
 for y in bin(r)[2:]:s=pair(int(y),s)
 assert s&5==p+4*(1-p)
 assert all(clamp(r,j)%2**n in S for j in range(h+1))
 return hex(r)
def run(n=34,d=82754,L=20,cap=120000):
 for p in (0,1):
  S,V=start(n,d,p)
  for h in range(L+1):
   print('past finite',p,'strobes',h,'resolved admissible prefixes',len(V),'finite witness',ex(V,n,h,p,S) if V else None,flush=True)
   if not V or len(V)>cap:break
   V=grow(V,S,n,h+1)
if __name__=='__main__':run()
