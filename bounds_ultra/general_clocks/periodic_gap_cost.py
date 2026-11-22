"""Finite marked tapes force bounded spatial-gap cost along cyclic closures
of arbitrary long future center masks. Check actual anchored cycle completions,
not unconstrained temporal columns. A low-cost sequence is the precise rival;
monotone growth needs an argument beyond these finite tables."""
from pathlib import Path
import json

def prim(z):return all(z!=z[:h]*(len(z)//h)for h in range(1,len(z))if len(z)%h==0)
def cyc(A,w):
 j=0;seen=set()
 while j not in seen:
  seen.add(j)
  for b in w:
   j=A[j][b]
   if j<0:return False
 return True

def cost(p,z):
 L=len(p)*len(z);mask=(1<<L)-1;low=sum(int(b)<<j for j,b in enumerate(p))*sum(1<<(i*len(p))for i in range(len(z)));c=low
 q=0
 for i,b in enumerate(z):
  h=p.count('0');
  for j,x in enumerate(p):
   if x=='0':h-=1;q|=(b>>h&1)<<(i*len(p)+j)
 sh=lambda a:a>>1|((a&1)<<(L-1));a,b=c,sh(c)^(c|q)
 # Integer index of the starting black + shortfall (L-g)_+. Evaluate all L
 # temporal rotations at once; the best trivial bound is L+d. Once depth
 # exceeds it, no unseen black there can improve it. A run longer than L
 # never further decreases the score. The center is not counted as west.
 cols=[];d0=0
 for j in range(2*L+3):cols.append(b);a,b=b,sh(b)^(a|b)
 costs=[]
 for ph in range(L):
  v=[b>>ph&1 for b in cols];best=2*L+4;w=None;right=0
  for j in range(len(v)-1,-1,-1):
   if v[j]:
    d=j+1;cc=d+max(0,L-right)
    if cc<best:best=cc;w=(d,right)
    right=0
   else:right+=1
  if best>len(v)-L: # no small bound from this spatial window; exact up to L
   best=min(best,L+1)
  costs.append((best,ph,w))
 return min(costs)

def run(p,n,K):
 A=json.loads(next(Path(__file__).parent.glob(f'dfa_{p}_n{n}_*.json')).read_text())['adjacency'];last=[((),0)]
 for k in range(1,K+1):
  last=[(w+(b,),v)for w,i in last for b,v in enumerate(A[i])if v>=0];cycles=[]
  for w,i in last:
   if not prim(w) or any(w[j:]+w[:j]<w for j in range(1,k))or not cyc(A,w):continue
   h,ph,x=cost(p,w);cycles.append((h,''.join(map(str,w)),ph,x))
  if cycles:
   h,z,ph,x=min(cycles);print(p,'L',k*len(p),'primitive cyclic word orbits',len(cycles),'smallest rooted-gap cost (cap L+1)',h,'cycle/phase/(depth,gap)',z,ph,x,flush=True)

if __name__=='__main__':
 for p,n,K in [('01',25,35),('011',18,22),('0011',18,19),('00101',18,14)]:run(p,n,K)
