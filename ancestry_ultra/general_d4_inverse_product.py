"""Full characteristic inverse at arbitrary period, with *cyclic* or
SW-marked boundary. Input coordinates (b[j-1],a[j]) never cross another
choice: count/predict a whole old diagonal via the product of scalar fibers.
A one-bit endpoint test is weaker than subjecting its complete compatible
row to this actual previous-row filter.
"""
from general_characteristic_d4 import field
from itertools import product
from math import prod

def fibre(Y,s=0,cyclic=False):
 # Marked start z=2s,p=s; cyclic start is Y[-1], no prescribed old p.
 y=[2*s]+list(Y)if not cyclic else [Y[-1]]+list(Y)
 # Permitted b_j is read from (u_j,v_j,v_{j-1}), nothing to its east.
 B=[]
 for prev,z in zip(y,y[1:]):
    u=z&1;dv=(z^prev)>>1;B.append(tuple(b for b in (0,1)if u|b==dv))
 pairs=[]
 for j,(prev,z) in enumerate(zip(y,y[1:])):
    du=(prev^z)&1;bs=B[j-1]if j or cyclic else (s,)
    pairs.append(tuple((b,a)for b in bs for a in(0,1)if b|a==du))
 return pairs,(()if cyclic else B[-1])

def count(Y,s=0,cyclic=False):
 P,B=fibre(Y,s,cyclic);return prod(map(len,P))*(1 if cyclic else len(B))

def check():
 from general_characteristic_d4 import factor
 from collections import Counter
 for m in(1,2,3,4,5,6):
  hist=Counter()
  for w in product(range(4),repeat=m):
   z=0;p=0;V=[]
   for d in w:z=factor(z,d,p);p=d>>1;V.append(z)
   hist[tuple(V)]+=1
  assert all(count(y)==hist[y]for y in product(range(4),repeat=m))
  print(m,len(hist),'of',4**m,'fiber max',max(hist.values()))
 for pat in('01','011','00101'):
  for ru in(30,90):
   at=field(ru,pat,500);hit=tot=0;first=[]
   for i in range(1,249):
    for s in(0,1):
     out=[at(i+1+j+s,j-i-1)+2*at(i+2+j+s,j-i-1)for j in range(i+1)]
     n=count(out,s);tot+=1;hit+=bool(n)
     if not n and len(first)<3:first.append((i,s))
   print('pattern/rule,positive whole diagonal inverse fibers',pat,ru,hit,tot,'first zero',first)
if __name__=='__main__':check()

def interior():
 from collections import Counter
 for p in('01','011','00101'):
  for r in(30,90):
   at=field(r,p);a=Counter()
   for i in range(3,249):
    for s in(0,1):
     ys=[at(i+1+j+s,j-i-1)+2*at(i+2+j+s,j-i-1)for j in range(i+1)]
     fail=[]
     for j in range(1,i):
      u=ys[j]&1;e=(ys[j]^ys[j-1])>>1
      fail.append(not (u<=e<=u|(ys[j+1]&1)))
     a['bulk violated triples']+=sum(fail);a['bulk triples']+=len(fail);a['half cut,any fail']+=any(fail[len(fail)//2:]);a['rows']+=1
   print('bulk condition',p,r,dict(a))
if __name__=='__main__':interior()
