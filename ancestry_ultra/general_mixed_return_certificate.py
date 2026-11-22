"""A general-period right synchronizer with no long black/white anchor:
test if arbitrary A/B mosaics reach a single observed return class
under true R30, while fullspace identically driven Rule90 escapes it.
Positive result is a mark+frozen Step4 family, no claim for all clocks."""
from general_characteristic_d4 import field

D=('01100000001','10000001')
S=(0xffffffffffffffff,0x1014111510101115,0x5496719756943117,
   0x1010111110101111,0x5010501150101011,0x5014501550101015,
   0x1010101110101011)
dest=((1,2),(3,4),(1,5),(3,6),(6,5),(6,5),(6,6))
labels=('00111111','111111')

def step(x,c,b,r):
 return ((2*x|c)^(((x if r==30 else 0)|(x>>1)|(b<<5))))&63

def scan(X,w,r):
 actual=lambda i:(X>>i)&1
 vals=[];Y=[i for i in range(64) if actual(i)]
 for c in map(int,w):
  if not c:
   y={i%2 for i in Y};vals.append(str(next(iter(y))) if len(y)==1 else '?')
  Y={step(i,c,b,r)for i in Y for b in range(2)}
 return sum(1<<i for i in Y),''.join(vals)

def regression():
 for r in(30,90):
  for i,X in enumerate(S):
   for a,w in enumerate(D):
    Y,q=scan(X,w,r)
    if r==30:
     assert S[dest[i][a]]==Y
     if i==6:assert q==labels[a]
  print('r,seven terminal results on A/B',r,[(Y.bit_count(),q)for w in D for Y,q in[scan(S[-1],w,r)]])
 print('chronological (length, white offsets for q)',[(len(w),[i for i,c in enumerate(w) if c=='0'])for w in D])
 for i,(X,idx) in enumerate(zip(S,dest)):print(i,f'0x{X:016x}',idx)
 for p in('01','011','00101',D[0]+D[1]):
  at=field(90,p,500)
  assert all(at(t,0)==int(p[(t-1)%len(p)])for t in range(1,501))
  if p==D[0]+D[1]:
   fails=hits=0;start=1
   for k in range(1000):
    w=D[k%2]
    if start+len(w)>500:break
    q=''.join(str(at(start+i,1))for i,c in enumerate(w)if c=='0')
    if k>=4:hits+=1;fails+=q!=labels[k%2]
    start+=len(w)
   assert fails;print('R90 init mark, blank strict west, exact AB drive through 500: post-lock failures/blocks',fails,hits)
  else:
   Y,q=scan(S[0],p*24,90);assert Y==S[0] and set(q)=={'?'}
   print('R90 init mark, blank strict west, exact',p,'through 500: right state count',Y.bit_count())
 at=field(30,None,500);counts=[0,0];hits=[0,0]
 for x in range(-50,51):
  c=''.join(str(at(t,x))for t in range(501));R=[sum(at(t,x+j+1)<<j for j in range(6))for t in range(501)]
  for t in range(500):assert R[t+1]==step(R[t],int(c[t]),at(t,x+7),30)
  for a,w in enumerate(D):
   for t in range(501-len(w)):
    if c[t:t+len(w)]!=w:continue
    counts[a]+=1
    if (S[6]>>R[t])&1:
     q=''.join(str(R[t+j]&1)for j,s in enumerate(w)if s=='0');assert q==labels[a]
     assert S[6]&(1<<R[t+len(w)]);hits[a]+=1
 print('R30 singleton real A/B blocks, included state6, 501 rows and x=-50..50',counts,hits)
if __name__=='__main__':regression()
