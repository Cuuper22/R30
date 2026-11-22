"""Does the D4 lower/upper-bit cancellation propagate to an arbitrary
physical west depth on a genuine periodic east channel? First nonaffine
cone selects the first surviving nonlinear interaction, not a host sweep."""
import numpy as np
from general_characteristic_d4 import field

def check(p,N=500):
 for rule in(30,90):
  at=field(rule,p,N);good=[0]*3
  for t in range(N-2):
   a,b,c=map(lambda s:at(t+s,0),range(3));x,y,z=map(lambda s:at(t+s,-1),range(3))
   fall=(c & x)if a==0 else ((1^b)&(1^y));k=a*b;l=b*c
   good[0]+=int((at(t,-2)==x^y^k));good[1]+=int((x&(1^y))==fall);good[2]+=int(at(t,-3)==z^k^l^fall)
  print('physical',rule,p,'second linear,fall linear,third linear',good,'of',N-2)
  if rule==30:assert all(g==N-2 for g in good)
  else:assert min(good)<N-2

def first(p,maxk=15):
 for ph in range(len(p)):
  c=[int(p[(t+ph)%len(p)])for t in range(maxk+1)]
  for k in range(2,maxk+1):
   r=np.arange(2**k,dtype=np.int64);qs=[]
   for t in range(k):
    qs.append((r&1)^(c[t+1]) if not c[t] else np.full(len(r),1^c[t+1],np.int64));r=(r*2+c[t])^(r|r>>1)
   trace=sum(q<<i for i,q in enumerate(qs));I=np.unique(trace,return_index=True)[1];u=trace[I];w=np.stack([q[I]for q in qs],axis=0);a=np.broadcast_to(np.array(c[:k])[:,None],w.shape)
   for h in range(1,k):a,w=w[:-1],np.bitwise_xor(w[1:],np.bitwise_or(w[:-1],a[:len(w)-1]))
   B={};bad=None
   for n,y in zip(u,w[0]):
    x=int(n)|(1<<k);y=int(y);hist=1<<len(B)
    while x:
     l=x.bit_length()-1
     if l not in B:B[l]=(x,y);break
     b,d=B[l];x^=b;y^=d
    if not x and y:bad=int(n);break
   if bad is not None:
    print('pattern,phase,first genuinely nonlinear west depth,distinct temporal words,witness',p,ph,k,len(I),hex(bad));break
  else:print('affine through',maxk,p,ph)
if __name__=='__main__':
 for p in ('01','011','00101'):check(p);first(p)
