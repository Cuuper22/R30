"""The complete marked southwest/east wave gives an ONLINE neighbor map
on its horizontal orbit's prefix tree: equal initial center pairs imply
equal next-site pairs, by invertible D4 transport. Does that map admit a
finite context realization (which would preserve periodic center words)?
Use the true entire dyadic source orbit at each level, not hypothetical
unconstrained paths. A collision tests finite window vs a genuine state.
"""
import numpy as np
from general_marked_fiber import child

def inputs(n):
 W=[np.array([3,1],np.uint8)]
 for k in range(n+1):W.append(child(W[-1])[0])
 return W

def sliceof(W,i,z,centerstep=0):return W[i][(z+i+centerstep)%len(W[i])].astype(np.uint64)
def blocks(W,i,z,typ):
 x=sliceof(W,i,z);y=sliceof(W,i,z,1)
 if typ=='full':return x,y
 nx=sliceof(W,i+1,z)
 # For an input step (C(t+1),C(t+2)), recover simultaneous masked R bits.
 c=(x>>1)+2*(nx&1);return c,y&(~c&3)

def test(W,h,typ,pat=None):
 K=[];V=[];T=[];Z=[]
 for i in range(h,len(W)-1):
  n=len(W[i+(typ=='masked')]);z=np.arange(n,dtype=np.uint64);k=np.zeros(n,np.uint64);digits=[]
  for j in range(i-h,i+1):
   x,y=blocks(W,j,z,typ);digits.append(x);k=(k<<2)|x
   if j<i:k=(k<<2)|y
  m=np.ones(n,bool)
  if pat:
   p=list(map(int,pat));D=len(p);m=np.zeros(n,bool)
   for ph in range(D):
    tt=np.ones(n,bool)
    for j,x in enumerate(digits):tt&=(x==p[(ph+2*j)%D]+2*p[(ph+2*j+1)%D]);
    m|=tt
  K.append(k[m]);V.append(y[m]);T.append(np.full(m.sum(),i));Z.append(z[m]);
 k=np.concatenate(K);v=np.concatenate(V);i=np.concatenate(T);z=np.concatenate(Z)
 if not len(k):return 0,0,None
 I=np.lexsort((v,k));j=I[:-1];f=I[1:];bad=(k[j]==k[f])&(v[j]!=v[f]);B=np.flatnonzero(bad)
 return len(k),len(np.unique(k)),(int(i[j[B[0]]]),int(z[j[B[0]]]),int(v[j[B[0]]]),int(i[f[B[0]]]),int(z[f[B[0]]]),int(v[f[B[0]]]))if len(B)else None

def go(n=19):
 W=inputs(n)
 for mode in('full','masked'):
  for h in(1,2,3,4,5,6,8):
   s,u,b=test(W,h,mode);print('reader,history pairs,samples,keys,actual different-output collision (i,horizontal shift,out ×2)',mode,h,s,u,b,flush=True)
 for p in('01','011','00101'):
  for h in(2,3,4,5):
   s,u,b=test(W,h,'masked',p);print('matched drive',p,h,s,u,b,flush=True)
if __name__=='__main__':go()
