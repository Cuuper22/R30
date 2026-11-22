"""A single NE word has purely dyadic period from the marked east edge;
compute its *exact* D4 monodromy and use both SW/NE initialization.
Can a periodic center force bounded monodromy rather than just bounded
terminal symbols? If such a finite-type block repeats, test joint periods.
"""
import numpy as np
from general_characteristic_d4 import factor,field

def tx(w,s=0):
 # old cyclic b at j=-1 equals s in the actual (s=0) SW marks, including i=0.
 a=w&1;b=w>>1;k=np.roll(b,1)|a
 u=np.bitwise_xor.accumulate(k)^(s&1);v=np.bitwise_xor.accumulate(u|b)^(s>>1)
 return u+2*v

def go(limit=1<<20,I=500):
 w=np.array([3,1],np.uint8);D=[]
 for i in range(I):
  m=len(w);b=w>>1;a=w&1;k=np.roll(b,1)|a
  assert w[0]==3 and (i==0 or not w[-i:].any()) and i<m
  sgn=1 if (m+int(k.sum())+int(b.sum()))%2==0 else -1
  w0=tx(w);d=int(w0[-1]);x=d;V=[w0]
  while x:
   V.append(tx(w,x));x=(sgn*x+d)%4
   assert len(V)<=4
  v=np.concatenate(V)
  while len(v)>1 and np.array_equal(v[:len(v)//2],v[len(v)//2:]):v=v[:len(v)//2]
  D.append((i,m,sgn,d,len(v),int(w[i])))
  if len(v)>limit:break
  w=v
 print('first i,p_i,sign,offset,p_i+1,center',D[:32]);print('monodromy total sign,offset', {k:sum((s,d)==k for _,_,s,d,_,_ in D)for k in sorted({(s,d)for _,_,s,d,_,_ in D})});print('sample ends at',D[-1]);return D
if __name__=='__main__':go()
