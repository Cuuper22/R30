"""Impose the actual old dyadic horizontal period and the preceding marked
row's local image on the complete D4 inverse, rather than counting free
rises on a single row. When the monodromy toggles the low bit this pins
all old upper bits; test whether the genuine source removes the rest.
"""
import numpy as np
from general_characteristic_periods import tx
from general_d4_inverse_product import fibre

def child(w):
 u=w&1;b=w>>1;k=np.roll(b,1)|u;sgn=1 if (len(w)+int(k.sum())+int(b.sum()))%2==0 else -1
 v=tx(w);d=int(v[-1]);g=d;V=[v]
 while g:V.append(tx(w,g));g=(sgn*g+d)%4
 return np.concatenate(V),d

def choices(y,d,age):
 # A genuine period-d predecessor must meet every residue's intersected
 # pair constraints. Cyclic input/output are fully physical, no cutoffs.
 p=len(y);assert p%d==0;M=np.full(d,15,np.uint8)
 for j,C in enumerate(fibre(y,cyclic=True)[0]):
  mask=sum(1<<(2*b+a)for b,a in C);M[j%d]&=mask
 # state = previous packed symbol plus the upper bit two sites ago.
 # At age>=3 the exact previous SW zero run fixes the start and end 0.
 lock={j%d:0 for j in range(-age,0)};lock[(-age-1)%d]=1;lock[0]=3
 layers=[];start=1;active=start
 def trans(j,s):
  old=s%4;bp=s//4;b=old>>1;u=old&1
  for z in range(4):
   a=z&1
   if j in lock and z!=lock[j]:continue
   if not M[j]>>(2*b+a)&1:continue
   if u<=b^bp<=u|a:yield z+4*b
 for j in range(d):
  n=0;E=[]
  for s in range(8):
   if active>>s&1:
    for z in trans(j,s):E.append((s,z));n|=1<<z
  layers.append(E);active=n
 assert active&start
 out=[set()for _ in range(d)];active=start
 for j in reversed(range(d)):
  n=0
  for s,z in layers[j]:
   if active>>z&1:n|=1<<s;out[j].add(z%4)
  active=n
 assert active&start
 return out

def go(n=16):
 w=np.array([3,1],np.uint8)
 for i in range(n+1):
  v,m=child(w)
  if i>=3:
   S=choices(v,len(w),i);assert all(int(x)in a for x,a in zip(w,S))
   unk=np.array([len(x)>1 for x in S]);ub=np.array([len({z>>1 for z in x})>1 for x in S]);
   assert not(m&1 and ub.any());print('age,period,offset,ambiguous full old letters and old upper,center allowed,nearby previous ambiguity',i,len(w),m,int(unk.sum()),int(ub.sum()),sorted(S[i]),''.join('?' if k else '.'for k in unk[max(0,i-4):i+8]),flush=True)
  w=v
if __name__=='__main__':go()
