"""Do consecutive actual B launches under the two surviving nonabsorbing
P2 channels have to merge before the single finite east rim? Every such
merge identifies absolute time of first contact with the tip. A universal
local merger would bound all cofinal B launch times, contradiction.
A nonmerger deep within the q-variable host will locate the extra return
conditions needed by this particular two-launch argument."""
from symbolic_q221_lift import gethost
from symbolic_copy_arrivals import delay
from collections import Counter
from random import Random
def step(r,c):return (2*r+c)^(r|r>>1)
def data(n,d,N=250):
 V=list(map(int,gethost(n,d)));D=set(V);m=(1<<n)-1
 rng=Random(3701+d);freq=Counter();best={};longest=(0,None)
 for k in range(600):
  z=rng.choice(V);r0=z+(rng.getrandbits(rng.choice([0,8,30,101]))<<n);r=r0
  H=[]
  for t in range(N):
   if r&m not in D:break
   b=step(r,0)
   if b&15==11:
    h=r&31;T=2*t+1;A=T+delay(b,30);H.append((T,h,A))
   r=step(b,1)
  if len(H)>longest[0]:longest=(len(H),hex(r0))
  for (s,h,a),(T,j,b)in zip(H,H[1:]):
   assert b>=a,(hex(r0),s,T,a,b)
   q=T-s;tag=h,j,q,b>a;freq[tag]+=1
   score=min(s//2,t-T//2);old=best.get(tag)
   if old is None or score>old[0]:best[tag]=(score,hex(r0),s,T,a,b,t)
 print('host',d,'most B in-variable',longest,'launch-type/lag records',flush=True)
 for tag in sorted({k[:3]for k in freq}):
  print(tag,'same/distinct tip-contact counts',freq[tag+(False,)],freq[tag+(True,)],'most interior strict jump',best.get(tag+(True,)),flush=True)
if __name__=='__main__':
 for n,d in ((31,315078),(39,264368)):data(n,d)
