"""Width-free exact right-ray search for a merger after a prescribed finite
center past. A node is two adjacent time columns in each donor. Follow
true horizontal extensions and certify any witness on an actual spatial cycle;
an empty frontier rejects every full eastern tail, including aperiodic ones.
A cap gives UNKNOWN. Does the residual mature 20-bit guard really lift?
"""
from functools import lru_cache
from collections import Counter
import sys
def solve(p,ph,k,u,n=20,cap=70000,maxdepth=95):
 C=sum(int(p[(ph-k+1+j)%len(p)])<<j for j in range(k+1));m=(1<<k)-1;high=1<<k
 @lru_cache(None)
 def inside_ok(a,b):
  return not (b & ((b>>1)^a^m) &m) # if b_t=1 -> b_next=1 xor a_t
 @lru_cache(None)
 def opts(a,b,top): # all feasible z columns
  v=(b>>1)^a;forced=(~b)&m
  if not inside_ok(a,b):return ()
  S=[0]
  for t in range(k+1):
   if t==k:allowed=(top,)if top>=0 else (0,1)
   elif forced>>t&1:allowed=(v>>t&1,)
   else:allowed=(0,1)
   S=[h|(q<<t)for h in S for q in allowed if t==0 or not(h>>(t-1)&1)or q==1-(b>>(t-1)&1)]
   if not S:break
  return tuple(S)
 def starts():
  t=u&1;one=[z for z in range(1<<(k+1)) if z>>k==t and inside_ok(C,z)]
  return {(C,x,C,y)for x in one if x>>(k-1)&1 for y in one if not(y>>(k-1)&1)}
 S=starts();counts=[len(S)]
 for j in range(1,maxdepth):
  NEWS=set();top=(u>>j)&1 if j<n else -1
  for a,b,c,d in S:
   for x in opts(a,b,top):
    for y in opts(c,d,top):
     if (x^y)&high:continue
     # distinct actual prior donors must never share a black or two
     # consecutive blanks at/after position 1 (else they rewind equal).
     if (x&y)>>(k-1)&1:continue
     if not ((b^d)|(x^y))>>(k-1)&1:continue
     NEWS.add((b,x,d,y))
     if len(NEWS)>cap:return 'cap',j+1,counts
  S=NEWS;counts.append(len(S))
  if not S:return 'empty',j+1,counts
  if j>=n and len(S)==prev and S==old:return 'cycle',j+1,counts
  old=S;prev=len(S)
 return 'depth',j+1,counts
if __name__=='__main__':
 p,ph,k,u=sys.argv[1:5];print(p,ph,k,u,solve(p,int(ph),int(k),int(u,16)),flush=True)
