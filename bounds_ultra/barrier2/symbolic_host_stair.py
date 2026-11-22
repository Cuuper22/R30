"""A capped old finite tape under a true long B return needs a vacancy of
Q−O(1) in the closed q-comparator. A slow westward black staircase lands
inside it. Test actual cyclic walks of the surviving host: if one launch
always travels <Q by a linear amount, seek its OR monotone bound; if the
clocks straddle unit speed, use the explicit first faster cycle instead."""
from symbolic_q221_lift import *
from random import Random
def cycles(S,n,count=40,seed=13):
 a,b,h=edges(S,n);G,C,sz=cc(a,b,len(S));r=Random(seed);out=[]
 for _ in range(count):
  v=r.randrange(len(S));seen={};q=[]
  while v not in seen:
   seen[v]=len(q);q.append(int(S[v])&1);ad=G.indices[G.indptr[v]:G.indptr[v+1]];v=int(ad[r.randrange(len(ad))])
  q=q[seen[v]:];out.append(q)
 return out
def run(q):
 # time zero white; X0=0, X−1=1−q; black at odd t and X−1=1.
 Q=2*len(q);M=(1<<Q)-1;c=sum(2<<(2*i)for i in range(len(q)));b=sum((3-int(h))<<(2*i)for i,h in enumerate(q));A=[c,b]
 for j in range(3*Q+64):
  a,b=A[-2:];A.append((b>>1|(b&1)<<(Q-1))^(b|a))
 old=[d for d in range(1,9)if A[d]&1];pos=old.copy()
 for i in range(Q):
  for k,d in enumerate(pos):
   if d<0:continue
   while d+1<len(A) and (A[d+1]>>i)&1:d+=1
   pos[k]=d if d+1<len(A)else -1
 return [y-x if y>=0 else 9*Q for x,y in zip(old,pos)]
if __name__=='__main__':
 for n,d in((31,315078),(39,264368)):
  L=[]
  for q in cycles(gethost(n,d),n):
   z=run(q);m=min(z);Q=2*len(q);s=''.join(map(str,q))
   L.append((m/Q,Q,min(z),max(z),s[:42]))
  print(n,d,'slowest launch relative to Q in true q cycles',min(L),max(L),'cycles min≥Q',sum(xs[0]>=1 for xs in L),'of',len(L),flush=True)
