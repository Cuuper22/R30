"""Audit every bounded finite-right survivor against genuine closed exterior-
independent periodic traps, not just membership of its coarse variable host.
If all reach an exact periodic trap or exit, use this dichotomy for a quasi-
nilpotence proof on arbitrary finite RHS; surviving finite seeds instead test for a second required trap."""
from symbolic_q221_lift import *
from collections import Counter
def setup():
 n=31;sz0=203375;S=gethost(n-1,sz0);V=np.sort(np.concatenate((S,S+(1<<(n-1)))));a,b,h=edges(V,n);G,C,sz=cc(a,b,len(V));tr=set()
 for j in np.flatnonzero(sz>1):
  m=(C[a]==j)&(C[b]==j)
  if int(m.sum())==4*int(sz[j]):tr.update(map(int,V[C==j]))
 return tr
def go(lim=5000):
 tr=setup();S=set(map(int,gethost(25,24899)));live=[(i,i)for i in S];cnt=Counter();last=[]
 for t in range(lim+1):
  nxt=[]
  for i,r in live:
   if r%(1<<25)not in S:cnt['exit']+=1;continue
   if r%(1<<31)in tr:cnt['q7']+=1;continue
   y=(2*r)^(r|r>>1);z=(2*y+1)^(y|y>>1);nxt.append((i,z))
  live=nxt
  if t in(20,100,500,1000,2000,3000,5000)or not live:print(t,'pending',len(live),'resolved',cnt,'remaining seed',list(map(hex,(i for i,r in live[:3]))),flush=True)
  if not live:break
if __name__=='__main__':go()
