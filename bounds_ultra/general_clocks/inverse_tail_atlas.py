"""Rescue the inverse-island test when a phase's target does not synchronize
to a unique ether. Compute *all* possible past eventually-periodic tails
under its exact two-bit inverse, initially retaining each cyclic choice.
If the closure stays finite, get a uniform propagation speed without any
uniqueness assumption. If periods grow, identify where and how."""
from periodic_islands import ref
from collections import defaultdict
def canon(T):
 for k in range(1,len(T)+1):
  if len(T)%k==0 and all(T[j]==T[j%k]for j in range(len(T))):T=T[:k];break
 return min(T[i:]+T[:i] for i in range(len(T)))
def invert(T,rule=30):
 d=len(T);out={};m=0
 for s in range(4):
  x,y=s>>1,s&1;seen={};row=[]
  while (x,y)not in seen:
   seen[x,y]=len(row)
   for b in T:
    row.append(y);x,y=y,b^(x|y if rule==30 else x)
  i=seen[x,y];m=max(m,i);U=canon(tuple(row[i:]));out[U]=max(out.get(U,0),i)
 return out,m
if __name__=='__main__':
 import sys
 for p,z in [('0011',(1,)),('0011',(3,)),('011',(0,1,1)),('00101',(0,)),('01',(0,1,0,0,0))]:
  _,E=ref(p,z);S={canon(tuple(a))for a in E};original=set(S);seen=set();K=0;allrows=set(S)
  for step in range(21):
   V=set()
   for T in S:
    if T in seen:continue
    seen.add(T);G,k=invert(T);V.update(G);K=max(K,k)
   S=V-seen;allrows.update(V)
   if not S:break
   if max(map(len,S))>300 or len(seen)>500:break
  gap=max(max(map(len,(''.join(map(str,T))*2).split('1')))for T in allrows)
  print(p,z,'closed',not S,'rewinds',step+1,'distinct tail rotation classes',len(allrows),'max spatial period',max(map(len,allrows)),'max locking prefix',K,'longest Zero',gap,'vacuum accessible', (0,) in allrows, flush=True)
