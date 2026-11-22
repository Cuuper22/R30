"""Does the universal short forbidden-white-word lemma eliminate a genuinely
marked western cut while ALL earlier black constraints pass? Reuse the actual
singleton rows through 500, without an onset search or a SAT problem. A
short white-only refutation identifies an ordinary-integer cylinder via
triangularity. Coupled Rule90 actual controls must never hit one."""
from functools import lru_cache
from pathlib import Path
from controls import r90
@lru_cache(None)
def obs_table(p,n=8,rule=30):
 S=(1<<(1<<n))-1;low=sum(1<<i for i in range(1<<n)if i&1);mask=(1<<n)-1
 def one(s,c):
  u=0
  while s:
   B=s&-s;i=B.bit_length()-1;s^=B
   for b in (0,1):
    v=(i>>1)|(b<<(n-1));j=((2*i+c)^((i|v)if rule==30 else v))&mask;u|=1<<j
  return u
 @lru_cache(None)
 def step(s,c):return one(s,c)
 whites=tuple(i for i,t in enumerate(p)if t=='0');R={}
 for a in whites:
  live={0:S};j=a
  for h in range(1,9):
   keep={};AL=set()
   for w,V in live.items():
    for q,G in [(0,S^low),(1,low)]:
     U=V&G;u=2*w+q
     if not U:continue
     AL.add(u);k=j;U=step(U,int(p[k%len(p)]));k+=1
     while p[k%len(p)]=='1':U=step(U,1);k+=1
     keep[u]=U
   R[a,h]=AL;live=keep;j+=1
   while p[j%len(p)]=='1':j+=1
 return R
def flags(p,w,K,repo):
 P=len(p);q=[];firstb=K;firstq=K;ev=None
 for t in range(K):
  c=int(p[t%P]);h=(w&1)^int(p[(t+1)%P])
  if c:
   if firstb==K and h!=1:firstb=t
  else:
   q.append((t,h))
   if firstq==K:
    v=0
    for k,(j,b) in enumerate(q[-8:][::-1],1):
     v|=b<<(k-1)
     if v not in repo[j%P,k]:firstq=t;ev=(j,k,format(v,'0%db'%k));break
  w=(w>>1)^(w|(2*w+c))
 return firstb,firstq,ev
def run():
 N=500;Z=1;X=[]
 for t in range(N+1):
  b=(Z>>t)&1;w=int(format(Z&((1<<t)-1),'0%db'%t)[::-1],2)if t else 0
  X.append((b,w));Z=(4*Z)^(2*Z|Z)
 for p in ('01','011','0011','00101'):
  T=obs_table(p);T90=obs_table(p,rule=90);C,R=r90(p,N);K=120
  # Row indexes 1..500 of the genuine marked R90 adversary carry p from phase0.
  rr=[(t-1,R[t])for t in range(1,N+1)if C[t]==0]
  for i in range(len(rr)):
   for k in range(1,min(8,len(rr)-i)+1):
    j=rr[i][0];v=int(''.join(str(z[1])for z in rr[i:i+k]),2);assert v in T90[j%len(p),k]
  res=[];first=None;outside=[];surv=0
  for t,(b,w)in enumerate(X):
   if b!=int(p[0]):continue
   prev,q,ev=flags(p,w,K,T);res.append((prev,q))
   if q<prev:
    if first is None:first=(t,hex(w% (1<<(q+1))),q+1,ev,prev)
    outside.append(t)
   if prev>=K or q>=K:surv+=1
  head=max(min(b,q)for b,q in res)
  print(p,'white phase 8-read cardinalities',[len(T[a,8])for a in range(len(p))if p[a]=='0'],'R90',[len(T90[a,8])for a in range(len(p))if p[a]=='0'],'eligible actual cuts',len(res),'white before black',len(outside),'first rooted (age,low tape mod 2^bits,bits,(start,size,prohibited word),first black failure)',first,'largest first rejection tick',head,'longest white-only survival',max(q for b,q in res),flush=True)
if __name__=='__main__':run()
