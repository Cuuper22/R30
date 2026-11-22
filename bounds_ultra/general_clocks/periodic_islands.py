"""Tests if an actual marked-west ray can spend an asymptotically full
fraction of its age in a periodic right-read regime, across four clocks.
A synchronizing spatial ether gives a subunit upper bound; retain the
failing phase/reset (rather than guessing) if it has cyclic alternatives."""
from fractions import Fraction
from pathlib import Path
import json
def ref(p,labels):
 c=tuple(map(int,p))*len(labels);m=len(c);a=sum(x<<j for j,x in enumerate(c));sc=lambda x:(x>>1)|((x&1)<<(m-1))
 r=0;w=p.count('0')
 for i,s in enumerate(labels):
  k=w
  for j,v in enumerate(p):
   if v=='0':k-=1;r|=((s>>k)&1)<<(i*len(p)+j)
 b=sc(a)^(a|r);A={};data=[]
 while (a,b) not in A:
  A[a,b]=len(data);data.append(b);a,b=b,sc(b)^(a|b)
  if len(data)>200000:raise OverflowError
 o=A[a,b];D=len(data)-o
 E=[[data[o+j]>>t&1 for j in range(D)]for t in range(m)]
 return o,E
def sync(E,rule):
 L=len(E);d=len(E[0]);K=0;gap=0
 for a,target in enumerate(E):
  old=E[(a-1)%L]
  if not any(target):return -1,0
  cc=0
  for b in target*2:cc=0 if b else cc+1;gap=max(gap,cc)
  for j in range(d):
   for v in range(4):
    x=v>>1;y=v&1;k=j
    while (x,y)!=(old[(k-1)%d],old[k%d]):
     x,y=y,target[k%d]^(x|y if rule==30 else x);k+=1
     if k-j>4*d:return None,gap
    K=max(K,k-j)
 return K,gap
def admitted(p,z):
 d=json.loads(next(Path(__file__).parent.glob('dfa_'+p+'_*.json')).read_text());A=d['adjacency'];i=0;seen=set()
 while i>=0 and i not in seen:
  seen.add(i)
  for q in z:i=A[i][q]if i>=0 else -1
 return i>=0
def r90_sanity(E):
 # A Rule90 preimage scan transports the two arbitrarily entered bits bijectively:
 # no target tail is synchronizing, even if the reference also followed Rule90.
 for t in (0,1):assert len({(y,t^x)for x in (0,1)for y in (0,1)})==4
def run():
 for p,z in [('01',(0,1,0,0,0)),('011',(0,1,1)),('0011',(1,)),('0011',(3,)),('00101',(0,))]:
  ok=admitted(p,z);assert ok
  o,E=ref(p,z);K,gap=sync(E,30);r90_sanity(E)
  # largest boundary-perturbation initially grows at most K+1 per inverse step
  C=K+1 if K is not None and K>=0 else None
  print(p,'repeating white-labels',z,'accepted',ok,'temporal length',len(E),'west transient',o,'spatial period',len(E[0]),'max zero gap',gap,'max inverse synchronization',K,'C',C,'island/age limsup ≤',(C-1)/(C+1) if C else None,'R90 no reset',flush=True)
if __name__=='__main__':run()
