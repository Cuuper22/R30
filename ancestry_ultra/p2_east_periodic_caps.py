"""Search for a full periodic H-channel whose finite east truncation
can itself stay there. An incoming physical shift of its vacuum edge
rules out an all-support cutoff; outward shielding yields an actual
finite-right counterexample to the bare 'must escape' claim."""
import json,numpy as np
from pathlib import Path
def ether(w,cap=100000):
 p=2*len(w);mask=(1<<p)-1
 a=sum(1<<(2*i)for i in range(len(w)));b=a+sum((1-int(q))<<(2*i+1)for i,q in enumerate(w))
 # strictly west H and the center serve as the seed pair
 A=[];seen={}
 while (a,b)not in seen and len(A)<cap:
  seen[a,b]=len(A);A.append(a)
  a,b=b,((b>>1)|((b&1)<<(p-1)))^(a|b)
 if (a,b)not in seen:return None
 k=seen[a,b]
 if k:return ('transient',k,len(A)-k)
 return ('cycle',len(A),A)
def run():
 J=json.loads((Path(__file__).parent/'p2_b_next_words.json').read_text())
 for n,N in ((25,24899),(34,82754)):
  H=set(map(int,np.load('/tmp/r30a_bhost_%s_%s.npy'%(n,N))));D=J[str(N)]
  calls=[]
  def rec(i,u,w,l,pre):
   for v,W in D[u].items():
    for s in W:
     z=w+s
     if len(z)>26:continue
     if v==i and z!=pre:calls.append(z)
     if l:rec(i,v,z,l-1,z)
  for k in D:rec(k,k,'',2,'')
  for w in sorted(set(calls),key=lambda x:(len(x),x)):
   z=ether(w)
   if z is None or z[0]!='cycle':
    if len(w)<=16:print(N,w,None if z is None else z[:3])
    continue
   A=z[2];s=len(A);e=sum(((A[-(j%s)]>>1)&1)<<(j-1)for j in range(1,n+1))
   print('physical ether',N,w,'spatial',s,'white head',hex(e),'in host',e in H,flush=True)
if __name__=='__main__':run()
