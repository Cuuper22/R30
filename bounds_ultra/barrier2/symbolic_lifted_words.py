"""Test whether adding cells to the true 24899/82754 hosts strictly removes
B-return source signatures. A surviving unchanged dictionary sends us to
the original-source condition, while lost labels reduce the exact necessary
clocks at all sufficiently late onsets."""
from symbolic_q221_lift import *
from collections import defaultdict
def words(S,n):
 a,b,h=edges(S,n);N=len(S);A,B=a[h<0],b[h<0];terms={t:a[h==t]for t in(10,17,26)};dirs=defaultdict(set)
 for st in terms:
  V={0:np.unique(b[h==st])}
  for i in range(1,75):
   W={}
   for w,D in V.items():
    Z=S[D]&1
    for v in(0,1):
     F=D[Z==v]
     if not len(F):continue
     m=np.zeros(N,np.bool_);m[F]=1;k=2*w+v
     for te,t in terms.items():
      if m[t].any():dirs[st,te].add(format(k,f'0{i}b'))
     q=np.unique(B[m[A]])
     if len(q):W[k]=q
   V=W
   if not V:break
  assert not V
 return dirs
def run(n,s):
 S=gethost(n,s);ans=words(S,n)
 for k,v in sorted(ans.items()):print(k, sorted(map(len,v)),flush=True)
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]))
