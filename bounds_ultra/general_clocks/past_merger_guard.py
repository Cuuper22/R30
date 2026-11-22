"""At each white of a genuinely matured mixed drive, is its old masked bit
already determined by the next entire n-site east prefix? Nonempty pairs
are strip candidates, not full lifts; an empty intersection is a uniform
full-space injectivity theorem instead of a finite onsets test. Rule90 has
its own free input language and update."""
import numpy as np,sys
def js(V,c,n,r):
 m=(1<<n)-1;W=V>>1;A=(2*V+c)
 O=(V|W)if r==30 else W
 X=(A^O)&m;Y=(A^((O|1<<(n-1))))&m
 return np.union1d(X,Y)
def find(p,n,r):
 S=np.arange(1<<n,dtype=np.uint32);P=list(map(int,p))
 cycles=0
 while True:
  V=S
  for c in P:V=js(V,c,n,r)
  if len(V)==len(S):break
  S=V;cycles+=1
 for ph,c in enumerate(P):
  old=S;S=js(S,c,n,r)
  if c:continue
  U=np.intersect1d(js(old[old%2==0],c,n,r),js(old[old%2==1],c,n,r))
  print('mature inverse merger,',p,'r',r,'width',n,'physical burn-in ≤',cycles*len(p)+ph,'white ph',ph,'ambiguous #',len(U),'first',hex(int(U[0]))if len(U) else '-',flush=True)
if __name__=='__main__':
 for p in('01','011','0011','00101'):
  for n in(12,16,20):find(p,n,30)
  find(p,12,90)
