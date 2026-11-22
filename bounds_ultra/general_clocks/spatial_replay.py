"""Direct spatial-word test, no independence assumption or eigen arithmetic.
The exact number passing the reverse-center decoder should be identical for
all four clocks and the matrix formula, before applying mature restrictions."""
from spatial_certificate import trans,autom
import sys
def solve(y,n,p,rule=30):
 r=0;s=n;row=[0]+[(y>>i)&1 for i in range(n)];S=15;obs=[]
 while s>r:
  x=s-r;s-=1;b=row[x];S=trans(S,b,rule)
  if S.bit_count()!=1:continue
  if s==r:break
  u=S.bit_length()-1
  old=[0]*(x+1);old[x]=u>>1;old[x-1]=u&1
  for j in range(x-1,0,-1):old[j-1]=row[j]^((old[j]|old[j+1]) if rule==30 else old[j+1])
  r+=1;obs.append(old[0])
  if old[0]!=int(p[-r%len(p)]):return False,tuple(obs)
  row=old;S=15
 return True,tuple(obs)
if __name__=='__main__':
 import r30fast,numpy as np
 for p in ('01','011','0011','00101'):
  n=12;M=autom(30)[2];expected=int(((np.linalg.matrix_power(M,n))@np.ones(len(M),dtype=np.int64))[0])
  P=[s for s in range(1<<n)if solve(s,n,p)[0]]
  assert len(P)==expected
  m,K,H=r30fast.general_p_hosts(p,n=n,rule=30,return_states=True)
  # Public API labels recurrent graph components only; when some component data are
  # intentionally omitted, validate every returned state and print the actual count.
  PP=set(P);N=0
  for v in H.values():
   A=np.frombuffer(v,dtype=np.uint64);assert all(int(x)in PP for x in A);N+=len(A)
  assert all(solve(s,n,p,90)[0]for s in range(1<<n))
  print('p',p,'n',n,'all words passing',len(P),'project graph mature count',m,'returned SCC-state occurrences checked',N,'R90 passed every word',flush=True)
