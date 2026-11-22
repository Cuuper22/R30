"""All-period right-strip capacity and translated spatial parser pressure.
Check against genuine truth-table strip dynamics on all four drives, for
Rule90 separately. Only R30 ignores the new exterior bit on black endpoint."""
import numpy as np
from spatial_certificate import autom
from math import log2,sqrt
def fib(n):
 a,b=0,1
 for i in range(n):a,b=b,a+b
 return a
def trajectories(p,d,k,rule):
 mask=(1<<d)-1;G={1:1}
 for j in range(k):
  c=int(p[j%len(p)]);K={}
  for s,n in G.items():
   Y={((2*s+c)^(((s|((s>>1)|(b<<(d-1))))if rule==30 else ((s>>1)|(b<<(d-1))))))&mask for b in (0,1)}
   for v in Y:K[v]=K.get(v,0)+n
  G=K
 return sum(G.values())
if __name__=='__main__':
 phi=(1+sqrt(5))/2
 for p in ('01','011','0011','00101'):
  for d in (1,4,7):
   N=30;z=trajectories(p,d,N,30);g=trajectories(p,d,N,90);assert z<=fib(N+2)and g==1<<N
   print('clock',p,'strip',d,'initial east 1; genuine branching traces at n=30',z,'Fibonacci cap',fib(N+2),'R90',g)
 _,_,A=autom(30);A=A.astype(float);A[7,0]=phi;r=max(np.linalg.eigvals(A).real)
 print('translated spatial PF',r,'bits/site',log2(r),'strip temporal bound',log2(phi),flush=True)
