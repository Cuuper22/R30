"""Convert exact zero-extension exits into certificates on infinite
cylinders of arbitrary higher suffix. The first suffix black in any
genuine survivor must fall within the backward causal aperture determined
by the old host head, not simply within twice its escape time."""
import sys
from pathlib import Path
sys.path.append(str(Path(__file__).resolve().parents[1]/'bounds_ultra'/'barrier2'))
from symbolic_finite_host_traps import setup
from p2_b_recur_host import np
def f(r,c):return (2*r+c)^(r|r>>1)
def typ(H,n):
 A=[set()for _ in range(n+1)]
 for i in range(n+1):A[i]={r%2**i for r in H}
 return A
def leaf(r,S,M,T,A,steps=5000):
 n=M.bit_length();seq=[];v=r;t=0
 while (v&M) in S and (not T or (v&0x7fffffff)not in T):
  seq.append(v);v=f(v,0);seq.append(v);v=f(v,1);t+=1
  if t>steps:raise RuntimeError(hex(r),steps)
 kind='trap'if (v&M)in S else 'escape'
 if kind=='escape':
  k=next(i for i in range(n+1)if v%(1<<i)not in A[i])
 else:k=31
 target=k
 for old in reversed(seq):
  if not(old>>(k-1)&1):k+=1
 return max(k-n,0),t,kind,target
def go(n,N):
 from collections import Counter
 S=set(map(int,np.load('/tmp/r30a_bhost_%s_%s.npy'%(n,N))));T=setup()if N==24899 else set();M=(1<<n)-1;A=typ(S,n)
 vals=[(leaf(r,S,M,T,A),r)for r in S]
 for k in('trap','escape'):
  R=sorted((d,t,r,target)for (d,t,kind,target),r in vals if kind==k)
  if R:print('existing width,host,fate,n,exact incoming extra-zero radius quantiles (0,.5,.9,.99,1),worst word',n,N,k,len(R),[R[int(v*(len(R)-1))][:2]for v in(0,.5,.9,.99,1)],hex(R[-1][2]),'zero extras itself sufficient',sum(d==0 for d,_,_,_ in R),flush=True)
 return vals
if __name__=='__main__':
 go(25,24899);go(34,82754)
