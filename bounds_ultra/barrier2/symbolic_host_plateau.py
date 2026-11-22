"""Do the genuine lifts still permit arbitrarily long intervals in each
apparent q7 and 3/5 phase? If a projected periodic domain dies inside the
q-variable component, every true tail must switch in bounded time; use
that forced signed interface. A surviving cycle falsifies that bound."""
from symbolic_q221_lift import *
def periodic(S,n,q,lim=500):
 a,b,_=edges(S,n);N=len(S);bit=S&1;A=[a[bit[a]==int(z)]for z in '01'];B=[b[bit[a]==int(z)]for z in '01'];V=np.ones(N,dtype=np.bool_);i=0
 for k in range(lim):
  size=int(V.sum())
  for c in q:
   c=int(c);U=np.zeros(N,np.bool_);U[B[c][V[A[c]]]]=1;V=U;i+=1
   if not V.any():return 'no path by',i
  if int(V.sum())==size:return 'unbounded at',i,'recurrent entry states',size
 return 'unknown',i,int(V.sum())
def run(n,d):
 S=gethost(n,d)
 for w in ('010','01000','010010000','0100001','01000010','010000101010100','010100','0100001001000'):
  print(n,d,w,periodic(S,n,w),flush=True)
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]))
