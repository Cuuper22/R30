"""At the replica's first actual center slip, ask whether its incoming
black packet really comes from a copied rim lane, as opposed to a local
birth. Track all occupied B paths; if too few survive, use the closed
form for origins possible in BOTH actual histories at the flipped lane."""
from p2_b_dyadic_replica import step,valuation
def table(R,D):
 U=[[0]*(D+1)for _ in R]
 for t,v in enumerate(R):
  for j in range(D+1):
   if not(v>>j&1):continue
   if j<2:U[t][j]=1<<t
   else:U[t][j]=U[t][j-2] | (U[t-1][j-2] if t and not(R[t-1]>>j&1) else 0)
 return U
def go(hi=21):
 v=1;mask=(1<<(hi*4+30))-1;O=[1]
 for t in range(hi*4+31):O.append(step(O[-1],30))
 obs=[]
 for s in range(1,(1<<hi)+1):
  v=step(v,30)&mask
  if s&(s-1):continue
  r=s.bit_length()-1;k=valuation(v^1);assert k>0
  A=[v];m=(1<<(k+1))-1
  for i in range(k+1):A.append(step(A[-1],30)&m)
  assert all((a^b)&m==1<<k for a,b in zip(A,O))
  u,w=table(A,k),table(O[:len(A)],k)
  n=k;real=A[n]>>k&1
  aa,ab=u[n][k],w[n][k]
  before=n-1
  options=(u[n][k-2] if k>=2 else 0,u[n-1][k-2] if k>=2 else 0)
  obs.append((r,k,real,aa.bit_count(),ab.bit_count(),*(x.bit_count()for x in options)))
 print('r,k,satellite black-at-slip,number of actual/old rim births reaching that slip,upstream current/previous birth counts',obs)
 # A genuine R90 center-1010 control (marked blank-left; see matched row500 check) lacks raw B reset.
 from p2_b_dyadic_replica import run
 run()
if __name__=='__main__':go()
