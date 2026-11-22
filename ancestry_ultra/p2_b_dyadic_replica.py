"""Tie high-v2 returns to a genuine singleton replica, not an abstract
dyadic color. Verify the two actual marked dynamics through row500 and
separate the exact recurring right rim from the generally transient left.
The fixed-old simultaneous B conclusion is conditional on infinite P2."""
def step(x,rule):return x^((2*x|4*x)if rule==30 else 4*x)
def valuation(x):return (x&-x).bit_length()-1
def run():
 x=1;A=[]
 for t in range(501):A.append(x);x=step(x,30)
 for Q in (2,4,8,16,32,64,128,256):
  k=valuation(A[Q]^A[0]);assert all(valuation(A[t+Q]^A[t])==k for t in range(501-Q))
  print('actual right rim physical lag, number of initial bits fixed for all available old rows',Q,k)
 # Genuine marked-blank-left R90 control has alternating center but no B=1101 in 251 black ticks.
 N=500;O=N+8;v=(1<<O)|sum(1<<(O+j)for j in range(1,2*N+2)if j%6 in(2,4));cc=hits=0
 for t in range(N+1):
  assert v>>O&1==1-(t&1)
  if not t&1:cc+=1;hits+=(v>>(O+1)&15)==11
  v=2*v^(v>>1)
 assert not hits and cc==251
 print('real R90 alternating black ticks with requisite B',hits,'/',cc)
if __name__=='__main__':run()
