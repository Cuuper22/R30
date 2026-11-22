"""Hard Step4: do repeated marked rim returns leave absolute time windows
that NO central packet, regardless of its launch age, can first hit?
If yes, a bounded *jump* of the terminal time between consecutive P2/B
launches (weaker than exact merger) suffices to contradict rootedness.
Control the purely kinematic part on true singleton R90 as well."""
from symbolic_fixed_cut_rim import G,vf
from symbolic_copy_arrivals import delay
def go(rule=30,N=500):
 A=[1]
 for _ in range(N):A.append(G(A[-1],rule))
 # Include every central black for Rule30. R90 has white centers, so test
 # every closest true black on the west side at that age instead.
 out=[]
 for t,v in enumerate(A):
  x=0 if v>>t&1 else (-vf(v>>t)if rule==90 else None)
  if x is None:continue
  z=t-x;sr=int(format(v%(1<<z),f'0{z}b')[::-1],2)if z else 0
  out.append((t,t+delay(sr,rule)))
 pos=[]
 for Q in range(1,N):
  d=vf(A[Q]^1);L=(d-1)//2
  if Q<d or Q+L>N or not L:continue
  pre=A[Q-1]%2**d
  if rule==30:assert pre==(1<<d)-1
  else:assert pre==sum(1<<i for i in range(0,d,2))
  assert all(not Q<=a<Q+L for _,a in out)
  if L>=min(10,N//10):pos.append((Q,d,L))
 print('rule',rule,'true west/center launches',len(out),'forbidden contact intervals of size ≥10: Q,d_r,length',pos,flush=True)
if __name__=='__main__':go();go(90)
