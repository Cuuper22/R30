"""A fixed old cut and high dyadic return give two same-row genuine black
launches, separated by an expanding vacuum. Do the launch codes really
reach the marked right tip at increasingly different times? Prove the
geometric bound and check the exact packet dynamics against R30 and R90.
A shared-arrival inference from the fixed 1101 prefix would now need to
overcome this actual source transfer, not an arbitrary local clock."""
from symbolic_fixed_cut_rim import G,vf
def delay(r,rule):
 a=w=0
 while r:
  if r&1:r>>=1
  elif r&2:r>>=2
  else:
   r>>=2;r=4*r^((r|2*r)if rule==30 else r);w+=1
  a+=1
  assert a<400000
 return w
def test(rule):
 S=[1]
 for _ in range(500):S.append(G(S[-1],rule))
 result=[]
 def E(r,t,x):
  # normalized right depth for a cell x is t−x, from east toward west.
  d=t-x;return int(format(r%2**d,f'0{d}b')[::-1],2)if d>0 else 0
 for u in range(0,10):
  if not(S[u]>>u&1):continue
  for Q in range(4,490,4):
   v=u+Q
   x=0
   if not(S[v]>>v&1):
    if rule==30:continue
    # For true singleton R90 the center is always white after age 0.
    # Use the closest black to its west instead to test vacancy crossing.
    x=-vf(S[v]>>v)
   d=vf(S[v]^S[u]);L=d-2*u-1
   if L<2 or d>=v:continue
   e0=E(S[u],u,0);e1=E(S[v],v,Q);en=E(S[v],v,x)
   assert e0==e1
   # Disjoint copy and head. The all-zero gap shrinks by at most 2
   # per ordinary tick; a zero belt of length >=2 blocks both black hops.
   old=delay(e0,rule);new=delay(en,rule);lower=L//2
   assert new>=lower,(rule,Q,u,L,lower,new)
   result.append((L,u,Q,x,old,new))
 print(rule,'real paired black launches (R90 permits noncentral later launch)',len(result),'largest certified gap (L,old age,lag,later start,copy delay,center delay)',max(result,default=None),flush=True)
if __name__=='__main__':test(30);test(90)
