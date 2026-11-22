"""The marked online map on oriented temporal words also has an exact
binary recursion on the whole prefix tree. Check every link on real
singleton and independent same-pattern R90. A true ordinary west vacuum
rules out a universal finite-state reader, without imposing any onsets."""
from general_characteristic_d4 import field

def test(r,p,N=500):
 at=field(r,p,N);ok=bad=constant=0;examples=[]
 for x in range(2,31):
  n=N-x-2
  low=(1<<n)-1
  def u(d):return sum(at(k+d,d)<<k for k in range(n))
  a,b,c=map(u,(x-1,x,x+1));w=(b^((b<<1)|(c<<2)))&low
  # The low two boundary bits pertain to the right ray; the R90 control
  # has nonempty initial east, so ignore them for its bulk falsification.
  d=((a^w)&low)>>2;bad+=d.bit_count();ok+=n-2-d.bit_count()
 print('oriented temporal-orbit identity (bulk) rule/pattern pass/fail',r,p,ok,bad)
 assert (r==30)==(not bad)
 if r==90:
  C=lambda t:at(t,0);q=[at(t,1) if not C(t) else 0 for t in range(501)];P=len(p)
  for k in(1,2,4,8):
   z=[t for t in range(1,501-P*k)if q[t]!=q[t+P*k]];examples.append((P*k,len(z)))
  print('independent same-pattern R90 actual masked lag mismatches',p,examples)

def vacuum():
 # Two real oriented traces at x=-d and x+1 from the full-space singleton.
 # Read the ordinary physical times starting from 0 in two-tick blocks:
 # output is at time+1 (one horizontal move), so for even d=2h an initial
 # h-1 allzero-output blocks precede the changed output on another 00.
 for d in(20,100,200,400):
  at=field(30,None,500);x=-d
  obs=[(at(t,x)+2*at(t+1,x),at(t+1,x+1)+2*at(t+2,x+1))for t in range(0,d,2)]
  assert all(w==0 for w,z in obs)and all(z==0 for w,z in obs[:-1])and obs[-1][1]
  print('actual negative-column unary input,first changed output pair since row0',d,len(obs),obs[-1])
if __name__=='__main__':
 for p in('01','011','00101'):
  for r in(30,90):test(r,p)
 vacuum()
