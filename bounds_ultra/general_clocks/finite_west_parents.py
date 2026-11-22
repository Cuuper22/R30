"""Finite first-parent table and a certified fan of backward histories from
one *actual* west tape. True vacuum beyond the western mark is compulsory.
Compare both rules and the four distinct clamped all-period observer drives.
Universal parenthood would permit minimal-width descent only if it survived
onto earlier nonrooted tapes; track exactly how far the marked cap certifies.
"""
from spatial_certificate import trans
from itertools import product
F={r:[[trans(s,b,r)for b in(0,1)]for s in range(16)]for r in (30,90)}
D={r:[[sum(1<<i for i in range(4)if F[r][1<<i][b]&s)for b in(0,1)]for s in range(16)]for r in F}
def roots(rule,N,p=None):
 z=1;rows=[]
 for t in range(N+1):
  rows.append(z)
  # Genuine normalized left cone restricted to the strict west, with known
  # center bit at old depth t. For the original singleton use the full row.
  if p is not None:
   c=1 if t==0 else int(p[(t-1)%len(p)]);z=(z&((1<<t)-1))|(c<<t)
  z=(4*z)^((2*z|z)if rule==30 else z)
 return rows
def scan(z,t,r):
 s=1
 for j in range(t):
  s=D[r][s][z>>j&1]
  if s in(0,15):return s,j+1
 return s,t
def guaranteed(rows,t,r):
 # Current common suffix starts at physical x=-1, x indexes the target bit.
 # Unknown internal head data are completely free. A singleton pair after
 # processing x pins the previous row all the way west; this includes x.
 # In the next older layer initiate at x-1, using the previous pair as true
 # common target data, with entirely unconstrained entering predecessor pair.
 x=-1;age=t;S=15;z=rows[t];res=0
 while age>0 and x>=-age:
  bit=z>>(x+age)&1;S=F[r][S][bit];x-=1
  if S.bit_count()==1:
   res+=1;S=15;age-=1;z=rows[age]
 return res

def run():
 for p in(None,'01','011','0011','00101'):
  for r in (30,90):
   V=roots(r,500,p);C=[scan(z,t,r)for t,z in enumerate(V)]
   print('finite-west roots',p or 'singleton',r,'fully predecessor-flexible ages 8..500',sum(s==15 for s,k in C[8:]),'outer cap max resolution',max(k for s,k in C[8:]),'certified free (center,head)-pair past depths at 100,200,300,400,500',[guaranteed(V,t,r)for t in(100,200,300,400,500)],flush=True)
 # A finite preimage for each independently prescribed old center/head exists
 # iff the scanned left tail enters 00. The true normalized rim patterns:
 for v,m in[(0x13,6),(0x7b,8)]:assert scan(v,m,30)==(15,m)
 print('universal finite-parent rim masks: low 6=0x13 or low 8=0x7b; all four entering pairs pass')
if __name__=='__main__':run()
