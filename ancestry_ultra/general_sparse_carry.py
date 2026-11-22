"""Use ordinary binary carries on the two marked half tapes. Check the
exact isolated-mark advance on R30 through 500 and genuine matched R90.
If the periodic wall correction separates the two histories, carry it
over an entire strobe; if not, retain the sparse-sign obstruction."""
from general_characteristic_d4 import field
def isolated(v):return v&~(v>>1)&~(v>>2)
def test(r,p,N=500):
 at=field(r,p,N);bad=bad2=0;wh=[sum(at(t,-j-1)<<j for j in range(t+1))for t in range(N+1)]
 for t in range(N-1):
  w,v=wh[t:t+2];c,d,e=(at(t+i,0)for i in range(3));gamma=2*c*d*(1-2*e)
  bad+= w+2*v+(w%2)!=8*isolated(w)+gamma
  # Compare the whole normalized R30 row (R90 has initial infinite east;
  # test its actual three-site marking relation at bulk coordinates).
  for x in range(-30,31):
   # Normalized digit i at time t is x; two older digits below it
   # correspond to x+1,x+2. Written bit of output at x+1.
   a=at(t,x);n=at(t+1,x+1)
   carry=any(at(t,x+j) for j in (1,2,3));f=any(at(t,x+j)for j in (0,1,2))
   h=at(t,x+3)*(1-at(t,x+2))*(1-at(t,x+1))
   bad2+=a+n+carry != h+2*f
 print('rule,w,complete marked west arithmetic fails out of 499; local carry fails out of 30439',r,p,bad,bad2)
 assert (not bad and not bad2)==(r==30)
if __name__=='__main__':
 for p in ('01','011','00101'):
  for r in (30,90):test(r,p)

def naf(z):
 while z:
  d=(2-z%4) if z%2 else 0
  yield d;z=(z-d)//2
def signed(r,p,N=500):
 at=field(r,p,N)
 # Work inside the genuine finite cone for R30, compare local signed
 # digits on all three genuine Rule90 fields (R90 east is not cut).
 bad=badsep=0;origin=at(0,0)
 if r==30:
  z=1
  for t in range(N-1):
   zp=z^(2*z|4*z);zpp=zp^(2*zp|4*zp)
   ds=list(naf((zpp-z)//8))
   assert all(d==((isolated(zp)>>j)&1)-((isolated(z)>>j)&1)for j,d in enumerate(ds))
   z=zp
 for t in range(N-1):
  def mark(t,x):return at(t,x)*(1-at(t,x-1))*(1-at(t,x-2))
  for x in range(-30,31):
   bad+=mark(t,x)!=at(t,x)*at(t+1,x)*(1-at(t+2,x))
   if mark(t,x):badsep+=sum(mark(t+1,x+j)for j in(0,1,2))
 print('rule,w,spatial001-temporal110 fails / 30439; next-row forbidden contacts',r,p,bad,badsep)
 assert (bad==badsep==0)==(r==30)
if __name__=='__main__':
 for p in ('01','011','00101'):
  for r in (30,90):signed(r,p)
