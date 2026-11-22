"""Use the EXACT all-drive quotient instead of an arbitrary fixed collar:
do section updates on moving-edge clocks. Verify on matched true controls,
and test cancellation/period information needed by the actual w closure."""
from general_characteristic_d4 import field

def go(r,p,N=500):
 at=field(r,p,N);h=n=0;bad=0;bad2=0
 for t in range(1,300):
  c=at(t,0);z=c
  # Labels obtained from rows independently; no artificially free clocks.
  for j in range(N-t):
   a=at(t+j,j+1);b=at(t+j,j+2);m=a|b
   z^=m
   az=at(t+j+1,j+1);bz=at(t+j+1,j+2);a1=at(t+j+1,j+2)
   bad+=z!=az;bad2+=(z|a1)!=(az|bz);n+=1
 print('rule,pattern,seam quotient updates, OR lower/upper failures',r,p,n,bad,bad2)
 assert (bad==bad2==0)==(r==30)
def main():
 for p in ('01','011','00101'):
  for r in (30,90):go(r,p)
if __name__=='__main__':main()

def period_growth():
 # On the finite cap permutation, compute each orbit once, not once per
 # tape. At any ore where m has odd weight over D, both phases of a' occur
 # and weight(m') over 2D is D+weight(a). A second doubling gives the
 # next-old a weight D, precluding a third doubling for even D.
 for r in (30,90):
  N=16; seen=bytearray(1<<N);per=[0]*len(seen)
  for x in range(len(seen)):
   if seen[x]:continue
   y=x;orb=[]
   while not seen[y]:
    seen[y]=1;orb.append(y)
    y^=((y>>1)|(y>>2))if r==30 else y>>2
   assert y==x
   for q in orb:per[q]=len(orb)
  vals=[]
  for q,D in enumerate(per):
   if per[q>>3]>1 and D==8*per[q>>3]:vals.append(q)
  print('all finite cap widths through',N,'rule',r,'triple dyadic period doublings above period 1:',len(vals),'max period',max(per))
  assert not vals
if __name__=='__main__':period_growth()
