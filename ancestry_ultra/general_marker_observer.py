"""Test whether the signed displacement of the two FULL rows recovers the
entire unresolved white read through the two nearest marker lanes. If
it decodes, transfer the residual periodicity question to interval hits
of the scalar; if not, isolate the endpoint or orientation counterexample."""
from general_characteristic_d4 import field
def test(rule,pat,N=500):
 v=field(rule,pat,N);fail=marks=blocks=reads=wrong=0;K=2*N+4;D=1<<K
 # A marked Rule90 control's true east half is infinite: the exact causal
 # triangle gives these local markers. For its scalar check use dyadic
 # truncation with a verified guard away from threshold, not an implicit
 # assumption of east vacuum.
 ms=[]
 for t in range(N+1):
  m=lambda x: v(t,x)*(1-v(t,x-1))*(1-v(t,x-2))
  ms.append((m(1),m(2)))
 scale=1<<12
 for t in range(N-1):
  # Use bits -4..12 of each V. The omitted east values <2^-12
  # (<= when general R90 east); deep west is 0 mod16.
  def sv(t):return sum(v(t,x)<<(12-x) for x in range(-4,13))
  a=4*sv(t+2)-sv(t)
  for j in (1,2):
   # 2^j (4 V_next2 - V)/8 mod4; numerator uncertainty
   # less than 4*2^j on the common 8*scale denominator.
   h=((a<<j)*3)%(96*scale);u=(4<<j)*3
   if min(abs(h-64*scale),abs(h-80*scale))<=u:continue
   yes=int(64*scale<h<80*scale);wrong+=yes!=ms[t][j-1];marks+=1
 t=0
 while t<N:
  if v(t,0):t+=1;continue
  e=t
  while e<N and not v(e+1,0):e+=1
  if e>=N:break
  q=ms[e][0];blocks+=1
  for i in range(e,t-1,-1):
   if i<e:q-=ms[i][1]
   fail+=q!=v(i,1);reads+=1
  t=e+1
 print(rule,pat,'two-marker white-read fails',fail,'/',reads,'in runs',blocks,'signed interval fails',wrong,'/',marks)
 assert (fail==0 and wrong==0)==(rule==30)
if __name__=='__main__':
 for p in ('01','011','00101'):
  for r in (30,90):test(r,p)
