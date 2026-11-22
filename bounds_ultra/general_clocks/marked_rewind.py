"""How much future mask, together with the *actual* finite current east
slice, certifies the old singleton's marked western front even if one
ignores the current eastern vacuum? Rewinds are only credited after a
genuine four-pair inverse reset. An early certified rim gives a root
test invisible to either entropy count alone; compare true Rule90."""
from spatial_certificate import trans
def rows(rule,N):
 z=1;R=[]
 for t in range(N+1):
  R.append(z);z=4*z^((2*z|z)if rule==30 else z)
 return R
def rewind_count(R,t,lo,rule):
 # Query at age t-s and physical x=t-j-s, so normalized LEFT depth x+t-s.
 # Its normalized EAST depth is j. Stop where the inherited left endpoint
 # lo-s meets the next probe. No observed western bit beyond lo is used.
 S=15;s=0
 for j in range(t-lo+1):
  x=t-j-s;age=t-s;idx=x+age
  b=(R[age]>>idx&1) if idx>=0 else 0
  S=trans(S,b,rule)
  if S.bit_count()==1:
   s+=1;S=15
 return s
def run(rule):
 N=500;R=rows(rule,N);dat=[]
 for t in range(40,N+1):
  lo,hi=0,t
  while lo<hi:
   m=(lo+hi)//2;s=rewind_count(R,t,-m,rule)
   if m+2*s>=t:hi=m
   else:lo=m+1
  m=lo;s=rewind_count(R,t,-m,rule);dat.append((t,m,s))
 print('marked rule',rule,'(age,needed future masked ticks,guaranteed full-pair rewinds)',[v for v in dat if v[0]in(50,100,200,300,400,500)],'m/age range t>=100',min(m/t for t,m,s in dat if t>=100),max(m/t for t,m,s in dat if t>=100),flush=True)
if __name__=='__main__':
 for r in (30,90):run(r)
