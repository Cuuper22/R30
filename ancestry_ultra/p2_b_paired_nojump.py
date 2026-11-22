"""A finite true west makes every marked B path eventually free of
horizontal jumps. At each strobe the current white q bit independently
sets the next jump of the center path. Decode its forced continuation,
and check the paired neighboring B path and actual odd-gap language."""
from p2_pulse_inverse import decode
from p2_b_physical_repeats import qword
from p2_b_dyadic_replica import run
from collections import Counter
def jumps(w,n):
 a=0
 for i in range(n):
  v=w>>2;b=w&1
  if w&2:a|=1<<i;w=v
  else:w=v^(2*(v|2*v))^b
 return a
def hs(q):
 n=len(q)
 h=(1<<(2*n+1))-1
 for i,b in enumerate(q):
  if b:h^=2<<(2*i)
 return h
def extend(q,n):
 h=hs(q);out=[];v=[]
 for i in range(len(q),n):
  # Appended 1,1 from old 2i+1 through new 2i+2 means candidate q_i=0
  h|=3<<(2*i+1)
  w=decode(h,2*i+3);a=jumps(w,i+1)>>i
  w2=decode(h^(2<<(2*i)),2*i+3)
  assert jumps(w2,i+1)>>i==1-a
  if a:h^=2<<(2*i);w=w2
  out.append(a);v.append(jumps(w>>1,i+1)>>i)
 return out,v
def test():
 q=qword(1,4000)
 for old in (9,100,681):
  print('fixed finite east old',old)
  for k in (0,10,30,80,160,320):
   a,v=extend(q[old:old+k],k+100)
   on=[i for i,b in enumerate(a)if b];g=Counter(j-i for i,j in zip(on,on[1:]))
   print('jump cutoff',k,'new q gaps',dict(g),'paired west jumps',sum(v),'first',next((i for i,k in enumerate(v)if k),None),flush=True)
 run()
if __name__=='__main__':test()
