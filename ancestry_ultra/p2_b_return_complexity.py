"""Check whether the absorbing true finite-east return sequence has a
small substitution/linear-complexity clock which would upgrade fixed-age
dyadic B returns to recurrence of the whole actual old finite west. If
word counts double at long scales, seek the source coupling instead."""
from collections import Counter
def go(R=1,N=140000):
 c=1;old=None;u=[];Bs=0
 for t in range(N):
  if c and R&15==11:
   if old is not None:u.append(int((t-old)//2==3))
   old=t
  R=(2*R+c)^(R|R>>1);c^=1
 u=u[300:];P=1;w=0;counts=[set()for _ in range(32)]
 for j,x in enumerate(u):
  w=2*w+x;w%=1<<32
  for k in range(min(32,j+1)):counts[k].add(w%(1<<(k+1)))
 print('finite east 1',len(u),'actual B gap-word complexities length 1..32',list(map(len,counts)))
if __name__=='__main__':go()
