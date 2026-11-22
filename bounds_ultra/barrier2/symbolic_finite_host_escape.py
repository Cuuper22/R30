"""Probe finite-right escape for the surviving nonabsorbing B hosts. If a finite exterior remains inside for long, finite support by itself does not give a short uniform exit. If all escape, classify how the exit time depends on the rightmost nonvacuum bit, targeting a right-tail descent rather than more width growth."""
from symbolic_q221_lift import *
def run(n,d,lim):
 S=gethost(n,d);V=list(map(int,S));domain=set(V);m=(1<<n)-1
 from collections import Counter
 vals=[(r,r)for r in V];H=Counter()
 for tick in range(1,lim+1):
  nxt=[]
  for root,r in vals:
   y=(2*r)^(r|r>>1);z=(2*y+1)^(y|y>>1)
   if z&m in domain:nxt.append((root,z))
   else:H[tick]+=1
  vals=nxt
  if tick in(10,25,50,100,250,500,1000)or not vals:print('host',d,'strobes',tick,'survival',len(vals),'example',[hex(i)for i,_ in vals[:2]],flush=True)
  if not vals:break
 print('longest dead',max(H,default=0),'last deaths',sorted(H.items())[-10:],flush=True)
if __name__=='__main__':run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]))
