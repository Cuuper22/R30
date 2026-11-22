"""Can an invisible temporal difference of two finite spatial perturbations
have the marked lag's exact exterior imbalance a+b=-2? First test permanently
checker west: a hit makes true vacuum west essential; otherwise try a
structural radius bound before a second vacuum-west computation."""
def check(D,rule,N=120):
 M=(1<<(2*D+1))-1;o=N+D+3;mask=(1<<(o+N+D+8))-1;chi=sum(1<<(o+i)for i in range(-o,o+3) if i%2==0)&mask
 groups={}
 for s in range(1<<(2*D+1)):
  z=chi^(s<<(o-D));c=0;last=None;per=False
  for t in range(N):
   c|=((z>>o&1)<<t)
   # If at least a single column x<=0 is a permanently locked black anchor
   # all the way to center, every more eastern choice preserves black center.
   if rule==30 and ((z^chi)&((1<<(o+1))-1)&~((1<<t)-1))==0:
    c|=((1<<N)-(1<<t));last=t;per=True;break
   z=((2*z)^((z|z>>1)if rule==30 else z>>1))&mask
  if not per:continue
  for v,t in groups.setdefault(c,[]):
   d=s^v;a=(d&-d).bit_length()-1-D;b=d.bit_length()-1-D
   if a+b==-2 and a<0<b:
    print('R30 permanent rigorous invisible perturbations of full checker',D,'local XOR masks',hex(s),hex(v),'difference endpoints',a,b,'permanent checker times',last,t,'early center',format(c&((1<<max(last,t))-1),'0%db'%max(last,t))[::-1]);return True
  groups[c].append((s,last))
 return False
if __name__=='__main__':
 for d in (2,3,4,5,6,7):
  if check(d,30):break
