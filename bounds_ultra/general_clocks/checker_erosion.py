"""Does iterating the one-row checker inverse use a genuinely sharp slope
four, or is a near-unit cutoff available for comparing to the fixed old mark?
Try a true leftmost deviation advancing at speed 4, not independent layer
worst cases. A surviving long witness refutes finite shortcuts. Failure bounds
the allowed maximal displacements by a block inequality."""
from pathlib import Path
import itertools,subprocess
from finite_tail_merger_sat import SOL
def test(k,d,n=0,tm=10):
 # odd x=1 first departure to the east of a left checker half; x=0 is a
 # black stable wall under rightward perturbations. Constrain final x≤d
 # checker so net displacement is at least d (first departure=1 originally).
 D=(d+k+4);G={(t,j):1+t*D+j for t in range(k+1)for j in range(1,D-t)};V=[]
 def b(t,j):return bool(1-(j&1)) if j<=0 else G[t,j]
 def nt(x):return not x if type(x)==bool else -x
 def cl(v):
  if any(type(q)==bool and q for q in v):return
  V.append([q for q in v if type(q)!=bool])
 cl([b(0,1)])
 for t in range(k):
  for j in range(1,D-t-1):
   a,m,h,y=b(t,j-1),b(t,j),b(t,j+1),b(t+1,j)
   for g,v,w in itertools.product((0,1),repeat=3):
    m1=g^(v|w);cl([nt(a)if g else a,nt(m)if v else m,nt(h)if w else h,y if m1 else nt(y)])
 for j in range(1,d+1):cl([nt(b(k,j))if j%2 else b(k,j)])
 Q='p cnf %d %d\n'%(max(G.values()),len(V))+''.join(' '.join(map(str,v))+' 0\n'for v in V)
 try:r=subprocess.run([SOL,'-q'],input=Q,text=True,stdout=subprocess.PIPE,timeout=tm)
 except subprocess.TimeoutExpired:return 'unknown'
 if r.returncode==20:return 'unsat'
 assert r.returncode==10
 a={int(j)for l in r.stdout.splitlines()if l.startswith('v ')for j in l[2:].split()if int(j)>0};E=sum((b(0,j) in a)<<(j-1)for j in range(1,D));z=E
 for j in range(k):z=(2*z+1)^(z|z>>1)
 assert (E&1) and all((z>>(j-1)&1)==1-j%2 for j in range(1,d+1))
 return 'sat '+hex(E)
if __name__=='__main__':
 for k in(2,3,4,5,8,11,16,25,40):
  x=test(k,4*k);print('genuine checker erosion',k,'lambda4',x,flush=True)
  if x=='unsat':
   for d in range(4*k-1,3*k-1,-1):
    v=test(k,d);print('nearby bound',k,d,v,flush=True)
    if v.startswith('sat'):break
   break
