"""Test the actual two marked B particles against the complete isolated
3/5 envelope. Bound each total jump budget, rather than inspect an arbitrary
finite known onset. Each next prescribed q exactly decides the central
jump bit. If sparse-jump grammar paths exist, extract the cheapest words
and their paired particle states for a proof or a discriminating witness."""
from symbolic_fork_reflector import W
def decode(q):
 n=len(q);cur=(1<<(2*n+1))-1
 for i,b in enumerate(q):cur^=int(b)<<(2*i+1)
 y=0;a=0
 for j in range(2*n+1):y+=int(cur&1)<<j;a,cur=cur,(cur>>1)^(cur|a)
 return y
def js(w,n):
 s=0
 for j in range(n):
  v=w>>2
  if w&2:s+=1<<j;w=v
  else:w=v^(2*(v|2*v))^(w&1)
 return s
def zrun(x,n):
 best=(0,-1);k=0
 for i in range(n):
  if x>>i&1:k=0
  else:k+=1;best=max(best,(k,i-k+1))
 return best
def results(depth):
 states=[('','')];m={}
 for i in range(1,depth+1):
  states=[(gs+str(h),q+'010'+'0'*(h-3))for gs,q in states for h in (3,5) if h!=3 or not gs.endswith('3')]
  best=(9999999,None);rare=(9999999,None);dry=(0,None);defect=(9999999,None)
  for gs,q in states:
   n=len(q);w=decode(q);a=js(w,n);b=js(w>>1,n);cost=(a|b).bit_count();st,lo=zrun(a|b,n)
   ob=(cost,gs,a.bit_count(),b.bit_count())
   if ob<best:best=ob
   if i>=3:
    cut=len(q)//2;ob=(((a|b)>>cut).bit_count(),gs)
    if ob<rare:rare=ob
   if st>dry[0]:dry=(st,(gs,lo))
   # cumulative jump *difference* determines the true terminal separation.
   j=a.bit_count()-b.bit_count();ob=(abs(2*j-1),gs,j)
   if ob<defect:defect=ob
  print('tiles',i,'states',len(states),'min jumps (union)',best,'min last-half cost',rare,'max joint dry strobe run',dry,'closest paired labels',defect,flush=True)
if __name__=='__main__':results(18)
