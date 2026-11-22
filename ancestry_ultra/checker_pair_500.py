"""Target mixed 513-bit observations for canonical vacuum-west / absolute
even-black checker-east rows with DIFFERENT leftmost marks inside the
observed causal cone. Use toolkit exact sideways elimination. Compare
forward evolution beyond H and discriminate finite from infinite aliases."""
import os,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'r30fast'))
import r30fast as kit
def west(c, E, rule):
 H=len(c);m=(1<<(H+3))-1
 R=[]
 for b in c:
  R.append(E&1);E=(((E<<1)|b)^((E|E>>1)if rule==30 else E>>1))&m
 cols=kit.sideways_rewind(c,R,H-1,rule)
 return sum(a[0]<<i for i,a in enumerate(cols))
def real(W, Efix, d, O, D, r):
 # W bit0 is x=-1, Efix is [1,d]. All x>d are initialized to
 # the ABSOLUTE physical even-black checker; all x<-W.bit_length blank.
 C,E0=Efix
 z=C<<O
 for i in range(W.bit_length()):z|=(W>>i&1)<<(O-i-1)
 z|=E0<<(O+1)
 for i in range(d+1,D+2):
  if not i%2:z|=1<<(O+i)
 tr=[]
 for _ in range(D+1):
  tr.append((z>>O)&1);z=(z<<1)^((z|z>>1)if r==30 else z>>1)
 return tr
def run(c,label,rule):
 H=len(c);d=10 if rule==30 else H-1
 checker=sum(1<<(i-1)for i in range(d+1,H+3)if not i%2)
 bits=[0,1,2,5,13,341,655%(1<<d)]
 if rule==90:bits=[0,1<<(d-1)]
 old=None
 for e in bits:
  W=west(c,e|checker,rule);D=H+140;tr=real(W,(c[0],e),d,D+2,D,rule)
  assert tr[:H]==list(c)
  if old is not None and W.bit_length()!=old[0].bit_length():
   Z,e0,tr0=old
   split=next((i for i,(a,b)in enumerate(zip(tr,tr0))if a!=b),None)
   print(rule,label,'H',H,'leftmarks',-Z.bit_length(),-W.bit_length(),'east finite width',d,'edits',hex(e0),hex(e),'west',hex(Z),hex(W),'first difference',split)
   return
  if old is None:old=(W,e,tr)
 raise AssertionError((label,rule,'no heterogeneous marks on test'))
if __name__=='__main__':
 H=513
 for p in('01','011','00101'):
  c=[int(p[i%len(p)])for i in range(H)]
  for r in(30,90):run(c,p,r)
 run(kit.sim_center(H-1,30),'true-singleton-center',30)
def singleton_pair(H=513):
 c=kit.sim_center(H-1,30);d=10;D=H+140
 ck=sum(1<<(j-1)for j in range(1,d+1)if not j%2)
 tail=sum(1<<(j-1)for j in range(d+1,H+3)if not j%2)
 assert west(c,ck|tail,30)==0
 Z=real(0,(1,ck),d,D+2,D,30)
 for flip in range(d):
  e=ck^(1<<flip);W=west(c,e|tail,30)
  if W:
   z=real(W,(1,e),d,D+2,D,30)
   assert z[:H]==Z[:H];end=next((i for i in range(H,D+1)if z[i]!=Z[i]),None)
   print('30 actual canonical Z0 vs true checker twin, H',H,'flip x',flip+1,'first needed negative edit',-(W&-W).bit_length(),'deepest',-W.bit_length(),'first split',end,'W',hex(W))
   return flip+1,W
if __name__=='__main__':singleton_pair()
