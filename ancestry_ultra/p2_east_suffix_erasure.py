"""Can a finite outer suffix be removed once and for all before an
arbitrary inner right tape, independently of the P2 observer? Two
outer caps with identical incoming action at their moving seam have
the same entire inner field. Separate actual erasable caps from a
failure of uniform suffix induction; no host-width lifting."""
import numpy as np
def test(m,rule):
 S=np.arange(1<<m,dtype=np.int64);mask=(1<<m)-1
 G=(S^((2*S|4*S)if rule==30 else 4*S))&mask
 # Boundary j=m needs OR of the last two cap bits. At j=m+1 the
 # only unknown is last cap bit; it suffices to match that bit exactly.
 a=(S>>(m-1))&1;b=(S>>(m-2))&1
 obs=(2*a+(a|b)) if rule==30 else (2*a+b)
 c=obs
 p=G
 for k in range(m+1):
  d=c[p];sz=int(c.max())+1
  _,new=np.unique(c*sz+d,return_inverse=True)
  if len(np.unique(c))==int(new.max())+1:c=new;break
  c=new;p=p[p]
 even=np.zeros(int(c.max())+1,bool);even[c[::2]]=1
 ix=np.flatnonzero(even[c[1::2]])*2+1
 if len(ix):
  s=int(ix[0]);t=int(np.flatnonzero(c[::2]==c[s])[0])*2
  ex=(hex(s),hex(t))
 else:ex=None
 print('rule',rule,'cap width',m,'erasable high-one starts',len(ix),'/',1<<(m-1),'example reversed outer words',ex,'distinct full seam-action classes',int(c.max())+1,flush=True)
if __name__=='__main__':
 for rule in(30,90):
  for m in (3,4,5,6,7,8,9,10,12,14,16,18):test(m,rule)

def physical_control(N=500,D=21):
 O=2*N+32;M=(1<<(2*O+1))-1
 # Mirrored genuine six-periodic R90 control has finite right support.
 bg=(1<<O)|sum(1<<(O-i)for i in range(1,O)if i%6 in(2,4))
 def sym(i):return (1<<(O+i))|(1<<(O-i))
 for rule in(30,90):
  if rule==90:
   a=bg^sym(D)^sym(D-1);b=bg^sym(D-1)
  else:a=(1<<(D-1))|(1<<(D-2))|37;b=(1<<(D-2))|37
  mism=0
  for t in range(N+1):
   if rule==90:
    assert (a>>O&1)==(b>>O&1)==1-(t&1)
    ds=(a^b)>>(O+1)
    a=((2*a)^(a>>1))&M;b=((2*b)^(b>>1))&M
   else:
    ds=a^b;c=1-(t&1)
    a=(2*a+c)^(a|a>>1);b=(2*b+c)^(b|b>>1)
   mism+=bool(ds% (1<<(D-2+t)))
  print('physical rule',rule,'same-inner-cone violations through row500',mism,flush=True)
  assert (mism==0)==(rule==30)
if __name__=='__main__':physical_control()
