"""Does the proposed small rational comparator recur at arbitrarily high
2-adic precision on host 58203? If no, identify its exact annuli and the
correct pure-five comparator for long unbroken stretches; it must not be
used as a common fixed point of the two distinct tile branches."""
from symbolic_fork_reflector import W,ref,val2
from itertools import product
F=ref('010000','10')[0];P=ref('','01000')[0]
def go():
 trials={}
 for k in range(8):
  for s in product((3,5),repeat=k):
   h=(5,)*k+(3,5)+s;w=''.join('010'+'0'*(x-3)for x in h)
   z=W(w)
   e=val2(F.denominator*z-F.numerator);p=val2(P.denominator*z-P.numerator)
   assert e==(9 if h[0]==3 else 17), (h,e)
   assert p==10*k+9,(h,p)
   trials[k]=k,e,p
 print('small reference',F,'pure-five reference',P,'pure-five spatial tail/period',ref('','01000')[1:3])
 print('k, d(small), d(pure-five) by number k of first long tiles',list(trials.values()))
if __name__=='__main__':go()
