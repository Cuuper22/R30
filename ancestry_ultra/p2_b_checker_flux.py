"""Can the exact odd-gap q injection carry enough checkerboard defects to
fill the linearly wide temporal vacuum of a finite initial west? Test an
isolated physical q pulse: bounded mass inspires a current; a growing
front demands a flux bound in the advancing blank wedge instead."""
def go(N=4096):
 O=N+10
 a=1<<O;b=(1<<O)|(1<<(O-1));old=a
 for j in range(1,N):
  c=(b>>1)^(a&~b);d=(c>>1)^(c&~b)
  if j in (1,2,3,4,5,8,16,32,64,128,256,1024,2048,4095):
   print('depth',2*j+2,'odd/even single-pulse temporal mass',c.bit_count(),d.bit_count(),'support',d.bit_length()-(d&-d).bit_length()+1,flush=True)
  a,b=c,d
if __name__=='__main__':go()
