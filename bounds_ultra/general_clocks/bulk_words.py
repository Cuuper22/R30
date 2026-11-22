"""All unrestricted 2xk spacetime words, by the exact 2k-bit initial cone."""
import numpy as np
for k in (6,8):
 v=np.arange(1<<(2*k),dtype=np.uint32);u=v*0
 for t in range(k):
  p=k-1-t;u|=((v>>p)&1)<<(k+t);u|=((v>>(p+1))&1)<<t;v=v^(v>>1|v>>2)
 print(k,len(np.unique(u)))
