// Exact first-64 center prefixes for all [-d,d] words, with certified
// infinite left vacuum and the common absolute stationary right checker.
#include<cstdint>
#include<cstdio>
#include<vector>
#include<algorithm>
#include<cstdlib>
using U=unsigned __int128;using T=uint64_t;
int main(int argc,char**argv){int d=argc>1?atoi(argv[1]):10;unsigned N=1u<<(2*d+1),lim=argc>2?atoi(argv[2]):30;
 U ck=0;for(int x=d+1;x<=63;++x)if(!(x&1))ck|=U(1)<<(63+x);
 std::vector<std::pair<T,unsigned>> a(N);
 #pragma omp parallel for
 for(unsigned i=0;i<N;++i){U z=ck|(U(i)<<(63-d));T t=0;for(unsigned k=0;k<64;++k){t|=T((z>>63)&1)<<k;z=(z<<1)^((lim==30?z:0)|(z>>1));}a[i]={t,i};}
 std::sort(a.begin(),a.end());int groups=0,num=0;
 for(unsigned i=0,j;i<N;i=j){for(j=i+1;j<N && a[j].first==a[i].first;++j);
   unsigned all=a[i].second&-a[i].second;bool diff=0;
   for(unsigned k=i;k<j;++k)diff|=(a[k].second&-a[k].second)!=all;
   if(!diff)continue;++groups;
   for(unsigned k=i;k<j;++k){printf("%016llx %x\n",(unsigned long long)a[i].first,a[k].second);++num;}
 }fprintf(stderr,"d%d rule%d: %d eligible mixed-mark groups; %d states incl temporarily empty west\n",d,lim,groups,num);
}
