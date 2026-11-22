// Test if periodic closure of ANY accepted q word can conflict with the true
// outer marked zero sleeve via a uniform bound on time-periodic spatial gaps.
// Iterate the exact sideways two-column map; include transient western tails
// (arbitrary right boundary) as well as its cyclic bulk. Compare true R90.
#include<cstdio>
#include<cstdlib>
#include<vector>
#include<algorithm>
#include<cstdint>
int main(int argc,char**argv){int L=atoi(argv[1]),r=atoi(argv[2]),d=1<<L,m=d-1,N=d*d;std::vector<int>f(N),g(N,-1),v(N),c(N),path;for(int a=0;a<d;a++)for(int b=0;b<d;b++)f[a*d+b]=b*d+(((b>>1)|(b&1)<<(L-1))^(r==30?(a|b):a)); // each successor west cell
 int glob=0,cy=0,gmark=0,cmark=0;
 for(int i=1;i<N;i++){if(v[i])continue;path.clear();int p=i;while(v[p]==0){v[p]=1;path.push_back(p);p=f[p];}if(v[p]==1){int q=p;do{c[q]=1;q=f[q];}while(q!=p);}for(int q:path)v[q]=2;}
 // Maximum zero run *immediately outside a black*: whole past at all columns
 // is L-cyclic. No requirement that either entering column is a true east host.
 for(int i=0;i<N;i++)if((i&1)&&!(f[i]&1)){int z=f[i],x=0;while(!(z&1)&&x<=2*L+1){x++;z=f[z];}if(x>glob){glob=x;gmark=i;}if(c[i]&&x>cy){cy=x;cmark=i;}}
 std::printf("L %d rule %d max western zero run after black all %d cyclic %d examples %d %d\n",L,r,glob,cy,gmark,cmark);
}
