#define main oldcm
#include "barrier_cone.cpp"
#undef main
#include <map>
#include <tuple>
#include <cstdint>
static int member(B&b,std::vector<unsigned long long> xs,const V&W){
 auto s=xs;std::map<std::tuple<int,int,int>,int> memo;
 // Sorted distinct integers; Shannon split by descending bit, merge equal subfunctions.
 auto go=[&](auto &&f,int l,int r,int j)->int{
  if(r==l)return NO;if(j<0)return YES;
  int m=l;while(m<r&&!(s[m]>>j&1))m++;
  int x=f(f,l,m,j-1),y=f(f,m,r,j-1);if(x==y)return x;
  auto k=std::make_tuple(j,x,y);auto i=memo.find(k);if(i!=memo.end())return i->second;
  int z=b.nv(),h=W[j];b.add({h,-x,z});b.add({h,x,-z});b.add({-h,-y,z});b.add({-h,y,-z});return memo[k]=z;};
 return go(go,0,s.size(),W.size()-1);
}

// Entire finite-target ambiguity: east scanned finite predecessor starts 00;
// second predecessor starts 11. Arbitrary finite target tail can generate
// exactly the reachable ordered pairs at the far end of this finite cone.
int main(int ac,char**v){
 int d=atoi(v[1]),h=atoi(v[2]),ph=atoi(v[3]),H=d+2*h;
 std::vector<unsigned long long> hosts;for(unsigned long long i;scanf("%llu",&i)==1;)hosts.push_back(i);B b;V w(H+3,NO),src;
 for(int j=0;j<H;j++)w[j]=b.nv();src=w;src.resize(H);
 int a=b.nv(),c=b.nv(),A=b.nv(),C=b.nv();V pair={a,c,A,C};int seen[16]={0};std::vector<int> g={12};seen[12]=1;
 for(size_t j=0;j<g.size();j++)for(int u=0;u<2;u++){int st=g[j],x=st&3,y=st>>2;
 auto f=[&](int k){return (2*(k&1))+(u^bool(k));};int z=f(x)+4*f(y);if(!seen[z]){seen[z]=1;g.push_back(z);}}
 for(int i=0;i<16;i++)if(!seen[i]){V l;for(int j=0;j<4;j++)l.push_back((i>>j&1)?-pair[j]:pair[j]);b.add(l);}
 for(int j=H-1;j>=0;j--){int x=b.X(w[j],b.OR(a,c));c=a;a=x;int y=b.X(w[j],b.OR(A,C));C=A;A=y;}
 b.eq(a,ph?YES:NO);b.eq(A,ph?NO:YES);
 for(int t=0;t<=2*h;t++){if(!(t%2)){V p(w.begin(),w.begin()+d);b.eq(member(b,hosts,p),YES);}
 if(t==2*h)break;V z(H+3,NO);for(int j=0;j<H-t-1;j++)z[j]=b.F(j?w[j-1]:((t&1)?YES:NO),w[j],w[j+1]);w.swap(z);}
 for(int x:src)fprintf(stderr,"%d ",x);b.dump();}
