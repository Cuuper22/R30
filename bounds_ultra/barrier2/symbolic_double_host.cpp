#define main oldcm
#include "barrier_cone.cpp"
#undef main
#include <map>
#include <tuple>
#include <cstdint>
static int member(B&b,V xs,const V&W){
 V s=xs;std::map<std::tuple<int,int,int>,int> memo;
 // Sorted distinct integers; Shannon split by descending bit, merge equal subfunctions.
 auto go=[&](auto &&f,int l,int r,int j)->int{
  if(r==l)return NO;if(j<0)return YES;
  int m=l;while(m<r&&!(s[m]>>j&1))m++;
  int x=f(f,l,m,j-1),y=f(f,m,r,j-1);if(x==y)return x;
  auto k=std::make_tuple(j,x,y);auto i=memo.find(k);if(i!=memo.end())return i->second;
  int z=b.nv(),h=W[j];b.add({h,-x,z});b.add({h,x,-z});b.add({-h,-y,z});b.add({-h,y,-z});return memo[k]=z;};
 return go(go,0,s.size(),W.size()-1);
}
int main(int ac,char**v){
 int r=atoi(v[1]),st=atoi(v[2]),u=atoi(v[3]),q=atoi(v[4]),en=u+q,side=atoi(v[5]),d=atoi(v[6]),sub=atoi(v[7]),PH=1^((u-st)&1),H=en+std::max(d,5),C=H+5;
 V valid;for(int a;scanf("%d",&a)==1;)valid.push_back(a);B b;V w(2*H+12,NO),a=w;w[C]=YES;V src;for(int j=1;j<=H;j++){int e=b.nv();src.push_back(e);w[C+j]=e;
 if(getenv("PAIR_TAGK")&&j<=atoi(getenv("PAIR_TAGK")))b.eq(e,(strtoul(getenv("PAIR_TAG"),0,0)>>(j-1)&1)?YES:NO);}
 for(int t=0;t<=en;t++){
  if(t>=st){int c=PH^((t-st)&1);b.eq(w[C],c?YES:NO);w[C]=c?YES:NO;}
  for(int k=0;k<2;k++)if(side>>k&1){
   int s=u+k*q;
   if(t==s-1){b.eq(w[C],NO);w[C]=NO;
    V p(w.begin()+C+1,w.begin()+C+1+d);
    if(d)b.eq(member(b,valid,p),YES);
    if(sub>=0)for(int j=1;j<=5;j++){int bit=sub>>(j-1)&1;b.eq(w[C+j],bit?YES:NO);w[C+j]=bit?YES:NO;}
   }
   if(t==s){for(int j=1;j<=4;j++){int bit=11>>(j-1)&1;b.eq(w[C+j],bit?YES:NO);w[C+j]=bit?YES:NO;}b.eq(w[C-3],YES);b.eq(w[C-2],NO);w[C-3]=YES;w[C-2]=NO;}
  }
  if(t==en)break;fill(a.begin(),a.end(),NO);for(int j=max(-t-1,-(H-t-1));j<=H-t-1;j++)a[C+j]=r==30?b.F(w[C+j-1],w[C+j],w[C+j+1]):b.X(w[C+j-1],w[C+j+1]);w.swap(a);
 }
 for(int x:src)fprintf(stderr,"%d ",x);b.dump();}
