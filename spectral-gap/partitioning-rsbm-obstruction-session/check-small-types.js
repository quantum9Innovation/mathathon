function rnd(n){return Math.floor(Math.random()*n)}
function shuffle(a){for(let k=a.length-1;k>0;k--){let j=rnd(k+1);[a[k],a[j]]=[a[j],a[k]];} return a}
function cycleGraph(N){
  for(;;){
    const s=shuffle(Array.from({length:2*N},(_,k)=>k>>1)), adj=Array.from({length:N},()=>[]);
    let ok=true;
    for(let k=0;k<2*N;k+=2){let a=s[k],b=s[k+1];if(a===b||adj[a].includes(b)){ok=false;break;}adj[a].push(b);adj[b].push(a);}
    if(ok)return adj;
  }
}
function inverse(a,p){let b=p,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v];}return ((u%p)+p)%p}
function rank(M,p){
 const n=M.length,m=M[0].length,A=M.map(r=>r.map(x=>(x%p+p)%p));let r=0;
 for(let c=0;c<m && r<n;c++){let z=r;while(z<n && !A[z][c])z++;if(z===n)continue;
 [A[r],A[z]]=[A[z],A[r]];let inv=inverse(A[r][c],p);
 for(let j=c;j<m;j++)A[r][j]=A[r][j]*inv%p;
 for(let i=r+1;i<n;i++){let t=A[i][c];if(t){for(let j=c;j<m;j++)A[i][j]=(A[i][j]-t*A[r][j]%p+p)%p;}}r++;
 } return r;
}
function experiment(N,reps){
 const counts={}, examples=[];
 for(let t=0;t<reps;t++){let C=cycleGraph(N),D=cycleGraph(N),M=Array.from({length:N},()=>Array(N).fill(0));
  for(let i=0;i<N;i++){for(let j of C[i])M[i][j]++;for(let j of D[i]){M[i][j]++;for(let k of C[j])M[i][k]--;}}
  let r1=rank(M,1000003),r2=r1<N-1?rank(M,1000033):r1,r=Math.max(r1,r2);
  counts[N-r]=(counts[N-r]||0)+1;if(r<N-1&&examples.length<3)examples.push({C,D,defect:N-r});
 }
 return {N,reps,counts,examples};
}


function allPairings(stubs){
 if(!stubs.length)return [[]];const a=stubs[0],out=[];
 for(let i=1;i<stubs.length;i++){const b=stubs[i],rest=stubs.filter((_,j)=>j!==0&&j!==i);for(let sub of allPairings(rest))out.push([[a,b],...sub]);}return out;
}
function matrices(N){return allPairings(Array.from({length:2*N},(_,i)=>i)).map(edges=>{let M=Array.from({length:N},()=>Array(N).fill(0));for(let [a,b]of edges){a>>=1;b>>=1;M[a][b]++;M[b][a]++;}return M;});}
function pairWeight(m,p){let v=1;for(let a=0;a<p;a++)for(let b=a;b<p;b++){let k=m[a*p+b];if(a===b){if(k%2)return 0;for(let j=1;j<k;j+=2)v*=j;}else{if(k!==m[b*p+a])return 0;for(let j=2;j<=k;j++)v*=j;}}return v;}
function directMoment(N,p){let mats=matrices(N),sum=0;for(let C of mats)for(let D of mats){let M=Array.from({length:N},(_,i)=>Array.from({length:N},(_,j)=>C[i][j]+D[i][j]-D[i].reduce((s,a,k)=>s+a*C[k][j],0)));sum+=p**(N-rank(M,p));}return {numerator:sum,denominator:mats.length**2};}
function typeMoment(N,p){let profiles=[];for(let a=0;a<p;a++)for(let d=0;d<p;d++)for(let b=0;b<p;b++)for(let e=0;e<p;e++)profiles.push([a,d,b,(a+d-b+p)%p,e,(a+d-e+p)%p]);let plus=Array(p*p).fill(0),minus=Array(p*p).fill(0),sum=0;
 function rec(k){if(k===N){sum+=pairWeight(plus,p)*pairWeight(minus,p);return;}
 for(let[a,d,b,c,e,f]of profiles){plus[a*p+b]++;plus[a*p+c]++;minus[d*p+e]++;minus[d*p+f]++;rec(k+1);plus[a*p+b]--;plus[a*p+c]--;minus[d*p+e]--;minus[d*p+f]--;}}
 rec(0);return{numerator:sum,denominator:matrices(N).length**2};}

const result=[];for(let p of[2,3])for(let N of[1,2,3])result.push({N,p,direct:directMoment(N,p),type:typeMoment(N,p)});console.log(JSON.stringify(result,null,2));
