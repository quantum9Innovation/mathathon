// RSBM(2,1): uniform configurations conditioned simple, cross matching relabeled I.
// Integer modular ranks certify real corank 1 whenever one modulus gives corank 1.
// Larger modular corank is only a candidate for real multiplicity.
// Xorshift pseudorandom sampling, fixed seed; no statistical claim follows.
let seed=987654321;
function rnd(n){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n}
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
const results=[experiment(30,1000),experiment(60,500),experiment(100,300)];
console.log(JSON.stringify(results,null,2));
