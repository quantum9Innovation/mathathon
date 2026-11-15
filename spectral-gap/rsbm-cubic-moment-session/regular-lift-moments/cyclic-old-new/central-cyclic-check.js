'use strict';
// Independent finite-field rank checks using an explicit saturated integer
// parameterization of the compatible-table direction lattice.
const B=[[0,1,1,1],[1,0,1,1],[1,1,0,1],[1,1,1,0]];
function mod(x,p){return ((x%p)+p)%p;}
function rank(vectors,n,p){
 const a=vectors.map(x=>x.map(v=>mod(v,p)));let row=0;
 for(let c=0;c<n&&row<a.length;c++){
  let z=row;while(z<a.length&&a[z][c]===0)z++;if(z===a.length)continue;
  [a[z],a[row]]=[a[row],a[z]];let inv=1;while(mod(inv*a[row][c],p)!==1)inv++;
  for(let j=c;j<n;j++)a[row][j]=mod(a[row][j]*inv,p);
  for(let i=0;i<a.length;i++)if(i!==row&&a[i][c]){const t=a[i][c];for(let j=c;j<n;j++)a[i][j]=mod(a[i][j]-t*a[row][j],p);}
  row++;
 }return row;
}
function check(p,R,name){
 const k=B.length,r=R.length,q=p**r,labels=[];
 for(let a=0;a<q;a++){let t=a,v=[];for(let j=0;j<r;j++){v.push(t%p);t=Math.floor(t/p);}labels.push(v);}
 const mul=a=>R[0].map((_,j)=>a.reduce((s,x,l)=>s+x*R[l][j],0));
 const idx=(i,a,l)=>(i*q+a)*r+l,cols=[];
 const fresh=()=>Array(k*q*r).fill(0);
 for(let i=0;i<k;i++)for(let a=1;a<q;a++){
  const c=fresh(),v=labels[a],w=mul(v);
  for(let l=0;l<r;l++)c[idx(i,a,l)]-=w[l];
  for(let j=0;j<k;j++)if(B[i][j])for(let l=0;l<r;l++)c[idx(j,0,l)]+=v[l];
  cols.push(c);
 }
 for(let i=0;i<k;i++)for(let j=i+1;j<k;j++)if(B[i][j])for(let a=1;a<q;a++)for(let b=1;b<q;b++){
  const c=fresh();for(let l=0;l<r;l++){
   c[idx(i,a,l)]+=labels[b][l];c[idx(i,0,l)]-=labels[b][l];
   c[idx(j,b,l)]+=labels[a][l];c[idx(j,0,l)]-=labels[a][l];
  }cols.push(c);
 }
 const oldCols=[];
 for(let i=0;i<k;i++)for(let a=0;a<r;a++){
  const c=Array(k*r).fill(0);
  for(let j=0;j<k;j++)c[j*r+a]+=B[j][i];
  for(let b=0;b<r;b++)c[i*r+b]-=R[a][b];oldCols.push(c);
 }
 const altCols=[];
 for(let a=0;a<r;a++)for(let b=a+1;b<r;b++){
  const K=Array.from({length:r},()=>Array(r).fill(0));K[a][b]=1;K[b][a]=-1;
  const c=[];for(let i=0;i<r;i++)for(let j=0;j<r;j++){
   let v=0;for(let z=0;z<r;z++)v+=R[i][z]*K[z][j]-K[i][z]*R[j][z];c.push(v);
  }altCols.push(c);
 }
 const rho=rank(cols,k*q*r,p),hOld=k*r-rank(oldCols,k*r,p),aR=r*(r-1)/2-rank(altCols,r*r,p);
 const expected=k*q*r-hOld-aR;
 if(rho!==expected)throw new Error(`rank mismatch ${name}: ${rho} != ${expected}`);
 return {name,p,r,q,compatibleDimension:cols.length,congruenceRank:rho,oldHomDimension:hOld,alternatingDimension:aR,dependencyDimension:k*q*r-rho,pass:true};
}
const tests=[
 check(3,[[2]],'scalar-minus-one'),
 check(3,[[0]],'scalar-degree-three'),
 check(5,[[4]],'scalar-minus-one-p5'),
 check(3,[[0,2],[1,0]],'irreducible-x2-plus-one'),
 check(3,[[0,0],[0,2]],'cyclic-distinct-eigenvalues'),
 check(3,[[2,1],[0,2]],'cyclic-jordan'),
 check(3,[[2,0],[0,2]],'noncyclic-scalar-double'),
 check(5,[[0,3],[1,0]],'irreducible-x2-minus-three-p5')
];
process.stdout.write(JSON.stringify({base:'K4',tests},null,2)+'\n');
