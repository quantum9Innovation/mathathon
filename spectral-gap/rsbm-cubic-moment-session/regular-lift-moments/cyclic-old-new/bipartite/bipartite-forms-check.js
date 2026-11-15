'use strict';
const mod=(x,p)=>((x%p)+p)%p;
function rank(vectors,n,p){
 const a=vectors.map(x=>x.map(v=>mod(v,p)));let row=0;
 for(let c=0;c<n&&row<a.length;c++){
  let z=row;while(z<a.length&&!a[z][c])z++;if(z===a.length)continue;
  [a[z],a[row]]=[a[row],a[z]];let inv=1;while(mod(inv*a[row][c],p)!==1)inv++;
  for(let j=c;j<n;j++)a[row][j]=mod(a[row][j]*inv,p);
  for(let i=0;i<a.length;i++)if(i!==row&&a[i][c]){const t=a[i][c];for(let j=c;j<n;j++)a[i][j]=mod(a[i][j]-t*a[row][j],p);}
  row++;
 }return row;
}
function formDim(p,R){
 const r=R.length,eq=2*r*(r+1)/2,cols=[];
 for(let a=0;a<r;a++)for(let b=0;b<r;b++){
  const c=[];
  for(let t=0;t<2;t++)for(let i=0;i<r;i++)for(let j=i;j<r;j++){
   const f=(x,y)=>t===0?(y===b?R[x][a]:0):(y===a?R[x][b]:0);
   c.push(i===j?f(i,j):f(i,j)+f(j,i));
  }cols.push(c);
 }
 return r*r-rank(cols,eq,p);
}
function companion(coeff,p){const r=coeff.length,R=Array.from({length:r},()=>Array(r).fill(0));for(let i=1;i<r;i++)R[i][i-1]=1;for(let i=0;i<r;i++)R[i][r-1]=mod(-coeff[i],p);return R;}
function oldHom(p,B,R){const k=B.length,r=R.length,cols=[];for(let i=0;i<k;i++)for(let a=0;a<r;a++){const c=Array(k*r).fill(0);for(let j=0;j<k;j++)c[j*r+a]+=B[j][i];for(let b=0;b<r;b++)c[i*r+b]-=R[a][b];cols.push(c);}return k*r-rank(cols,k*r,p);}
function congruenceCheck(p,B,R,name){
 const k=B.length,r=R.length,q=p**r,labels=[];
 for(let a=0;a<q;a++){let t=a,v=[];for(let j=0;j<r;j++){v.push(t%p);t=Math.floor(t/p);}labels.push(v);}
 const idx=(i,a,l)=>(i*q+a)*r+l,cols=[],fresh=()=>Array(k*q*r).fill(0);
 for(let i=0;i<k;i++)for(let a=1;a<q;a++){
  const c=fresh(),v=labels[a],w=R[0].map((_,j)=>v.reduce((s,x,l)=>s+x*R[l][j],0));
  for(let l=0;l<r;l++)c[idx(i,a,l)]-=w[l];
  for(let j=0;j<k;j++)if(B[i][j])for(let l=0;l<r;l++)c[idx(j,0,l)]+=v[l];cols.push(c);
 }
 for(let i=0;i<k;i++)for(let j=i+1;j<k;j++)if(B[i][j])for(let a=1;a<q;a++)for(let b=1;b<q;b++){
  const c=fresh();for(let l=0;l<r;l++){c[idx(i,a,l)]+=labels[b][l];c[idx(i,0,l)]-=labels[b][l];c[idx(j,b,l)]+=labels[a][l];c[idx(j,0,l)]-=labels[a][l];}cols.push(c);
 }
 const rho=rank(cols,k*q*r,p),h=oldHom(p,B,R),extra=formDim(p,R),expected=k*q*r-h-extra;
 if(rho!==expected)throw new Error(`${name}: ${rho} != ${expected}`);
 return {name,p,r,q,congruenceRank:rho,oldHomDimension:h,extraDimension:extra,pass:true};
}
const B=Array.from({length:6},(_,i)=>Array.from({length:6},(_,j)=>(i<3)!==(j<3)?1:0));
const formTests=[
 {name:'zero-scalar',p:3,R:[[0]],expected:1},
 {name:'nonzero-scalar',p:3,R:[[1]],expected:0},
 {name:'irreducible-even-degree2',p:3,R:companion([1,0],3),expected:1},
 {name:'irreducible-not-even-degree2',p:3,R:companion([2,1],3),expected:0},
 {name:'irreducible-even-degree4',p:3,R:companion([2,0,1,0],3),expected:2},
 {name:'cyclic-jordan',p:3,R:[[1,1],[0,1]],expected:0},
 {name:'reducible-even-distinct',p:3,R:[[1,0],[0,2]],expected:1},
 {name:'zero-double-control',p:3,R:[[0,0],[0,0]],expected:4}
].map(t=>{const got=formDim(t.p,t.R);if(got!==t.expected)throw new Error(`${t.name}: ${got} != ${t.expected}`);return {name:t.name,p:t.p,r:t.R.length,extraDimension:got,pass:true};});
const latticeTests=[
 congruenceCheck(3,B,[[0]],'K33-zero-scalar'),
 congruenceCheck(3,B,[[1]],'K33-nonzero-scalar'),
 congruenceCheck(3,B,companion([1,0],3),'K33-irreducible-even'),
 congruenceCheck(3,B,companion([2,1],3),'K33-irreducible-not-even')
];
process.stdout.write(JSON.stringify({formTests,latticeTests},null,2)+'\n');
