/* Reproducible diagnostic; no numerical spectral theorem is inferred from it.
   Run with Node >=18. Exact integer arithmetic is used for graph identities;
   the mod-p rank, together with eight exact independent kernel vectors,
   certifies the rational nullity of the specific 224-vertex example. */
const fs = require('fs');
const path = require('path');
const k=8, q=7, h=2*q, r=3, d=q+2*r, N=2*h*k;
const id=(i,s,a)=>(i*2+s)*h+a;
const nbr=Array.from({length:N},()=>new Set());
const add=(u,v)=>{if(u===v||nbr[u].has(v))throw Error('non-simple construction');nbr[u].add(v);nbr[v].add(u)};
for(let i=0;i<k;i++)for(let s=0;s<2;s++)for(let a=0;a<q;a++)for(let b=q;b<h;b++)add(id(i,s,a),id(i,s,b));
for(let i=0;i<k;i++)for(let bit=0;bit<3;bit++){
 const j=i^(1<<bit); if(i>j)continue;
 for(let a=0;a<h;a++)for(let s=0;s<2;s++)for(let t=0;t<2;t++)add(id(i,s,a),id(j,t,a));
}
const assert=(ok,msg)=>{if(!ok)throw Error(msg)};
assert(nbr.every(a=>a.size===d),'regularity');
const colors=Array(N).fill(-1);colors[0]=0;const queue=[0];
for(let j=0;j<queue.length;j++)for(const v of nbr[queue[j]]){
 if(colors[v]<0){colors[v]=colors[queue[j]]^1;queue.push(v)}
 else assert(colors[v]!==colors[queue[j]],'bipartiteness');
}
assert(queue.length===N,'connectivity');
const parity=i=>{let n=0;while(i){n^=i&1;i>>>=1}return n};
const cols=Array.from({length:k},(_,j)=>Array.from({length:N},(_,v)=>{
 const i=Math.floor(v/(2*h)),s=Math.floor(v/h)%2;
 return ((parity(i&j)^s)?-1:1);
}));
const dot=(a,b)=>a.reduce((z,x,i)=>z+x*b[i],0);
const applyA=f=>nbr.map(a=>[...a].reduce((z,v)=>z+f[v],0));
for(let j=0;j<k;j++){
 const af=applyA(cols[j]);assert(af.every((x,v)=>x===q*cols[j][v]),'Hadamard eigenvector');
 for(let l=0;l<k;l++)assert(dot(cols[j],cols[l])===(j===l?N:0),'Hadamard orthogonality');
}
const p=1000003;
const mod=x=>(x%p+p)%p;
const mul=(a,b)=>(a*b)%p;
const pow=(a,n)=>{let b=1;while(n){if(n%2)b=mul(b,a);a=mul(a,a);n=Math.floor(n/2)}return b};
const mat=Array.from({length:N},(_,u)=>Array.from({length:N},(_,v)=>u===v?p-q:nbr[u].has(v)?1:0));
let rank=0;
for(let col=0;col<N&&rank<N;col++){
 let pivot=rank;while(pivot<N&&mat[pivot][col]===0)pivot++;
 if(pivot===N)continue;
 [mat[rank],mat[pivot]]=[mat[pivot],mat[rank]];
 const inv=pow(mat[rank][col],p-2);
 for(let j=col;j<N;j++)mat[rank][j]=mul(mat[rank][j],inv);
 for(let i=rank+1;i<N;i++)if(mat[i][col]){
  const a=mat[i][col];for(let j=col;j<N;j++)mat[i][j]=mod(mat[i][j]-mul(a,mat[rank][j]));
 }
 rank++;
}
assert(rank===N-k,'modular rank');
let equitableChecks=0;
let overlapSum=0;
for(let mask=0;mask<(1<<k);mask++){
 const f=Array.from({length:N},(_,v)=>{
  const i=Math.floor(v/(2*h)),s=Math.floor(v/h)%2;
  return (((mask>>i)&1)^s)?-1:1;
 });
 assert(f.reduce((a,b)=>a+b,0)===0,'balanced labels');
 for(let v=0;v<N;v++)assert([...nbr[v]].filter(u=>f[u]!==f[v]).length===r,'equitable cross degree');
 overlapSum+=Math.abs(dot(cols[0],f))/N;equitableChecks++;
}
const arcs=[];for(let u=0;u<N;u++)for(const v of nbr[u])arcs.push([u,v]);
const zcols=cols.map(f=>arcs.map(([u,v])=>4*f[v]-f[u]));
for(let j=0;j<k;j++){
 const f=cols[j], z=zcols[j];
 for(let a=0;a<arcs.length;a++){
  const [u,v]=arcs[a];let bz=0;
  for(const w of nbr[v])if(w!==u)bz+=4*f[w]-f[v];
  assert(bz===4*z[a],'nonbacktracking eigenvector');
 }
 for(let l=0;l<k;l++)assert(dot(z,zcols[l])===(j===l?165*N:0),'nonbacktracking orthogonality');
}
const z=zcols[0], z2=dot(z,z),z4=z.reduce((a,b)=>a+b**4,0);
assert(z4===2685*N,'nonbacktracking fourth moment');
const thetaR=[3,1,1,1,-1,-1,-1,-3], lambdaF=[q,-q,...Array(h-2).fill(0)];
const spectrum=[];
for(const f of lambdaF)for(let j=0;j<k;j++)spectrum.push(f);
for(const f of lambdaF)for(const t of thetaR)spectrum.push(f+2*t);
spectrum.sort((a,b)=>b-a);
assert(spectrum.length===N&&spectrum[0]===d&&spectrum[1]===9,'tensor spectrum');
assert(spectrum.filter(x=>x===q).length===k,'full outlier multiplicity');
assert(spectrum.reduce((a,b)=>a+b*b,0)===N*d,'spectral trace two');
const report={
 status:'PASS: diagnostics corroborate the written proof; no novelty or asymptotic theorem inferred',
 graph:{N,d,r,q,h,k,connected:queue.length===N,bipartite:true,simple:true},
 exactChecks:{integerHadamardColumns:k,integerEquitableBisections:equitableChecks,
  modularPrime:p,rankAMinus7I:rank,rationalNullityCertifiedByExactKernelAndModularRank:k,
  nonbacktrackingColumns:k,nonbacktrackingEigenvalue:4,nonbacktrackingNormSquaredForIntegerColumns:z2,
  nonbacktrackingFourthMomentForIntegerColumns:z4},
 spectral:{universalCoverEdge:2*Math.sqrt(d-1),outlier:q,laplacianGap:4,
  betheHessianOutlier:2*(d-1)-q*Math.sqrt(d-1),negativeBetheHessianCount:spectrum.filter(x=>2*(d-1)-Math.sqrt(d-1)*x<0).length},
 incoherence:{fullOutlierRank:k,projectorDiagonal:k/N,projectorIncoherence:1,
  flatVertexIPR:1/N,flatVertexInfinityNorm:1/Math.sqrt(N),
  normalizedNonbacktrackingIPR:z4/(z2*z2),nonbacktrackingIPRFormula:179/(1815*N),
  normalizedNonbacktrackingInfinityNorm:5/Math.sqrt(165*N)},
 oracleBayesOverlap:{enumerated:overlapSum/(1<<k),centralBinomialFormula:70/256,cauchySchwarzUpperBound:1/Math.sqrt(k)},
 fullSpectrum:spectrum.reduce((a,x)=>(a[x]=(a[x]||0)+1,a),{})
};
// All following algebraic identities hold for every lift. Reproducible
// pseudorandom matchings exercise them; they do not numerically verify the
// asymptotic probabilistic norm input or claim the full finite-lift kernel.
report.arbitraryLiftDiagnostics=[];
for(const n of [3,7]){
 let seed=194+17*n;
 const draw=()=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0};
 const lnbr=Array.from({length:N*n},()=>new Set());
 for(let u=0;u<N;u++)for(const v of nbr[u])if(u<v){
  const perm=Array.from({length:n},(_,i)=>i);
  for(let i=n-1;i>0;i--){const j=draw()%(i+1);[perm[i],perm[j]]=[perm[j],perm[i]]}
  for(let i=0;i<n;i++){const a=u*n+i,b=v*n+perm[i];lnbr[a].add(b);lnbr[b].add(a)}
 }
 assert(lnbr.every(a=>a.size===d),'lift regularity');
 const reached=new Set([0]), todo=[0];
 for(let j=0;j<todo.length;j++)for(const v of lnbr[todo[j]]){
  assert(colors[Math.floor(v/n)]!==colors[Math.floor(todo[j]/n)],'lift bipartiteness');
  if(!reached.has(v)){reached.add(v);todo.push(v)}
 }
 let residualMax=0, crossCheck=0;
 for(let j=0;j<k;j++){
  const f=cols[j];
  for(let u=0;u<N*n;u++){
   const fv=f[Math.floor(u/n)];let af=0,cross=0;
   for(const v of lnbr[u]){const fvv=f[Math.floor(v/n)];af+=fvv;if(fvv!==fv)cross++}
   residualMax=Math.max(residualMax,Math.abs(af-q*fv));
   assert(cross===r,'lift equitable labels');crossCheck++;
  }
 }
 assert(residualMax===0,'old lift eigenvector identity');
 report.arbitraryLiftDiagnostics.push({liftDegree:n,totalSize:N*n,connected:reached.size===N*n,
  bipartite:true,regularDegree:d,oldEigenvectorColumns:k,maximumIntegerEigenResidual:residualMax,
  vertexCrossDegreeIdentities:crossCheck,oldSubspaceProjectorIncoherence:1,
  oldSubspaceProjectorDiagonal:k/(N*n),flatOldBasisIPR:1/(N*n),
  scope:'algebraic checks for arbitrary reproducible lifts; no claim about full finite-lift eigenspace or new norm'});
}
fs.writeFileSync(path.join(__dirname,'flat-outlier-checks.json'),JSON.stringify(report,null,2)+'\n');
process.stdout.write(JSON.stringify(report,null,2)+'\n');
