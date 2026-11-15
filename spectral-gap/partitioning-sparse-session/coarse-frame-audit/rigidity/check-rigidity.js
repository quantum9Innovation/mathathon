/* Finite diagnostics for the audited entropy and variance identities.
   Run with Node>=18. Enumerates all set partitions of two small typed
   graphs, retains equitable candidate partitions, and checks their real
   one-hot star laws. This is corroboration, not a substitute for the proof. */
const fs=require('fs'),path=require('path');
const assert=(ok,msg)=>{if(!ok)throw Error(msg)};
const close=(a,b,msg)=>assert(Math.abs(a-b)<1e-10,msg+': '+a+' vs '+b);
const acc=(m,key,w)=>m.set(key,(m.get(key)||0)+w);
const ent=m=>[...m.values()].reduce((z,p)=>z-(p>0?p*Math.log(p):0),0);
const permutations=a=>a.length?a.flatMap((x,i)=>permutations(a.filter((_,j)=>j!==i)).map(b=>[x,...b])):[[]];
const sqnorm=a=>a.reduce((z,x)=>z+x*x,0);
const makeGraph=(sizes,internalEdges,crossEdges)=>{
 const N=sizes[0]+sizes[1],nbr=Array.from({length:N},()=>[]);
 for(const [u,v] of [...internalEdges,...crossEdges]){nbr[u].push(v);nbr[v].push(u)}
 const type=Array.from({length:N},(_,v)=>v<sizes[0]?0:1);
 const a=[nbr[0].filter(v=>type[v]===0).length,nbr[sizes[0]].filter(v=>type[v]===1).length];
 const b=[nbr[0].filter(v=>type[v]===1).length,nbr[sizes[0]].filter(v=>type[v]===0).length];
 return {N,nbr,sizes,type,a,b};
};
const prism=makeGraph([3,3],[[0,1],[1,2],[2,0],[3,4],[4,5],[5,3]],[[0,3],[1,4],[2,5]]);
const unequal=makeGraph([3,6],[[0,1],[1,2],[2,0],...[3,4,5].flatMap(u=>[6,7,8].map(v=>[u,v]))],
 [[0,3],[0,4],[1,5],[1,6],[2,7],[2,8]]);
const output={status:'PASS: finite diagnostics corroborate the full written proof',examples:[]};
for(const [name,g] of [['equal-cubic-prism',prism],['unequal-proportions-ai2-ai3',unequal]]){
 const {N,nbr,sizes,type,a,b}=g,alpha=sizes.map(n=>n/N),Delta=Math.max(...nbr.map(n=>n.length));
 close(alpha[0]*b[0],alpha[1]*b[1],'weighted cross balance');
 let setPartitions=0,equitable=0,positiveDefect=0,zeroDefect=0,maxCancellationError=0,maxVarianceError=0;
 let minGapSlack=Infinity,largestAlphabet=0,minPositiveL=Infinity;
 const y=Array(N).fill(0);
 function visit(v,maxLabel){
  if(v<N){for(let x=0;x<=maxLabel+1;x++){y[v]=x;visit(v+1,Math.max(maxLabel,x))}return}
  setPartitions++;const r=maxLabel+1,R=Array(r).fill(null);
  for(let u=0;u<N;u++){
   const counts=Array(r).fill(0);for(const w of nbr[u])counts[y[w]]++;
   if(R[y[u]]&&R[y[u]].some((x,j)=>x!==counts[j]))return;
   R[y[u]]=counts;
  }
  equitable++;largestAlphabet=Math.max(largestAlphabet,r);
  const pi=[];
  for(let i=0;i<2;i++){
   const star=new Map(),raw=new Map();
   for(let u=0;u<N;u++)if(type[u]===i){
    const ins=nbr[u].filter(w=>type[w]===i).map(w=>y[w]);
    const cross=nbr[u].filter(w=>type[w]!==i).map(w=>y[w]);
    acc(raw,JSON.stringify([y[u],...ins,...cross]),1/sizes[i]);
    const ip=permutations(ins),cp=permutations(cross);
    for(const aa of ip)for(const bb of cp)acc(star,JSON.stringify([y[u],...aa,...bb]),1/(sizes[i]*ip.length*cp.length));
   }
   const root=new Map(),intpair=new Map(),crosspair=new Map(),trunc=new Map();
   for(const [key,p] of star){const z=JSON.parse(key),x=z[0];acc(root,x,p);acc(intpair,JSON.stringify([x,z[1]]),p);
    acc(crosspair,JSON.stringify([x,z[a[i]+1]]),p);acc(trunc,JSON.stringify([x,...z.slice(1,a[i]),...z.slice(a[i]+1)]),p)}
   const rho=Array(r).fill(0);for(const [x,p] of root)rho[x]=p;
   const m=Array.from({length:r},()=>Array(r).fill(0));
   for(const [key,p] of intpair){const [x,z]=JSON.parse(key);m[x][z]+=p/rho[x]}
   const Hi=ent(star),HX=ent(root),HA=ent(intpair),HB=ent(crosspair),HT=ent(trunc);
   const J=(a[i]-1)*(HA-HX)+b[i]*(HB-HX)-(HT-HX);
   const Iint=2*HX-HA,V=1-sqnorm(rho),vi=rho.reduce((z,p,x)=>z+p*(1-sqnorm(m[x])),0);
   assert(Hi>=ent(raw)-1e-10,'symmetrization entropy');
   pi.push({star,trunc,root,intpair,crosspair,rho,m,Hi,HX,HA,HB,HT,J,Iint,V,vi});
  }
  for(const [key,p] of pi[0].crosspair){const [x,z]=JSON.parse(key);close(p,pi[1].crosspair.get(JSON.stringify([z,x]))||0,'cross reversal')}
  const Icross=pi[0].HX+pi[1].HX-pi[0].HB;
  const Phi=alpha.reduce((z,w,i)=>z+w*(pi[i].Hi-a[i]/2*pi[i].HA),0)-alpha[0]*b[0]*pi[0].HB;
  const L=-Phi,Lidentity=alpha.reduce((z,w,i)=>z+w*((a[i]/2-1)*pi[i].Iint+pi[i].J),0)+alpha[0]*b[0]*Icross;
  maxCancellationError=Math.max(maxCancellationError,Math.abs(L-Lidentity));close(L,Lidentity,'entropy cancellation');
  const delta=alpha.reduce((z,w,i)=>z+w*(1-Math.max(...pi[i].rho)),0);
  const lower=Math.min(...alpha)*delta*delta/(2*Delta**4);minGapSlack=Math.min(minGapSlack,L-lower);
  assert(L>=lower-1e-10,'global quantitative gap');
  if(delta>1e-10){positiveDefect++;minPositiveL=Math.min(minPositiveL,L);assert(L>0,'strict negativity')}
  else{zeroDefect++;close(L,0,'point map equality')}
  for(let i=0;i<2;i++){
   const P=pi[i],O=pi[1-i],kap=P.J+b[i]*Icross;
   assert(alpha[i]*kap<=L+1e-10,'per-star weighted divergence bound');
   function f(x,labels){const W=[...R[x]];for(const z of labels)W[z]--;return W.reduce((tot,z,j)=>tot+(z-P.m[x][j])**2,0)}
   let EP=0,kl=0;
   for(const [key,p] of P.trunc){const z=JSON.parse(key),x=z[0],labels=z.slice(1);EP+=p*f(x,labels);
    let qp=P.rho[x];for(let j=0;j<labels.length;j++)qp*=j<a[i]-1?P.m[x][labels[j]]:O.rho[labels[j]];
    kl+=p*Math.log(p/qp)}
   close(EP,P.vi,'actual omitted variance');close(kl,kap,'product KL identity');
   let EQ=0;
   for(let x=0;x<r;x++)if(P.rho[x]){
    const slots=[...Array(a[i]-1).fill(P.m[x]),...Array(b[i]).fill(O.rho)];
    function product(j,labels,p){if(j===slots.length){const ff=f(x,labels);assert(ff<=2*nbr[sizes[0]*i].length**2+1e-10,'function range');EQ+=P.rho[x]*p*ff;return}
     for(let z=0;z<r;z++)if(slots[j][z])product(j+1,[...labels,z],p*slots[j][z])}
    product(0,[],1);
   }
   const drift=P.rho.reduce((tot,p,x)=>tot+p*R[x].reduce((z,v,j)=>z+(v-a[i]*P.m[x][j]-b[i]*O.rho[j])**2,0),0);
   const varianceIdentity=(a[i]-2)*P.vi+b[i]*O.V+drift;
   maxVarianceError=Math.max(maxVarianceError,Math.abs(EQ-EP-varianceIdentity));close(EQ-EP,varianceIdentity,'product variance identity');
  }
 }
 y[0]=0;visit(1,0);
 output.examples.push({name,N,sizes,alpha,internalDegrees:a,crossDegrees:b,Delta,setPartitions,equitable,
  positiveDefect,zeroDefect,largestAlphabet,maxCancellationError,maxVarianceError,minGapSlack,minPositiveL});
}
fs.writeFileSync(path.join(__dirname,'rigidity-checks.json'),JSON.stringify(output,null,2)+'\n');
process.stdout.write(JSON.stringify(output,null,2)+'\n');
