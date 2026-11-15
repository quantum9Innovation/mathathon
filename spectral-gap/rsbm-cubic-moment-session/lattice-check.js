// Exact supplementary audits. Run with any recent Node.js.
function check(p) {
  const k=p*p-1, dim=2*k, rows=[];
  const outer=Array.from({length:2*p*p},()=>Array(2*p*p).fill(0));
  function profile(a,d,b,e) {
    const c=(a+d-b+p)%p, f=(a+d-e+p)%p;
    const full=Array(2*p*p).fill(0);
    for(const [off,u,z] of [[0,a,b],[0,a,c],[p*p,d,e],[p*p,d,f]]) full[off+u*p+z]++;
    return full;
  }
  const base=profile(0,0,0,0);
  for(let a=0;a<p;a++)for(let d=0;d<p;d++)for(let b=0;b<p;b++)for(let e=0;e<p;e++) {
    const v=profile(a,d,b,e), ids=v.map((x,i)=>x?i:-1).filter(i=>i>=0);
    for(const i of ids)for(const j of ids)outer[i][j]+=v[i]*v[j];
    rows.push(v.flatMap((x,j)=>j%(p*p)===k?[]:[BigInt(x-base[j])]));
  }
  let covarianceOK=true;
  for(let i=0;i<2*p*p;i++)for(let j=0;j<2*p*p;j++) {
    const bi=Math.floor(i/(p*p)),bj=Math.floor(j/(p*p));
    const u=Math.floor((i%(p*p))/p),v=i%p,r=Math.floor((j%(p*p))/p),s=j%p;
    const expected=bi!==bj?0:(u===r?2*p*p*Number(v===s)+2*p:0)-4;
    covarianceOK &&= outer[i][j]-4===expected;
  }
  // Unimodular row Euclidean elimination of projected support differences.
  for(let col=0;col<dim;col++) {
    const pivot=rows.findIndex((r,i)=>i>=col&&r[col]!==0n);
    if(pivot<0)throw new Error("Rank deficiency at p="+p+", column="+col);
    [rows[col],rows[pivot]]=[rows[pivot],rows[col]];
    for(let i=col+1;i<rows.length;i++)while(rows[i][col]!==0n) {
      const q=rows[i][col]/rows[col][col];
      for(let j=col;j<dim;j++)rows[i][j]-=q*rows[col][j];
      if(rows[i][col]!==0n)[rows[i],rows[col]]=[rows[col],rows[i]];
    }
  }
  const index=Array.from({length:dim},(_,j)=>rows[j][j]).reduce((a,x)=>a*(x<0n?-x:x),1n);
  const expectedIndex=2n**BigInt(2*p-2)*BigInt(p)**3n;
  if(!covarianceOK||index!==expectedIndex)throw new Error("Failed at p="+p);
  return {p,rank:dim,index:String(index),expectedIndex:String(expectedIndex),covarianceOK};
}
const results=[3,5,7].map(check);
console.log(JSON.stringify(results,null,2));
