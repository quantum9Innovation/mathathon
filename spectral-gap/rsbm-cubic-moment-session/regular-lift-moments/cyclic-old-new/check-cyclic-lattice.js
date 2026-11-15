// Exact congruence-rank audit; run with Node.js. No external dependencies.
function rankMod(A,p) {
  if(!A.length)return 0;
  const rows=A.length,cols=A[0].length;
  const inv=Array(p).fill(0);
  for(let x=1;x<p;x++)for(let y=1;y<p;y++)if(x*y%p===1)inv[x]=y;
  let rank=0;
  for(let col=0;col<cols&&rank<rows;col++) {
    let at=rank;while(at<rows&&!A[at][col])at++;
    if(at===rows)continue;
    [A[at],A[rank]]=[A[rank],A[at]];
    const row=A[rank],m=inv[row[col]];
    for(let j=col;j<cols;j++)row[j]=row[j]*m%p;
    for(let i=rank+1;i<rows;i++)if(A[i][col]) {
      const z=A[i][col],rr=A[i];
      for(let j=col;j<cols;j++){let t=(rr[j]-z*row[j])%p;if(t<0)t+=p;rr[j]=t;}
    }
    rank++;
  }
  return rank;
}
function audit(p,R,name,base="K4") {
  const r=R.length,k=base==="K4"?4:8,q=p**r,edges=[];
  if(base==="K4")for(let i=0;i<k;i++)for(let j=i+1;j<k;j++)edges.push([i,j]);
  else {for(let i=0;i<8;i++)edges.push([i,(i+1)%8]);for(let i=0;i<4;i++)edges.push([i,i+4]);}
  const neighbors=Array.from({length:k},()=>[]);
  for(const [i,j] of edges){neighbors[i].push(j);neighbors[j].push(i);}
  const labels=Array.from({length:q},(_,x)=>Array.from({length:r},()=>{const a=x%p;x=Math.floor(x/p);return a;}));
  const rowCount=k*q*r,colCount=k*(q-1)+edges.length*(q-1)**2;
  const C=Array.from({length:rowCount},()=>new Uint8Array(colCount));
  function add(i,a,vector,sign,col) {
    for(let c=0;c<r;c++){const at=(i*q+a)*r+c;let t=(C[at][col]+sign*vector[c])%p;if(t<0)t+=p;C[at][col]=t;}
  }
  let col=0;
  for(let i=0;i<k;i++)for(let a=1;a<q;a++,col++) {
    const av=labels[a],out=Array(r).fill(0);
    for(let c=0;c<r;c++)for(let t=0;t<r;t++)out[c]=(out[c]+av[t]*R[t][c])%p;
    add(i,a,out,-1,col);
    for(const j of neighbors[i])add(j,0,av,1,col);
  }
  for(const [i,j] of edges)for(let a=1;a<q;a++)for(let b=1;b<q;b++,col++) {
    add(i,a,labels[b],1,col);add(i,0,labels[b],-1,col);
    add(j,b,labels[a],1,col);add(j,0,labels[a],-1,col);
  }
  if(col!==colCount)throw Error("Wrong dimension");
  const S=Array.from({length:k*r},()=>new Uint8Array(k*r));
  for(let i=0;i<k;i++)for(let c=0;c<r;c++) {
    const row=S[i*r+c];
    for(const j of neighbors[i])row[j*r+c]=1;
    for(let t=0;t<r;t++)row[i*r+t]=((row[i*r+t]-R[t][c])%p+p)%p;
  }
  const oldHom=k*r-rankMod(S,p),pairs=[];
  for(let i=0;i<r;i++)for(let j=i+1;j<r;j++)pairs.push([i,j]);
  const altEquations=Array.from({length:r*r},()=>new Uint8Array(pairs.length));
  pairs.forEach(([i,j],c)=>{
    const K=Array.from({length:r},()=>Array(r).fill(0));K[i][j]=1;K[j][i]=p-1;
    for(let a=0;a<r;a++)for(let b=0;b<r;b++) {
      let z=0;for(let t=0;t<r;t++)z+=R[a][t]*K[t][b]-K[a][t]*R[b][t];
      altEquations[a*r+b][c]=((z%p)+p)%p;
    }
  });
  const alternating=pairs.length-rankMod(altEquations,p);
  const actualRank=rankMod(C,p),dependencies=rowCount-actualRank;
  const ok=dependencies===oldHom+alternating;
  if(!ok)throw Error("Rank mismatch in "+name);
  return {name,base,p,r,q,compatibleDimension:colCount,congruenceCount:rowCount,rank:actualRank,dependencies,oldHom,alternating,ok};
}
const reports=[
 audit(3,[[0,1],[2,0]],"irreducible-x2+1"),
 audit(3,[[2,1],[0,2]],"cyclic-Jordan-minus1"),
 audit(3,[[2,0],[0,2]],"noncyclic-scalar-minus1"),
 audit(5,[[0,1],[3,0]],"irreducible-x2+2"),
 audit(3,[[0,1,0],[0,0,1],[2,1,0]],"irreducible-x3+2x+1"),
 audit(3,[[2,0,0],[0,2,0],[0,0,2]],"noncyclic-rank3-scalar"),
 audit(3,[[0,1],[1,1]],"irreducible-old-irrational-factor","mobius8")
];
console.log(JSON.stringify(reports,null,2));
