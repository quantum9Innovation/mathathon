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
function auditBip(p,base,rL,rR,TL,TR,name) {
  const m=base==="heawood"?7:3,k=2*m,edges=[];
  if(base==="heawood")for(let i=0;i<m;i++)for(const d of [0,1,3])edges.push([i,m+(i+d)%m]);
  else for(let i=0;i<m;i++)for(let j=0;j<m;j++)edges.push([i,m+j]);
  const dims=Array.from({length:k},(_,i)=>i<m?rL:rR),opp=dims.map((_,i)=>i<m?rR:rL);
  const qs=dims.map(r=>p**r),labels=dims.map((r,i)=>Array.from({length:qs[i]},(_,x)=>Array.from({length:r},()=>{const a=x%p;x=Math.floor(x/p);return a;})));
  const maps=Array.from({length:k},(_,i)=>i<m?TL:TR),neighbors=Array.from({length:k},()=>[]);
  for(const [i,j]of edges){neighbors[i].push(j);neighbors[j].push(i);}
  const rowsAt=[],inAt=[],outAt=[];let rowCount=0,inCount=0,outCount=0;
  for(let i=0;i<k;i++){rowsAt.push(rowCount);rowCount+=qs[i]*opp[i];inAt.push(inCount);inCount+=dims[i];outAt.push(outCount);outCount+=opp[i];}
  const colCount=qs.reduce((s,q)=>s+q-1,0)+edges.reduce((s,[i,j])=>s+(qs[i]-1)*(qs[j]-1),0);
  const C=Array.from({length:rowCount},()=>new Uint8Array(colCount));
  function add(i,a,v,sgn,col){for(let c=0;c<opp[i];c++){const at=rowsAt[i]+a*opp[i]+c;C[at][col]=((C[at][col]+sgn*v[c])%p+p)%p;}}
  let col=0;
  for(let i=0;i<k;i++)for(let a=1;a<qs[i];a++,col++) {
    const av=labels[i][a],out=Array(opp[i]).fill(0);
    for(let c=0;c<opp[i];c++)for(let t=0;t<dims[i];t++)out[c]=(out[c]+av[t]*maps[i][t][c])%p;
    add(i,a,out,-1,col);for(const j of neighbors[i])add(j,0,av,1,col);
  }
  for(const [i,j]of edges)for(let a=1;a<qs[i];a++)for(let b=1;b<qs[j];b++,col++){
    add(i,a,labels[j][b],1,col);add(i,0,labels[j][b],-1,col);add(j,b,labels[i][a],1,col);add(j,0,labels[i][a],-1,col);
  }
  if(col!==colCount)throw Error("Wrong dimension");
  const old=Array.from({length:outCount},()=>new Uint8Array(inCount));
  for(let i=0;i<k;i++)for(let c=0;c<opp[i];c++){
    const rr=old[outAt[i]+c];for(const j of neighbors[i])rr[inAt[j]+c]=1;
    for(let t=0;t<dims[i];t++)rr[inAt[i]+t]=((rr[inAt[i]+t]-maps[i][t][c])%p+p)%p;
  }
  const oldHom=inCount-rankMod(old,p),vars=rL*rR,eq=Array.from({length:rL*rL+rR*rR},()=>new Uint8Array(vars));
  for(let u=0;u<rR;u++)for(let v=0;v<rL;v++){
    const j=u*rL+v;
    for(let a=0;a<rL;a++)for(let b=0;b<rL;b++)eq[a*rL+b][j]=(TL[a][u]*Number(b===v)+TL[b][u]*Number(a===v))%p;
    for(let a=0;a<rR;a++)for(let b=0;b<rR;b++)eq[rL*rL+a*rR+b][j]=(TR[a][v]*Number(b===u)+TR[b][v]*Number(a===u))%p;
  }
  const forms=vars-rankMod(eq,p),rank=rankMod(C,p),dependencies=rowCount-rank,ok=dependencies===oldHom+forms;
  if(!ok)throw Error("Mismatch "+name);
  return{name,base,p,rL,rR,compatibleDimension:colCount,congruenceCount:rowCount,rank,dependencies,oldHom,forms,ok};
}
const even=[[0,1],[2,0]],nonEven=[[0,1],[1,2]];
const reports=[
 auditBip(3,"K33",2,2,even,even,"even-irreducible"),
 auditBip(3,"K33",2,2,nonEven,nonEven,"non-even-irreducible"),
 auditBip(5,"K33",1,1,[[0]],[[0]],"zero-target"),
 auditBip(3,"K33",1,1,[[1]],[[2]],"even-line-restriction"),
 auditBip(5,"K33",1,0,[[]],[],"zero-mixed-restriction"),
 auditBip(3,"heawood",2,2,even,even,"irrational-old-even-factor"),
 auditBip(3,"heawood",1,1,[[1]],[[2]],"irrational-old-line-restriction"),
 auditBip(3,"heawood",1,1,[[0]],[[0]],"zero-target-bad-base-prime")
];
console.log(JSON.stringify(reports,null,2));
