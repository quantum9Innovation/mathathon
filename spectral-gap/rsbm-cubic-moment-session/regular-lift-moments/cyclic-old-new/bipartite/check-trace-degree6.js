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

// g(t)=t^6+2t^2+1 over F3 is irreducible:
// f(z)=z^3+2z+1 has no F3 root; its root c has norm -1,
// hence c is nonsquare in F27 and adjoining sqrt(c) has degree six.
// Here s=3 is divisible by p: Tr_F27/F3(1)=0.
const p=3,r=6,R=Array.from({length:r},()=>Array(r).fill(0));
for(let i=0;i<r-1;i++)R[i][i+1]=1;
R[r-1]=[2,0,1,0,0,0];
const equations=Array.from({length:2*r*r},()=>new Uint8Array(r*r));
for(let u=0;u<r;u++)for(let v=0;v<r;v++){
  const j=u*r+v;
  for(let a=0;a<r;a++)for(let b=0;b<r;b++){
    equations[a*r+b][j]=(R[a][u]*Number(b===v)+R[b][u]*Number(a===v))%p;
    equations[r*r+a*r+b][j]=(R[a][v]*Number(b===u)+R[b][v]*Number(a===u))%p;
  }
}
const extra=r*r-rankMod(equations,p);
if(extra!==3)throw Error("Unexpected form dimension");
console.log(JSON.stringify({p,degree:r,s:3,traceOfOne:0,extraFormDimension:extra,expected:3,ok:true},null,2));
