function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a}
function frac(n,d=1n){if(d<0n){n=-n;d=-d}let g=gcd(n,d);return {n:n/g,d:d/g}}
function fadd(a,b){return frac(a.n*b.d+b.n*a.d,a.d*b.d)}
function fmul(a,n){return frac(a.n*n,a.d)}
function fdiv(a,n){return frac(a.n,a.d*n)}
function exactKernel(M){
 let A=M.map(row=>row.map(BigInt)),n=A.length,m=A[0].length,r=0,prev=1n,piv=[];
 for(let c=0;c<m&&r<n;c++){
  let z=r;while(z<n&&A[z][c]===0n)z++;if(z===n)continue;
  [A[r],A[z]]=[A[z],A[r]];let p=A[r][c];
  for(let i=r+1;i<n;i++){let ai=A[i][c];for(let j=c+1;j<m;j++){let num=p*A[i][j]-ai*A[r][j];if(num%prev!==0n)throw Error("Bareiss nonexact");A[i][j]=num/prev;}A[i][c]=0n;}
  prev=p;piv.push(c);r++;
 }
 let free=Array.from({length:m},(_,i)=>i).filter(i=>!piv.includes(i));
 let vectors=free.map(f=>{let v=Array.from({length:m},()=>frac(0n));v[f]=frac(1n);
  for(let i=piv.length-1;i>=0;i--){let sum=frac(0n);for(let j=piv[i]+1;j<m;j++)sum=fadd(sum,fmul(v[j],A[i][j]));v[piv[i]]=fdiv(fmul(sum,-1n),A[i][piv[i]]);}
  let den=v.reduce((l,a)=>l/gcd(l,a.d)*a.d,1n),vec=v.map(a=>a.n*(den/a.d)),g=vec.reduce((g,a)=>gcd(g,a),0n);
  return vec.map(a=>a/g);
 });
 return {rank:r,vectors};
}
