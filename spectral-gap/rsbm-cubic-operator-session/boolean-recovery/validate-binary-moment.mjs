// Dependency-free exact checks of the binary profile formula and recovery.
// Run with: node validate-binary-moment.mjs

const factorial = n => { let a=1n; for(let j=2;j<=n;j++) a*=BigInt(j); return a; };
const oddDoubleFactorial = n => { let a=1n; for(let j=n;j>0;j-=2) a*=BigInt(j); return a; };

function binaryRank(rows, n) {
  rows=rows.slice(); let rank=0;
  for(let j=0;j<n;j++) {
    const bit=1n<<BigInt(j);
    const p=rows.findIndex((r,i)=>i>=rank && (r&bit)!==0n);
    if(p<0) continue;
    [rows[p],rows[rank]]=[rows[rank],rows[p]];
    for(let i=rank+1;i<n;i++) if(rows[i]&bit) rows[i]^=rows[rank];
    rank++;
  }
  return rank;
}

function allPairings(stubs) {
  if(!stubs.length) return [[]];
  const a=stubs[0], out=[];
  for(let j=1;j<stubs.length;j++) {
    const rest=stubs.filter((_,i)=>i!==0 && i!==j);
    for(const pairs of allPairings(rest)) out.push([[a,stubs[j]],...pairs]);
  }
  return out;
}

function configurationMatrix(n, plus, minus) {
  const rows=Array.from({length:2*n},(_,i)=>1n<<BigInt(i));
  for(let i=0;i<n;i++) {
    rows[i]^=1n<<BigInt(i+n); rows[i+n]^=1n<<BigInt(i);
  }
  for(const [pairs,shift] of [[plus,0],[minus,n]]) for(const [a,b] of pairs) {
    const u=(a>>1)+shift, v=(b>>1)+shift;
    // A loop is counted twice on the diagonal and vanishes modulo two.
    rows[u]^=1n<<BigInt(v); rows[v]^=1n<<BigInt(u);
  }
  return rows;
}

function momentByPairings(n) {
  const pairings=allPairings(Array.from({length:2*n},(_,i)=>i));
  let numerator=0n;
  for(const plus of pairings) for(const minus of pairings) {
    const k=2*n-binaryRank(configurationMatrix(n,plus,minus),2*n);
    numerator+=1n<<BigInt(k);
  }
  return {numerator, denominator:BigInt(pairings.length)**2n};
}

function momentByProfiles(n) {
  let numerator=0n;
  const counts=Array(16).fill(0);
  const profiles=Array.from({length:16},(_,i)=>({
    a:(i>>3)&1, d:(i>>2)&1, b:(i>>1)&1, e:i&1
  }));
  function evaluate() {
    const plus=[0,0,0,0], minus=[0,0,0,0];
    let divisor=1n;
    for(let i=0;i<16;i++) {
      const {a,d,b,e}=profiles[i], c=a^d^b, f=a^d^e, z=counts[i];
      divisor*=factorial(z);
      plus[2*a+b]+=z; plus[2*a+c]+=z;
      minus[2*d+e]+=z; minus[2*d+f]+=z;
    }
    function weight(m) {
      if(m[1]!==m[2] || m[0]%2 || m[3]%2) return 0n;
      return factorial(m[1])*oddDoubleFactorial(m[0]-1)*oddDoubleFactorial(m[3]-1);
    }
    numerator+=(factorial(n)/divisor)*weight(plus)*weight(minus);
  }
  function visit(i,left) {
    if(i===15) { counts[i]=left; evaluate(); return; }
    for(let j=0;j<=left;j++) { counts[i]=j; visit(i+1,left-j); }
  }
  visit(0,n);
  return {numerator,denominator:oddDoubleFactorial(2*n-1)**2n};
}

const results=[];
for(const n of [1,2,3,4]) {
  const direct=momentByPairings(n), typed=momentByProfiles(n);
  if(direct.numerator!==typed.numerator || direct.denominator!==typed.denominator)
    throw new Error(`Exact moment mismatch at N=${n}`);
  results.push({N:n,numerator:String(direct.numerator),denominator:String(direct.denominator)});
}

// The earlier exact N=8 example has real corank two but unique Boolean cut.
const n=8, cycles=[[0,1,2,3,4,5,6,7],[5,6,7,0,4,1,2,3]];
const adj=Array.from({length:2*n},()=>[]);
function edge(a,b) {adj[a].push(b);adj[b].push(a);}
for(let side=0;side<2;side++) for(let i=0;i<n;i++)
  edge(cycles[side][i]+side*n,cycles[side][(i+1)%n]+side*n);
for(let i=0;i<n;i++) edge(i,i+n);
let paritySolutions=0, accepted=[];
for(let mask=0;mask<(1<<(2*n));mask++) {
  const crossing=adj.map((neighbors,i)=>neighbors.reduce((s,j)=>s+(((mask>>i)^(mask>>j))&1),0));
  if(crossing.every(r=>r%2===1)) paritySolutions++;
  if(crossing.every(r=>r===1)) accepted.push(mask);
}
if(accepted.length!==2 || accepted[0]!==255 || accepted[1]!==65280)
  throw new Error('The exact N=8 recovery check failed');
console.log(JSON.stringify({configurationMomentChecks:results,realCorankTwoExample:{paritySolutions,accepted}},null,2));
