// Exact certificate for bass-circle-counterexample.txt.
// Run with Node.js, or evaluate in a JavaScript runtime supporting BigInt.
// No packages, floating-point eigenvalue computation, or network needed.
(() => {
  function assert(condition, message) {
    if (!condition) throw new Error(message);
  }
  function eq(a, b) {
    return a.length === b.length && a.every((v, i) => v === b[i]);
  }
  const n = 14;
  const edges = [
    [0, 3], [0, 6], [0, 12], [1, 2], [1, 4], [1, 5],
    [2, 3], [2, 7], [3, 11], [4, 6], [4, 8], [5, 11],
    [5, 13], [6, 9], [7, 9], [7, 13], [8, 10], [8, 12],
    [9, 10], [10, 11], [12, 13]
  ];
  const adj = Array.from({length: n}, () => []);
  const seenEdges = new Set();
  for (const [a, b] of edges) {
    assert(a < b && !seenEdges.has(a + ',' + b), 'simple graph');
    seenEdges.add(a + ',' + b);
    adj[a].push(b); adj[b].push(a);
  }
  assert(adj.every(vs => vs.length === 3), 'cubic graph');
  let girth = Infinity;
  for (let start = 0; start < n; start++) {
    const dist = Array(n).fill(-1), parent = Array(n).fill(-1);
    const queue = [start]; dist[start] = 0;
    for (let i = 0; i < queue.length; i++) {
      const v = queue[i];
      for (const w of adj[v]) {
        if (dist[w] < 0) {
          dist[w] = dist[v] + 1; parent[w] = v; queue.push(w);
        } else if (parent[v] !== w) {
          girth = Math.min(girth, dist[v] + dist[w] + 1);
        }
      }
    }
    assert(queue.length === n, 'connected graph');
  }
  assert(girth === 5, 'girth exactly five');
  const cycle = [0, 6, 4, 8, 12, 0];
  assert(cycle.slice(1).every((w, i) => adj[cycle[i]].includes(w)),
    'explicit five-cycle');

  function characteristic(A) {
    let power = Array.from({length: n}, (_, i) =>
      Array.from({length: n}, (_, j) => i === j ? 1n : 0n));
    const traces = [BigInt(n)];
    for (let k = 1; k <= n; k++) {
      power = power.map(row => Array.from({length: n}, (_, j) =>
        row.reduce((sum, value, l) => sum + value * A[l][j], 0n)));
      traces.push(power.reduce((sum, row, i) => sum + row[i], 0n));
    }
    const coefficients = [1n];
    for (let k = 1; k <= n; k++) {
      let sum = 0n;
      for (let j = 1; j <= k; j++) sum += coefficients[k-j] * traces[j];
      assert(sum % BigInt(k) === 0n, 'integer Newton coefficient');
      coefficients.push(-sum / BigInt(k));
    }
    return coefficients;
  }
  function convolve(a, b) {
    const c = Array(a.length + b.length - 1).fill(0n);
    a.forEach((v, i) => b.forEach((w, j) => { c[i+j] += v * w; }));
    return c;
  }
  const factor = [1n, 0n, -4n, 0n, 4n]; // (x^2-2)^2
  const r = [1n, 0n, -17n, 0n, 96n, 0n, -204n, 0n, 120n, 0n, -4n];
  const s = [0n, 0n, 0n, 0n, 0n, 4n, 0n, -16n, 0n, -8n, 0n];
  const expectedPlus = convolve(factor, r.map((v, i) => v - s[i]));
  const expectedMinus = convolve(factor, r.map((v, i) => v + s[i]));
  const A = Array.from({length: n}, () => Array(n).fill(0n));
  for (const [a, b] of edges) A[a][b] = A[b][a] = 1n;
  A[2][7] = A[7][2] = -1n;
  const pPlus = characteristic(A);
  assert(eq(pPlus, expectedPlus), 'pPlus exact factorization');
  A[4][6] = A[6][4] = -1n;
  const pMinus = characteristic(A);
  assert(eq(pMinus, expectedMinus), 'pMinus exact factorization');
  assert(eq(pMinus, pPlus.map((v, i) => i % 2 ? -v : v)),
    'reflection pMinus(x)=pPlus(-x)');
  const parent = convolve(factor, r);
  assert(eq(pPlus.map((v, i) => v + pMinus[i]), parent.map(v => 2n*v)),
    'conditional parent exact polynomial');

  // Return b^5 f(a/b), an integer of the same sign as f(a/b).
  const f = [1n, -17n, 96n, -204n, 120n, -4n];
  function fRational(a, b) {
    return f.reduce((sum, coefficient, i) => sum + coefficient *
      a ** BigInt(5-i) * b ** BigInt(i), 0n);
  }
  const points = [[0n, 1n], [1n, 16n], [1n, 1n],
    [4n, 1n], [5n, 1n], [8n, 1n]];
  const values = points.map(([a, b]) => fRational(a, b));
  assert(eq(values, [-4n, 2858737n, -8n, 28n, -4n, 188n]),
    'exact rational sign values');
  assert(values.every((v, i) => i % 2 ? v > 0n : v < 0n),
    'five positive parent roots below eight');
  // pPlus(2sqrt(2)) = (8-2)^2 [f(8) - 120*(2sqrt(2))].
  assert(fRational(8n, 1n) === 188n, 'even endpoint part');
  assert(4n*64n - 16n*8n - 8n === 120n, 'odd endpoint coefficient');
  assert(188n > 0n && 188n**2n < 2n * 240n**2n,
    '188 - 240sqrt(2) negative');

  // Verify the fixed singular spectrum of B on this signed graph:
  // after independent row/column permutations its vertex block is
  // (J_3-I_3)D. Its Gram eigenvalues are 4,1,1.
  for (let v = 0; v < n; v++) {
    const block = adj[v].map((u, i) => adj[v].map((w, j) =>
      i === j ? 0n : A[v][w]));
    const gram = block.map(row => block.map(other =>
      row.reduce((sum, val, k) => sum + val * other[k], 0n)));
    assert(gram.every((row, i) => row.every((val, j) =>
      val === (i === j ? 2n : 1n))), 'block Gram = J_3 + I_3');
  }
  const result = {
    status: 'PASS', vertices: n, edges: edges.length, girth,
    fiveCycle: cycle,
    pPlus: pPlus.map(String), pMinus: pMinus.map(String),
    rationalSignNumerators: values.map(String),
    endpointCertificate: '36*(188-240*sqrt(2)) < 0'
  };
  if (typeof console !== 'undefined') console.log(JSON.stringify(result, null, 2));
  return result;
})()
