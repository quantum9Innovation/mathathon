/*
 * Independent, dependency-free numerical checks.
 * Run with any modern JavaScript engine, e.g.:
 *   node check_reverse_schur_and_exact_spectrum.js
 * The same source can run in the functions JavaScript tool runtime.
 * Double-precision diagnostics support, but do not replace, the proofs.
 */
const emit = typeof text === "function"
  ? text
  : value => console.log(JSON.stringify(value, null, 2));

function identity(n) {
  return Array.from({length: n}, (_, i) =>
    Array.from({length: n}, (_, j) => +(i === j)));
}

function matmul(A, B) {
  return A.map(row => B[0].map((_, j) =>
    row.reduce((sum, value, k) => sum + value * B[k][j], 0)));
}

function transpose(A) {
  return A[0].map((_, j) => A.map(row => row[j]));
}

function jacobi(A0) {
  const A = A0.map(row => row.slice());
  const n = A.length;
  const V = identity(n);
  for (let iteration = 0; iteration < 100 * n * n; iteration++) {
    let p = 0, q = 1, maximum = 0;
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        if (Math.abs(A[i][j]) > maximum) {
          maximum = Math.abs(A[i][j]);
          p = i;
          q = j;
        }
      }
    }
    if (maximum < 1e-28) break;
    const apq = A[p][q];
    const tau = (A[q][q] - A[p][p]) / (2 * apq);
    const t = (tau >= 0 ? 1 : -1) /
      (Math.abs(tau) + Math.sqrt(1 + tau * tau));
    const c = 1 / Math.sqrt(1 + t * t);
    const s = t * c;
    A[p][p] -= t * apq;
    A[q][q] += t * apq;
    A[p][q] = A[q][p] = 0;
    for (let k = 0; k < n; k++) {
      if (k === p || k === q) continue;
      const kp = A[k][p], kq = A[k][q];
      A[k][p] = A[p][k] = c * kp - s * kq;
      A[k][q] = A[q][k] = s * kp + c * kq;
    }
    for (let k = 0; k < n; k++) {
      const kp = V[k][p], kq = V[k][q];
      V[k][p] = c * kp - s * kq;
      V[k][q] = s * kp + c * kq;
    }
  }
  return {values: A.map((row, i) => row[i]), V};
}

function power(A, alpha) {
  const {values, V} = jacobi(A);
  if (!values.every(value => value > 0)) {
    throw new Error("Positive matrix power encountered a nonpositive eigenvalue");
  }
  return matmul(V.map(row => row.map((value, j) =>
    value * Math.pow(values[j], alpha))), transpose(V));
}

function relative(S, diagonal, alpha) {
  const B = S.map((row, i) => row.map((value, j) =>
    value * Math.sqrt(diagonal[i] * diagonal[j])));
  return power(B, alpha).map((row, i) => row.map((value, j) =>
    value / Math.pow(diagonal[i] * diagonal[j], alpha / 2)));
}

function maxEntryNorm(A) {
  return Math.max(...A.flat().map(Math.abs));
}

const alpha = 0.37;
const S = [[2, 0.3, -0.2], [0.3, 1.6, 0.4], [-0.2, 0.4, 1.3]];
const pivots = [
  2 - (0.3 * 0.3 * 1.3 + 2 * 0.3 * 0.2 * 0.4 +
       0.2 * 0.2 * 1.6) / (1.6 * 1.3 - 0.4 * 0.4),
  1.6 - 0.4 * 0.4 / 1.3,
  1.3
];
const scale = [0.1, 0.01, 0.001, 0.0001].map(delta => {
  const Q = relative(S, [delta * delta, delta, 1], alpha);
  return {
    delta,
    maxEntryError: maxEntryNorm(Q.map((row, i) => row.map((value, j) =>
      value - (i === j ? Math.pow(pivots[i], alpha) : 0))))
  };
});
if (!scale.every((value, i) => i === 0 ||
    value.maxEntryError < scale[i - 1].maxEntryError)) {
  throw new Error("The reverse-Schur diagnostic did not converge monotonically");
}

const target = [0.9, 0.5, 0.2];
const total = 1.6;
const delta = 0.005;
function rankOne(x) {
  const z = x.map((xi, i) => (Math.exp(xi) - 1) *
    Math.exp(x.slice(i + 1).reduce((sum, value) => sum + value, 0)));
  if (!z.every(value => value > 0)) {
    throw new Error("Newton iteration left the positive-pivot region");
  }
  const rankOneS = z.map((zi, i) => z.map((zj, j) =>
    (i === j ? 1 : 0) + Math.sqrt(zi * zj)));
  const Q = relative(rankOneS, [delta * delta, delta, 1], alpha);
  return {
    Q,
    z,
    F: jacobi(Q).values.sort((a, b) => b - a)
      .map(value => Math.log(value) / alpha)
  };
}

const x = target.slice();
const history = [];
for (let step = 0; step < 12; step++) {
  const output = rankOne(x);
  const residual = output.F.slice(0, 2).map((value, i) => value - target[i]);
  history.push(Math.max(...residual.map(Math.abs)));
  if (history[history.length - 1] < 1e-11) break;
  const J = [[], []];
  const h = 1e-5;
  for (let j = 0; j < 2; j++) {
    const y = x.slice();
    y[j] += h;
    y[2] -= h;
    const Fy = rankOne(y).F;
    for (let i = 0; i < 2; i++) J[i][j] = (Fy[i] - output.F[i]) / h;
  }
  const determinant = J[0][0] * J[1][1] - J[0][1] * J[1][0];
  const dx = [
    (J[1][1] * residual[0] - J[0][1] * residual[1]) / determinant,
    (-J[1][0] * residual[0] + J[0][0] * residual[1]) / determinant
  ];
  x[0] -= dx[0];
  x[1] -= dx[1];
  x[2] = total - x[0] - x[1];
}
const output = rankOne(x);
if (Math.max(...output.F.map((value, i) => Math.abs(value - target[i]))) > 1e-10) {
  throw new Error("The exact-spectrum Newton diagnostic did not converge");
}
const diagnostics = {
  general_reverse_schur: pivots,
  scale,
  exact_inverse_sample: {
    alpha,
    delta,
    targetLogPivots: target,
    inputLogPivots: x,
    outputLogSpectrum: output.F,
    newtonResiduals: history,
    leverage: output.z.reduce((sum, value) => sum + value, 0),
    targetLeverage: Math.exp(total) - 1
  }
};
emit(diagnostics);
