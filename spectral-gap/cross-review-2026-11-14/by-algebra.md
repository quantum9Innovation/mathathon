# Independent review of the sharp cubic scaling theorem

Date: 15 November 2026.

Reviewed artifact: `audit-2026-11-14/sharp-scaling-v1.md`, frozen revision 1, SHA-256 `fd7383e644319b6d6f9755c3412616923da5e2d9cf7d31bab94d67836d2bb0ec`.

Verdict: **supported**. The normalized recurrences, both lower bounds, the elementary upper bound, and the necessary-and-sufficient asymptotic criterion are correct on their stated domains. No mathematical flaw was found. This review was completed without reading another integrator verdict or the other spectral audit reports.

## 1. Exact source match and contribution boundary

The saved final [Collins and Nagatsu paper](https://alco.centre-mersenne.org/item/10.5802/alco.480.pdf) is *Weingarten calculus for centered random permutation matrices*, Algebraic Combinatorics 9(2) (2026), pages 465 to 479. Its SHA-256 is `c5b124655a495c03017b3866542ebd1f3289921cc4ed053244cc885cb8db017e`, matching the draft. The present review extracted the relevant text directly from that PDF rather than relying only on the saved text transcription. A fresh web fetch of the PDF returned HTTP 403, so the source comparison rests on the saved final PDF.

Proposition 3.3, equations (13) and (14), gives precisely the even and odd leading terms used in the draft, with a relative error estimate when `N` dominates `k^3`. Equation (16) on printed page 472 is the draft's recurrence S6. The two normalized recurrences S7 and S8 also appear explicitly in the proof on that page.

Remark 3.4 remains in the final publication on printed page 473. It identifies the proof's `k^3 <= C N` scale and says:

> It would be interesting to check whether this is the optimal scaling.

The draft supplies necessity for relative convergence to those particular leading terms, and hence directly resolves that interpretation of the scaling question. It does not establish a new graph spectral-gap theorem or rule out all other useful centered-moment bounds. Its explicit scope statement is appropriate.

Attribution refinement: the positive recurrence, the leading terms, and the normalized recurrences are prior material. The new step is to preserve the positive forcing term, sum it, propagate the resulting bound to odd indices, and deduce necessity. The draft already places the novelty in that inference, but explicitly crediting the printed normalized recurrences would make the distinction clearest. No literature-wide priority conclusion is established by this source check.

## 2. Reconstruction of the recurrence

For `2 <= k <= N`, multiply the zero sum of the last centered row by the first `k-1` centered diagonal entries. The `N-k+1` unused columns give the same moment `a_k`. Each used column creates two different entries `X,Y` with `XY=0`. Therefore

\[
(X-N^{-1})(Y-N^{-1})
=-N^{-1}(X-N^{-1})-N^{-1}(Y-N^{-1})-N^{-2}.
\]

The two shorter moments have the same distribution by a row permutation. Solving the resulting equation gives

\[
a_k=
\frac{2(k-1)}{N(N-k+1)}a_{k-1}
+\frac{k-1}{N^2(N-k+1)}a_{k-2}.
\]

Its denominators are positive even at `k=N`. Together with `a_0=1` and `a_1=0`, it proves positivity for every `k>=2` in the stated domain.

## 3. Independent normalization, S7 and S8

For even `k=2m`, division by its leading term gives the two homogeneous coefficients

\[
\alpha_m=\frac{N}{N-2m+1},
\qquad
\beta_m=\frac{4(2m-1)(2m-2)}{3(N-2m+1)}.
\]

They multiply `R_{2m-2}` and `R_{2m-1}`, respectively. Their sum minus one is

\[
\alpha_m+\beta_m-1
=\frac{(2m-1)(8m-5)}{3(N-2m+1)}.
\]

Substituting `R=1+E` gives exactly S7. The formula uses `m>=2`, so the undefined ratio at index one is never introduced.

For odd `k=2m+1`, the two homogeneous coefficients are

\[
u_m=\frac{3N}{(N-2m)(2m+1)},
\qquad
v_m=\frac{(2m-2)N}{(N-2m)(2m+1)}.
\]

Their sum is `N/(N-2m)`, giving the forcing term `2m/(N-2m)` in S8. At `m=1`, the coefficient `v_m` is zero. Omitting the index-one term is therefore exact. The starting value `E_2=1/(N-1)` is also exact.

All coefficients and forcing terms are nonnegative. This proves `E_k>=0`, which is essential for the later term deletion and denominator estimates.

## 4. Lower bounds and the identity S9

From S7, positivity and `N/(N-2m+1)>=1` give

\[
E_{2m}\ge E_{2m-2}
+\frac{(2m-1)(8m-5)}{3N}.
\]

The base at `m=1` is `E_2>=1/N`. Summing yields

\[
E_{2m}\ge\frac{C_e(m)}{N},
\qquad
C_e(m)=\frac{m(16m^2-3m-4)}9.
\]

The summation is valid for every `2m<=N`, including the endpoint. Its polynomial satisfies `C_e(m)>=m^3` for every positive integer `m`.

Define

\[
C_o(m)=\frac{80m^3+195m^2+124m+6}{135}.
\]

Direct expansion gives

\[
(2m+1)C_o(m)-(2m-2)C_o(m-1)
=3C_e(m)+2m(2m+1).
\]

This is S9 after division by `2m+1`. Also `C_o(1)=3`. Applying S8, replacing `N/(N-2m)` by one in its nonnegative terms, gives

\[
E_{2m+1}\ge
\frac{3E_{2m}+(2m-2)E_{2m-1}}{2m+1}
+\frac{2m}{N}.
\]

Induction proves `E_{2m+1}>=C_o(m)/N`. The base follows directly from `E_3>=E_2+2/N`.

The common bound follows from `C_e(m)>=(2m)^3/8` and

\[
C_o(m)-\frac{2(2m+1)^3}{27}
=\frac{75m^2+64m-4}{135}>0.
\]

Thus S1 holds for all `2<=k<=N`. In particular, no restriction to one parity or to `k=o(N)` was silently used in its proof.

## 5. Upper bound and the equivalence

Assume `2k<=N`. For every `j<=k`, the denominator `N-j+1` is at least `N/2`. If `j` is even, the sum of the recurrence coefficients is

\[
1+\frac{(j-1)(4j-5)}{3(N-j+1)}
\le1+\frac{3j^2}{N}.
\]

For odd `j`, it is `N/(N-j+1)` and obeys the same bound. The initial ratio `R_2=N/(N-1)` does as well. Positivity therefore bounds the successive running maximum by

\[
\prod_{j=2}^k\left(1+\frac{3j^2}{N}\right)
\le\exp\left(\frac3N\sum_{j=2}^k j^2\right)
\le\exp(3k^3/N).
\]

This proves S4 without using the asymptotic estimate from the paper.

Now let `2<=k_N<=N` be any integer sequence. If `R_{k_N}` tends to one, S1 gives

\[
0\le\frac{k_N^3}{N}\le\frac{27}{2}(R_{k_N}-1)\longrightarrow0.
\]

Conversely, `k_N^3/N` tending to zero forces `2k_N<=N` eventually. The lower bound `R>=1` and S4 then squeeze the ratio to one. This proves S5 in its full stated generality, including bounded or mixed-parity sequences.

At `k` comparable to `N^{1/3}`, S1 gives a positive lower bound on the relative error. If `k^3/N` tends to infinity, it forces the ratio to infinity. Both consequences are justified. No critical-scale limit follows from these estimates alone, and the draft does not claim one.

## 6. Fresh computational checks and their limits

A separate standard-library rational-arithmetic check was executed under a 60-second time limit and a 256 MiB memory limit. It did not call or inspect the existing spectral verification code.

| Check | Fresh range | Passed instances |
|---|---|---:|
| Moment recurrence against direct inclusion-exclusion | `2<=N<=30`, every `2<=k<=N` | 435 |
| Exact S7 normalized identity | `2<=N<=80`, every applicable even `k` | 1521 |
| Exact S8 normalized identity | `2<=N<=80`, every applicable odd `k` | 1560 |
| S1 and the parity-specific lower bound | `2<=N<=80`, every `2<=k<=N` | 3160 |
| Rational product bound preceding the exponential estimate | `2<=N<=80`, every `2k<=N` | 1521 |
| S9 polynomial identity | `1<=m<=1000` | 1000 |

The independent moment formula used was

\[
a_k(N)=\sum_{j=0}^k
\binom{k}{j}\frac{(-1)^{k-j}}{N^{k-j}(N)_j}.
\]

Every check passed. These finite calculations corroborate the identities and endpoint handling. The symbolic derivations above establish the unrestricted theorem.

## Final assessment

The draft proves its precise result and gives a direct, elementary answer to the leading-term relative-accuracy reading of the published scaling question. Its strongest defensible contribution is the necessity of the cubic scale, with an explicit global lower bound. The only suggested change is sharper attribution for the already published normalized recurrences. External novelty beyond the named paper remains a separate question.
