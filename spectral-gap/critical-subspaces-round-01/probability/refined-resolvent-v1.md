# Selected-sector resolvent estimates at criticality

November 15, 2026. Owner: probability workstream. Revision 1, frozen for separate review.

## 1. Scope, exposure and dependencies

This proof supplies quantitative probability estimates for the critical cubic model. It does not by itself prove a graph eigenvector normal form. The deterministic subspace transfer and finite resonance algebra are separate inputs to that application.

The marks are predetermined before the host is sampled. All statements are uniform in that predetermined choice, not simultaneous over all subsets of an observed graph. Prior exposure includes the earlier marked-resolvent proofs and their reviews. During this round the integrator suggested the analytic isometry transfer and asked for a rate sufficient to distinguish detunings of order `m^(-3/4)`. The finite algebra owner supplied the positive bright-mode coupling and warned that the negative antisymmetric modes have a finer degeneracy. No new probability proof by another owner was read before freezing this file.

Frozen dependencies:

- `growing-defects-round-01/probability/proof-v1.md`, SHA256 `56df2949df4d72b3ea48f5e7541218bfc9c70030a66891a32eb4b93aa00c102b`.
- `close-pair-transition-round-01/root/nonbacktracking-upper-v1.md`, SHA256 `d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896`.
- `critical-law-round-01/probability/pair-counts-v1.md`, SHA256 `702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29`.
- `critical-law-round-01/root/effective-operator-v1.md`, SHA256 `13b559897d6ed9253a2fc6dd4dede5dd03914c078558d759542afc9c54d28864`.

The only published probability premises retained through those files are a positive fixed-degree simplicity probability and a fixed two-sided host spectral gap with probability tending to one. No quantitative rate for the exceptional host-gap event is required.

## 2. Objects and theorem

Let A be the adjacency of a uniform simple labelled cubic graph on n vertices, with n even. Let m predetermined distinct labels satisfy

\[
 m/n^{1/3}\longrightarrow c\in(0,\infty),\qquad
 s=\sqrt{m/n},\qquad \delta=m^{-1/2},\qquad
 r_n=\lfloor\log_2(1/s)\rfloor.
\tag{1}
\]

Thus `ms` tends to `c^(3/2)`, and `s delta=n^(-1/2)` exactly. Let E be the marked coordinate inclusion, e the unit constant marked vector, and G the marked projected resolvent at z=3 on the fixed host-gap event H. Write g=2/3. Quantities can be extended by zero off H when needed for probability statements.

Fix an integer k0 and a fixed integer `K>=max(0,k0)`. Put

\[
 \ell=r_n+k_0,\qquad R=r_n+K.
\]

These are positive for all sufficiently large n. Let V be the marked vertices that belong to a marked pair at distance exactly ell. Let P be the orthogonal projector in the marked coordinate space onto

\[
 \operatorname{span}\{e,\ e_a:a\in V\}.
\tag{2}
\]

Define the symmetric zero-diagonal short-distance matrix

\[
 (W_R)_{ab}=2^{-\operatorname{dist}(a,b)}
 \mathbf1_{\{\operatorname{dist}(a,b)\le R\}}
 \quad(a\ne b),
\]

and the scaled remainder

\[
 B_K=\frac{G-gI-gW_R}{s}.
\tag{3}
\]

**Theorem 1.** With `L=ceil(C_0 log n)` and a sufficiently large fixed C_0 depending on the host-gap choice,

\[
 \|B_K\|=O_{\mathbb P}(1),
\tag{4}
\]

\[
 \|P B_K P\|=O_{\mathbb P}(L^3/m),\qquad
 \|B_K P\|^2=O_{\mathbb P}(L^4/m).
\tag{5}
\]

The constants can depend on c, k0, K and the fixed gap. They are uniform in the fractional distance phase. In particular both quantities in (5) are `o_P(m^(-1/2))` and also `o_P(m^(-3/4))`.

Let V_R instead denote all endpoints of pairs at distance at most R. On the event `|V_R|<m`, let f be the unit constant vector on its complement, extended by zero on V_R. The same bounds (5) hold with P replaced by the orthogonal projector P_f onto

\[
 \operatorname{span}\{f,\ e_a:a\in V\}.
\tag{6}
\]

Off that event the projector can be assigned arbitrarily. Its exceptional probability tends to zero.

For the cubic resonance one takes k0=0 and phases approaching 1/2. The theorem does not require this phase restriction and controls both symmetric and antisymmetric coordinates of each selected pair.

## 3. Unconditional sampling and the nonnegative tail

Relabelling invariance exactly identifies the law of any invariant statistic of the predetermined marks with the law obtained by sampling an independent uniform m-subset S after the host. We use that representation throughout the proof. For any v fixed distinct vertices, its inclusion probability is

\[
 p_v=(m)_v/(n)_v\le C_v(m/n)^v.
\tag{7}
\]

No expectation below is conditioned on H or on the occurrence of a selected pair.

Let N_j count nonbacktracking incidence walks of length j. Put

\[
 U=\sum_{j=R+1}^L2^{-j}N_j,\qquad
 T=\operatorname{offdiag}(E_S^\top U E_S).
\tag{8}
\]

For large n, `R<=L`. The matrices U and T are symmetric and entrywise nonnegative. Every row sum of U equals `3(L-R)/2`, so

\[
 0\le U_{ab}\le C L,\qquad
 \sum_b U_{ab}\le C L.
\tag{9}
\]

The earlier two-walk estimate and Minkowski argument give directly under the simple host law

\[
 \mathbb E\|U\|_F^2\le C(n2^{-R}+L^4)=:C H_R.
\tag{10}
\]

The short marked graph at radius R is a matching with probability tending to one. Its edge count is tight for each fixed K. With probability tending to one every pair of distinct marked vertices has at most one nonbacktracking incidence walk of length at most R. These are the frozen critical pair-geometry statements. In particular `|V|=O_P(1)` and `|V_R|=O_P(1)`.

On H and this uniqueness event, the exact projected nonbacktracking series yields

\[
 G-gI-gW_R
 =gT+D_0-\frac{g(1+3L/2)}n(J-I)+E_0,
\tag{11}
\]

where `D_0=diag(G-gI)` and `||E_0||<=2n^(-4)`. The nonbacktracking tail can be chosen this small by fixing C_0 sufficiently large. No positivity assertion is made about D_0 or the whole remainder.

The earlier single-walk diagonal argument, retaining its finite estimate, gives

\[
 \|D_0\|=O_{\mathbb P}(mL^3/n+L/n+n^{-4}).
\tag{12}
\]

Since `ms` is bounded above and away from zero, (11) and (12) imply

\[
 B_K=gT/s+A_0,\qquad
 \|A_0\|=O_{\mathbb P}(L^3/m).
\tag{13}
\]

This is a decomposition on an event of probability tending to one, which suffices for every asserted probability rate. In particular its diagonal and stationary terms are already smaller than the resonance scale delta as operators on the entire marked space.

## 4. A tail estimate selected by a short pair

Let D_ell(a,b) be the indicator that two distinct host vertices have distance exactly ell. Its row sums are at most `3*2^(ell-1)`, hence at most `C 2^ell`. It also satisfies `D_ell(a,b)<=N_ell(a,b)`.

For j>R>=ell, the unequal-length two-walk estimate from the frozen pair-count proof gives

\[
 \mathbb E\sum_{a,b}N_\ell(a,b)N_j(a,b)
 \le C(\ell+j)^2 a_\ell a_j,
 \qquad a_t=3\,2^{t-1}.
\tag{14}
\]

The walks have different lengths, so there is no identical-sequence term. The estimate follows by exposing the two walks from the same root. Distinct endpoint-coincident walks require a pairing collision. The collision probability is at most `C(ell+j)^2/n`, which is multiplied by `n a_ell a_j`. Conditioning the nonnegative count on simplicity costs only a fixed factor. There is no conditioning on a graph distance event.

Multiply (14) by `2^(-j)` and sum j from R+1 to L. Since `2^(-j)a_j=3/2` and `ell<=L`, this proves

\[
 \mathbb E\sum_{a,b}D_\ell(a,b)U_{ab}
 \le C2^\ell L^3.
\tag{15}
\]

By (9), the same argument also gives

\[
 \mathbb E\sum_{a,b}D_\ell(a,b)U_{ab}^2
 \le C2^\ell L^4.
\tag{16}
\]

These inequalities are the essential way to select the rare resonant pair without dividing by its small occurrence probability.

## 5. Collective-vector bounds

Using (7), (9) and (10),

\[
 \mathbb E(e^\top T e)
 =\frac{p_2}{m}\mathbb E\sum_{a\ne b}U_{ab}
 \le C\frac{mL}{n}.
\tag{17}
\]

To bound the column norm, expand the square of each row sum. Terms using the same second endpoint require two marked vertices. Terms using two different second endpoints require three. Thus

\[
 \begin{split}
 \mathbb E\|Te\|^2
 &\le\frac{p_2}{m}\mathbb E\sum_{a\ne b}U_{ab}^2
 +\frac{p_3}{m}\mathbb E\sum_a\left(\sum_b U_{ab}\right)^2\\
 &\le C\left[\frac{m}{n^2}H_R+\frac{m^2L^2}{n^2}\right].
 \end{split}
\tag{18}
\]

The diagonal deletion in T can only reduce the nonnegative upper sums. After division by s or s squared, respectively, these become

\[
 e^\top(T/s)e=O_{\mathbb P}(L/m),
\tag{19}
\]

\[
 \|Te/s\|^2
 =O_{\mathbb P}\left(2^{-R}+L^4/n+mL^2/n\right)
 =O_{\mathbb P}(1/m).
\tag{20}
\]

The last equality uses fixed K and logarithmic L.

## 6. Pair-selected columns and compressed entries

Let P_V denote the coordinate projector onto V. A selected endpoint a has at least one marked partner t with `D_ell(a,t)=1`. Replacing its indicator by the sum over those possible partners only increases any nonnegative expression.

First consider `||P_V T e||`. Because its entries are nonnegative, the norm is at most their sum. If the row endpoint a and column endpoint b form the selected pair, two vertices must be marked, and (15) applies. Otherwise choose a selected partner t distinct from a and b, so three vertices must be marked. Its distance indicator has row sum at most `C2^ell`, while U has row sum at most CL. Therefore

\[
 \begin{split}
 \mathbb E\|P_VTe\|
 &\le\frac C{\sqrt m}
 \left[p_2 2^\ell L^3+p_3 n2^\ell L\right]\\
 &\le C\frac{2^\ell}{n^2\sqrt m}
       (m^2L^3+m^3L).
 \end{split}
\tag{21}
\]

This inequality does not require the marked short graph to be a matching.

Next bound all selected column norms together. Terms in which b is the selected partner of a are bounded by (16) and p_2. For three distinct marked vertices a,t,b, sum over t using its deterministic distance degree and then use (10). This gives

\[
 \begin{split}
 \mathbb E\|T P_V\|_F^2
 &\le C\left[p_2 2^\ell L^4+p_3 2^\ell H_R\right]\\
 &\le C\left[\frac{m^2 2^\ell L^4}{n^2}
       +\frac{m^3 2^\ell H_R}{n^3}\right].
 \end{split}
\tag{22}
\]

Again no matching assumption is needed.

Finally consider `P_VTP_V`. Let M_R be the event that the short marked graph at radius R is a matching. On M_R, every selected vertex has one selected partner. For a,b in V, either b is that partner of a, or their two selected pairs have four distinct endpoints a,t,b,v. The first case uses (15). In the second case the number of choices for t and v, for fixed a,b, is at most `C2^(2ell)`. Summing U over a,b gives at most CnL by (9). Consequently

\[
 \begin{split}
 &\mathbb E\left[\mathbf1_{M_R}
       \sum_{a,b\in V}T_{ab}\right]\\
 &\qquad\le C\left[p_2 2^\ell L^3+p_4 n2^{2\ell}L\right]\\
 &\qquad\le C\left[\frac{m^2 2^\ell L^3}{n^2}
       +\frac{m^4 2^{2\ell}L}{n^3}\right].
 \end{split}
\tag{23}
\]

For a nonnegative matrix its operator norm is at most the sum of its entries. Since `Pr(M_R^c)` tends to zero, (23) therefore controls `||P_VTP_V||` in probability.

At criticality, `2^ell=Theta(m)`, `2^(-R)=Theta(1/m)`, `n=Theta(m^3)` and `s=Theta(1/m)`, with constants uniform in the phase. Equations (21) through (23) imply

\[
 \|P_VTe/s\|
 =O_{\mathbb P}(m^{-3/2}L+m^{-5/2}L^3),
\tag{24}
\]

\[
 \|T P_V/s\|_F^2=O_{\mathbb P}(L^4/m),
\tag{25}
\]

\[
 \|P_VTP_V/s\|=O_{\mathbb P}(L^3/m^2).
\tag{26}
\]

All mark-selection dependences have been included through exact two-, three- or four-vertex inclusion probabilities. In particular, none of these formulas assumes that the selected endpoints are uniform after conditioning on a rare short pair.

## 7. Proof of the projector estimates

Let F be the matrix whose columns are e followed by the distinct coordinate vectors at V. On an event of probability tending to one, `|V|<m/4`. Its Gram matrix has smallest eigenvalue at least

\[
 1-\sqrt{|V|/m}\ge1/2.
\]

Thus F has full column rank and the orthogonal projector onto its range is `F(F^top F)^(-1)F^top`. Bounds for `F^top B_K F` and `B_K F` transfer to the corresponding projector bounds by fixed numerical constants.

For the T part, (19), (24) and (26) control every block of `F^top(T/s)F`. Its operator norm is `O_P(L/m)`. Equations (20) and (25) give

\[
 \|(T/s)F\|^2
 \le \|Te/s\|^2+\|TP_V/s\|_F^2
 =O_{\mathbb P}(L^4/m).
\tag{27}
\]

The auxiliary term A_0 from (13) has operator norm `O_P(L^3/m)`. Its squared column contribution is at most a constant times `L^6/m^2`, which is smaller than `L^4/m`. This proves (5).

For (4), direct marked-subset sampling and (10) give

\[
 \mathbb E\|T/s\|_F^2
 \le C\frac{m}{n}H_R
 =C(m2^{-R}+mL^4/n)=O(1).
\tag{28}
\]

Together with (13), this proves `||B_K||=O_P(1)` without requiring a global error that tends to zero.

For the f variant, tightness of `|V_R|` gives

\[
 \|f-e\|=O_{\mathbb P}(m^{-1/2}).
\tag{29}
\]

The collective-column bound already proved gives `||B_K e||=O_P(L^2/sqrt(m))`, and (5) gives the same bound for `||B_K P_V||`. Replacing e by f changes each compressed block by at most `O_P(L^2/m+1/m)`, using (4) and (29). It changes the squared column bound by at most `O_P(1/m)`. Since f is exactly orthogonal to the selected coordinate vectors, the resulting columns form an orthonormal family. This proves (5) with P_f and completes Theorem 1.

## 8. Derivative and retained-matrix consequences

The previous all-orders marked-resolvent estimate, applied with j=1, gives

\[
 \|G'(3)-g_3'(3)I\|
 =O_{\mathbb P}\left(\frac{mL^4+m^2L^2}{n}
                  +Ln^{-4}\right)
 =O_{\mathbb P}(L^4/m),
\tag{30}
\]

where `g_3'(3)=-10/9`. No subcritical restriction was used in the finite bound, so this substitution at criticality is valid. The earlier critical norm bound is `||G-gI||=O_P(s)`.

For the cubic pole-free Schur block F, the exact derivative formula is

\[
 F'(3)=2I-6G-9G'(3)-J/n.
\]

The scalar identity `2-6g-9g_3'(3)=8` and (30) imply

\[
 \|F'(3)/8-I\|=O_{\mathbb P}(L^4/m).
\tag{31}
\]

The uniform local second derivative remains bounded on H. Thus the analytic assumptions needed for a separate transfer at accuracy `o_P(delta)` hold, and the displayed rates are also `o_P(m^(-3/4))`.

More concretely, let T_n be the retained matrix from the frozen effective theorem and S_(n,K) its undecoupled short-pair comparison. On the event of no edge between marked vertices, their bottom-right difference is exactly

\[
 (T_n-S_{n,K})_{\rm marked}
 =\frac98 B_K+\frac{3}{4ns}J.
\tag{32}
\]

The event has probability tending to one because its complementary probability is at most `C m^2/n`. The last term in (32) has operator norm `3s/4=O(1/m)`. Extend P or P_f by including the host coordinate. The conclusions (4) and (5) hold for this actual retained-matrix error as well.

This proof does not assert that a global fixed-K operator error tends to zero. For a complementary spectral-gap argument one uses the separately proved bound `limsup Pr(||T_n-S_(n,K)||>eta)<=C eta^(-2)2^(-K)`, takes n to infinity with K fixed, and then sends K to infinity. The selected-sector rates here remain a fixed-K statement. They can be combined with that order of limits without silently introducing a growing-cutoff assumption.

## 9. What the negative finer scale still requires

The estimates in (5) and (31) resolve errors relative to delta and also relative to `m^(-3/4)`. They do not resolve errors at order `1/m`. In particular, a finite normal form accurate only to `o_P(delta)` cannot select individual vectors inside a negative cluster whose splittings are smaller than delta.

There is a deterministic tree correction that explains why the unrenormalized finite star is insufficient at the finer scale. For the cubic tree, put

\[
 t(z)=\frac{z-\sqrt{z^2-8}}4,\qquad
 g_3(z)=\frac{t(z)}{1-t(z)^2}.
\]

The resolvent entry between vertices at distance ell is `g_3(z)t(z)^ell`. This follows by the tree recursion and the decaying solution of `2t^2-zt+1=0`. Its contribution to the scaled pair coupling in the cubic Schur equation is

\[
 w_\ell(z)=\frac{z^2g_3(z)t(z)^\ell}{8s}.
\tag{33}
\]

At z=3 one has `t=1/2`, `t'/t=-1`, `g_3=2/3`, and `g_3'/g_3=-5/3`. Therefore

\[
 \frac{w_\ell'(3)}{w_\ell(3)}
 =\frac23-\frac53-\ell=-(\ell+1).
\tag{34}
\]

For bounded real x and `ell=O(log n)`, Taylor expansion on a fixed compact interval inside `z>2sqrt(2)` gives, uniformly in x,

\[
 w_\ell(3+sx)
 =w_\ell(3)\left[1-(\ell+1)sx
                 +O(\ell^2s^2)\right].
\tag{35}
\]

The remainder bound follows by differentiating the logarithm twice. Its first derivative is O(ell), its second derivative is O(ell), and `ell s` tends to zero. At a pair amplitude bounded above and away from zero, the correction has order `s ell`, which is of order `(log n)/m`. This is smaller than delta and `m^(-3/4)`, but larger than `1/m`.

Equation (35) is an exact tree-model calculation. It is not a claim that the full finite-graph correction equals this term with a proved `o_P(1/m)` remainder. A negative basis law at that precision would need the energy-dependent selected resolvent, the collective centering and the effect of other pair levels to be expanded together. Those obligations are not discharged by this proof.

## 10. Handoff

The proved result is the selected-sector estimate (5), its free-vector variant, the derivative rate (31), and the actual retained-matrix interface (32). These support a separate positive resonance theorem and a test of negative basis nonuniqueness using detunings larger than `L^4/m`. They do not by themselves establish either graph eigenvector conclusion.

Requested review: reconstruct the pair-selected expectation bounds (15), (21), (22), and (23), check the exact subset probabilities and matching use, verify the projector Gram estimate, and retain the distinction between the proved graph error rates and the exact tree-only correction in (35). No canonical status or prior frozen file has been edited.
