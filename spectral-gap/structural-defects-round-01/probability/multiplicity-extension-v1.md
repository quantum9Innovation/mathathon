# All finite resonant multiplicities in the critical negative reduction

November 15, 2026. Owner: probability workstream. Revision 1, frozen for separate review.

## 1. Statement and prior exposure

Use the critical cubic model, s=sqrt(m/n), kappa=3/sqrt(8), r=floor(log_2(1/s)), w=(3/4)2^(-r)/s, theta=c^(3/2), and the finer tuning

\[
 \beta_n=\frac{w-\kappa+(\kappa^2/2)sr}{s}\longrightarrow\beta.
\tag{1}
\]

Let p_n=Z_(n,0) be the number of marked pairs at distance r. Its limit is Poisson with mean

\[
 \lambda_0=\frac{3\theta}{4\sqrt2}=\frac{\kappa\theta}{2}.
\]

For each fixed p>=0, condition only in the final statements on p_n=p. Its probability tends to the strictly positive number exp(-lambda_0)lambda_0^p/p!.

The previously frozen inputs are:

- collective-limit-v1.md, SHA256 e492d3dfa506167ba28782e316129146e72f8046e96bbaf50b265e42d3fc307d.
- signed-coupling-v1.md, SHA256 68660a0914a02b0a6bf53f2ccef75a2b844859e9dafc7f8a9e106db3921d5fba.
- collective-self-energy-v1.md, SHA256 a3c6b1b42bed9f7f3c7c5d45c1292df5a207951e709e318db24f6f711c9d9d4d.
- density-and-tuning-v1.md, SHA256 cf3e7ef384fad52dd78f22fbdb2d121a8c99049f4736012c4a7dfeae14a91098.

This workstream authored those proofs and the earlier probability inputs. The integrator requested the fixed-p extension and proposed the moment identities checked below. No live root or structural proof was read. This file preserves the one-pair proofs and verifies the multiplicity changes explicitly.

On the matching event let V contain the 2p endpoints of the distance-r pairs. Let A_V be their matching adjacency in marked coordinates. Let f_p be the unit constant vector outside V, zero on V. For pair j choose either endpoint ordering and define

\[
 a_j^-=(e_{u_j}-e_{v_j})/\sqrt2,\qquad
 c_-=(h-f_p)/\sqrt2.
\tag{2}
\]

Let U_p be the isometry with columns c_-,a_1^-,...,a_p^-. For p=0 it has only its collective column. Write P_p=U_pU_p^top and Q_p=I-P_p.

Let mathcal T_n(x) be the exact energy-dependent graph pencil from signed-coupling-v1.md and put

\[
 x_n^0=-\kappa-\frac{\kappa^2}{2}sr.
\]

Its exact Schur matrix on this reference space is

\[
 \mathcal B_{n,p}(x)=
 U_p^\top\mathcal T_n(x)U_p+
 U_p^\top\mathcal T_n(x)Q_p
 (xI-Q_p\mathcal T_n(x)Q_p)^{-1}
 Q_p\mathcal T_n(x)U_p.
\tag{3}
\]

The complementary inverse has a fixed norm bound with conditional probability tending to one, uniformly for |x-x_n^0|<=Ms, for every fixed M. Use arbitrary extensions on the exceptional event.

**Theorem 1.** For every fixed p>=0, conditional on p_n=p, there is a tight scalar L_(n,p) such that, uniformly for |x-x_n^0|<=Ms,

\[
 \mathcal B_{n,p}(x)
 =x_n^0 I+
 s\begin{pmatrix}
   L_{n,p}&0\\
   0&(33/16-\beta_n)I_p
  \end{pmatrix}
 +o_{\mathbb P}(s)
\tag{4}
\]

in operator norm. For p=0 the lower block is absent. The limit is

\[
 L_{n,p}\xrightarrow{\mathrm d}L_p,
\tag{5}
\]

where, with independent Poisson counts at all other offsets and P_0=p,

\[
 L_p=\frac{51}{32}
 +\frac1\theta\left[
  \sum_{k\le0}J(w_k)P_k+
  \sum_{k\ge1}\bigl(J(w_k)P_k-w_k\lambda_k\bigr)
 \right],
\tag{6}
\]

\[
 w_k=\kappa2^{-k},\qquad
 \lambda_k=\lambda_0 2^k,\qquad
 J(w)=\frac{\kappa w}{\kappa+w}.
\]

Convergence holds jointly with every fixed finite collection of pair counts. The scalar L_p has a bounded smooth density. Its mean and variance are

\[
 \mathbb E L_p=\frac{51}{32}+\frac{\kappa p}{2\theta},
\tag{7}
\]

\[
 \operatorname{Var}(L_p)=
 \frac{\kappa^3}{\theta}
 \sum_{k\ge1}\frac{2^k}{(1+2^k)^2}.
\tag{8}
\]

For p>=1, L_p differs almost surely from 33/16-beta, and each of the two possible orderings has positive probability. No basis inside the rank-p pair space is selected by (4).

These are statements about the exact graph-derived Schur reduction and its coefficient law. The actual graph root and physical mass synthesis remains a separate application. The moment formulas concern the limiting scalar, not convergence of finite-n moments.

## 2. Conditional probabilities and selected bounds

The estimates used in the one-pair argument were initially proved for V equal to all endpoints of distance-r pairs, with its cardinality tight. They were not obtained by conditioning on a specified rare pair. In particular, their raw bounds imply

\[
 \|(Z-wA_V)P_V\|^2=o_{\mathbb P}(1/m),
\tag{9}
\]

\[
 P_V ZP_V=wA_V+o_{\mathbb P}(s),
 \qquad P_VZe=wP_Ve+o_{\mathbb P}(s),
\tag{10}
\]

\[
 P_V\Gamma P_V=s(r+1)wA_V+o_{\mathbb P}(s),
 \qquad P_V\Gamma e=o_{\mathbb P}(s).
\tag{11}
\]

Here Z=-F(3)/(8s), Gamma has host coordinate zero and marked block F'(3)/8-I, and P_V is the coordinate projector onto V. The o(s) selected constant error follows from the bound O_P(log cubed(n)/n) for G before division by s. The derivative error follows from O_P(log^4(n)/n).

For clarity, the vanishing coefficient in (9) comes from the three-distinct-endpoint estimate at every fixed cutoff R=r+K. After multiplication by m, its limiting upper probability is at most C eta^(-1)2^(-K). The selected residual in (9) does not depend on K, so K is then sent to infinity. The own-partner entries are controlled by squaring their total O_P(log cubed(n)/n). Neither the count of selected pairs nor a choice of their ordering creates a growing dimension in these estimates.

The collective bounds are

\[
 \|Ze\|=O_{\mathbb P}(m^{-1/2}),\qquad
 \|Z\|=O_{\mathbb P}(1),\qquad
 e^\top\Gamma e=O_{\mathbb P}(s^2\log^2 n),
\tag{12}
\]

and globally ||Gamma||=O_P(s log squared(n)).

Every fixed-p conditional conclusion follows by restricting these unconditional probability bounds and dividing by Pr(p_n=p), which stays bounded away from zero for that fixed p. For p in any fixed finite set, the constants can be chosen uniformly, since that set has a positive minimum limiting conditioning probability. No estimate has been reinterpreted as an expectation conditioned on a specified local pairing.

The short-matching event at any fixed cutoff has conditional probability tending to one by the same division. Thus all p selected pairs are disjoint with high conditional probability.

## 3. Direct compression for p selected pairs

Put

\[
 v=\sum_{u\in V}e_u,\qquad \delta=m^{-1/2}.
\]

For fixed p, ||v||=sqrt(2p), and the exact free-vector relation is

\[
 f_p=\frac{e-\delta v}{\sqrt{1-2p/m}}.
\tag{13}
\]

The matching adjacency satisfies A_Vv=v and A_Va_j^-=-a_j^-. Every a_j^- is orthogonal to both e and v.

Equations (10) and (13) give

\[
 v^\top Ze=2p w\delta+o_{\mathbb P}(s),
 \qquad v^\top Zv=2p w+o_{\mathbb P}(s).
\]

Since e^top Ze=O_P(sr), expansion of the denominator in (13) yields

\[
 f_p^\top Zf_p=e^\top Ze-\frac{2pw}{m}+o_{\mathbb P}(s).
\tag{14}
\]

The host-star term is

\[
 -\kappa e^\top f_p
 =-\kappa\sqrt{1-2p/m}
 =-\kappa+\frac{\kappa p}{m}+o(s).
\]

Consequently the collective compression of T is

\[
 c_-^\top T c_-
 =-\kappa+\tfrac12e^\top Ze
        +\frac{p(\kappa-w)}m+o_{\mathbb P}(s)
 =-\kappa+\tfrac12e^\top Ze+o_{\mathbb P}(s).
\tag{15}
\]

The cancellation in (15) is the multiplicity-sensitive step. It uses p fixed and w-kappa=O(sr), so p(kappa-w)/m=o(s). For p=0 it is immediate.

The selected antisymmetric compression of T is -w I_p+o_P(s). Equations (10) and (13) show that its direct mixed row with c_- is o_P(s): both leading contractions with e and v vanish against every a_j^-. Because p is fixed, entrywise bounds on this finite row and block imply the same operator bound. Equivalently one can use the operator statements in (10) directly.

Replacing e by f_p in the Gamma quadratics costs at most
O_P(s log squared(n)/sqrt(m))=o_P(s). Equations (11)-(13) therefore give

\[
 c_-^\top\Gamma c_-=o_{\mathbb P}(s),
 \qquad
 (a_i^-)^\top\Gamma a_j^-
 =-s(r+1)w\,\mathbf1_{\{i=j\}}+o_{\mathbb P}(s),
\tag{16}
\]

and the entire mixed Gamma row is o_P(s).

The exact energy-dependent expansion remains

\[
 \mathcal T_n(x)
 =T-x\Gamma+\frac{17}{6}s x^2P_M+o_{\mathbb P}(s)
\tag{17}
\]

uniformly for bounded x. Its derivation uses F''(3)->(-136/3)I and does not depend on p. The marked-coordinate projector P_M has compression 1/2 on c_-, identity on the antisymmetric block, and zero mixed row.

Substitution of (15)-(17) gives the direct compression

\[
 U_p^\top\mathcal T_n(x)U_p
 =x_n^0I+
 s\begin{pmatrix}
   (\kappa^2/2)C_n+63/32&0\\
   0&(33/16-\beta_n)I_p
  \end{pmatrix}
 +o_{\mathbb P}(s).
\tag{18}
\]

All constants are unchanged. The collective p-dependent finite-star correction has cancelled in (15), and its later contribution is retained through the pair process and complementary correction.

## 4. Complementary columns and the exact Schur matrix

The selected residual norm in (9), together with the exact antisymmetric host cancellation, implies

\[
 \|Q_p\mathcal T_n(x)(a_1^-,\ldots,a_p^-)\|
 =o_{\mathbb P}(\sqrt s).
\tag{19}
\]

For fixed p this can be bounded either by the operator norm on the selected coordinate space or by its Frobenius norm. The analytic correction in (17) has norm O_P(s log squared(n))=o_P(sqrt(s)), so it preserves the rate.

For the collective column, (12)-(13) and the finite host star give

\[
 \|Q_p\mathcal T_n(x)c_-\|=O_{\mathbb P}(\sqrt s).
\tag{20}
\]

These statements include p=0, where only (20) is needed.

The complementary-gap proof removes all p selected antisymmetric vectors and the one collective negative vector. In the finite matching model, every other negative pair level is a fixed distance from -kappa, and the positive levels and zero are also separated. The free collective vector differs from c_- by O_P(m^(-1/2)) for every fixed short cutoff. The full-operator tail failure bound is C2^(-K), so taking n first and then K gives the actual fixed gap. This argument works for every fixed p and does not leave any selected negative vector in the complement.

Using the fixed inverse bound in (3), the induced pair block has norm o_P(s) by (19). The induced mixed row is o_P(s) by (19)-(20). Only the collective entry is O_P(s). The derivative argument in signed-coupling-v1.md uses the same column bounds and proves uniform o_P(s) variation on |x-x_n^0|<=Ms. It has no additional dimension factor for fixed p.

This establishes the form (4), with the remaining scalar determined by the collective complementary entry.

## 5. Collective complementary correction with p positive channels

Fix a short cutoff. Suppose its matching has p selected resonant pairs of weight w tending to kappa and ell other pairs with weights v_1,...,v_ell. Work on fixed bounds for the counts and weights, and with the nonresonant gap bounded below.

Let u be the unit constant vector outside all retained pairs. Let t_1,...,t_p be the selected symmetric pair vectors and let q_1,...,q_ell be the other symmetric pair vectors. The exact finite symmetric-sector matrix has free-star coefficient
kappa sqrt(1-2(p+ell)/m), host-to-each-pair coefficient kappa sqrt(2/m), and the indicated pair diagonals.

With c_0=(h-u)/sqrt(2), the collective vector excluding only the selected endpoints satisfies

\[
 c_-=c_0-\delta\sum_{j=1}^{\ell}q_j+O(\delta^2).
\]

The leading projected coupling is therefore

\[
 \delta^{-1}Q_p S_Kc_-
 =\kappa\sum_{i=1}^{p}t_i
       -\sum_{j=1}^{\ell}v_j q_j+O(\delta).
\tag{21}
\]

All p selected positive channels remain in the complement. Only their antisymmetric partners were removed. The limiting complementary inverse is diagonal on these symmetric channels, with denominators -kappa-w or -kappa-v_j. Hence

\[
 m\Sigma_{n,K}^{S}
 =-\frac{p\kappa^2}{\kappa+w}
       -\sum_{j=1}^{\ell}\frac{v_j^2}{\kappa+v_j}+o(1).
\tag{22}
\]

Replacing p kappa squared by p w squared in the first term costs o(1). For p=0 that term is absent. This verifies the multiplicity change in the finite-arrow calculation explicitly.

The collective tail-column estimate still retains the factor 2^(-K) after dividing its squared norm by s. The formula for f_p-e in (13), the selected residual (9), and p fixed show that replacing e by f_p preserves that bound. The global cutoff comparison and the resolvent identity therefore prove convergence of the actual collective correction to

\[
 -\frac1\theta\sum_{k\in\mathbb Z}
       \frac{w_k^2}{\kappa+w_k}P_k,
\tag{23}
\]

jointly with C_n and finite counts, conditional on P_0=p. The left tail is discarded by its rare-pair probability. The weak right tail has expectation O(2^(-K)). These bounds are uniform for p in a fixed finite set.

Combining (23) with the collective entry in (18) gives (6), with the same constant 51/32 and the same bounded jump kernel. This proves (4)-(6).

## 6. Density, noncoincidence and moments

For fixed p, the scalar differs from the p=0 scalar by the deterministic translation

\[
 L_p=L_0+\frac{\kappa p}{2\theta}
\tag{24}
\]

when all other Poisson coordinates are coupled identically. The positive-offset independent coordinates are unchanged. The Fourier proof from density-and-tuning-v1.md therefore gives the same exponential decay and a bounded smooth density for every fixed p. Its proof of unbounded support in both directions also persists under translation.

For p>=1, the pair coefficient is deterministic, so its coincidence probability with L_p is zero. Both relative orderings have positive probability. For p=0 there is no pair block to compare.

The moment identities can be checked without subtracting divergent expectations. The negative-offset means and the positive deterministic drift in (6) are both absolutely summable. For j>=1,

\[
 \lambda_{-j}J(w_{-j})
 =\frac{\lambda_0\kappa}{1+2^j},
\]

while

\[
 \lambda_j(J(w_j)-w_j)
 =-\frac{\lambda_0\kappa}{1+2^j}.
\tag{25}
\]

They cancel in pairs. The fixed k=0 contribution is J(kappa)p/theta=kappa p/(2theta). This proves (7).

Since P_0 is fixed, its contribution has no variance. Independence at other offsets gives

\[
 \operatorname{Var}(L_p)
 =\frac1{\theta^2}
    \sum_{k\ne0}\lambda_k J(w_k)^2.
\]

The contributions at j and -j are equal, each equal to
lambda_0 kappa squared times 2^j/(1+2^j) squared before division by theta squared. Since lambda_0=kappa theta/2, this is exactly (8). The series is finite.

For completeness, mixing over an independent Poisson P_0 with its original mean gives the unconditional limiting mean 15/8 and adds kappa cubed/(8theta) to the conditional variance. These are moments of the limiting mixture. No finite-n moment convergence is claimed.

## 7. Random multiplicity and scope

All statements have been proved for every fixed p, with estimates uniform over each finite set 0<=p<=P. The sequence p_n is tight and converges to its Poisson law. Thus one may combine the conditional results into an unconditional mixture by first restricting to 0<=p_n<=P, summing the finitely many conditional convergence statements, and then sending P to infinity. This avoids treating a tight random dimension as a fixed deterministic one without justification.

The retained order-s law has one random collective scalar and a repeated deterministic pair block. It does not select individual vectors within the rank-p pair block. A separate graph synthesis can transfer the separated collective line and the grouped pair space, since the limiting scalar almost surely differs from the pair coefficient. When p=0 only the collective line remains.

The integer construction in density-and-tuning-v1.md is independent of p and realizes every finite beta at the fixed c. Conditioning on p does not alter that deterministic tuning.

Requested review: check the cancellation in (14)-(15), removal of all selected negative modes from the complementary resolvent, the p selected positive channels in (21)-(22), the conditional probability bounds, and the paired mean and variance calculations.
