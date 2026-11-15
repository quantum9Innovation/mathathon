# Graph resonance application review

November 15, 2026. Review revision 1. Scope: the graph application, normalization, spectral-subspace reduction, physical scales and masses, and integer tuning.

## 1. Reviewed revisions and exposure

Initial target:

- `root/graph-resonance-v1.md`, SHA256 `d7e03a19f52d7e35bc934471b731d8541af4bc9acd796d0ee0464c9fbb9aad86`.

Final target accepted by this review:

- `root/graph-resonance-v2.md`, SHA256 `907d90af7ea1af8a59ec49c100869046e01e3ffd251e81a55239a054bb59f289`.

Read dependencies at their checked hashes:

- `root/subspaces-v1.md`, SHA256 `f13fbd47ba04bd638f4bafe940c20d604bfa4a4653df553b4b737f2e3779e87a`.
- `resonance/finite-normal-form-v1.md`, SHA256 `59bebac4b6a96d148d48830bf27130223d6820e53e16627720fb7f2f7216eed7`.
- `probability/refined-resolvent-v1.md`, SHA256 `bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df`.
- `probability/negative-log-scale-v1.md`, SHA256 `faced6a02d91d451e4ef0e0989d3d46811da66d809d40e9344e9444012901409`.

I authored the two probability premises, discussed the normalization strategy, and received the proposed logarithmic coefficients before deriving those probability statements. This is a separate review of the synthesis and its actual-graph bridge, not an independent review of my own probability proofs and not a claim of blind discovery. The graph synthesis and subspace proof were read at their frozen revisions for this application audit. Other reviewers are responsible for an independent reconstruction of the probability premises.

## 2. Decision and resolved finding

Accepted for the stated paper scope at final target revision 2, conditional on its explicitly named probability and subspace inputs. No unresolved application gap was found.

Finding CS-I1 concerned the literal statements of equations (17) and (18) in revision 1. Each omitted the additive plus sign before its `O_P(1/m)` remainder. The intended additive expansion was clear from the surrounding argument, but the displayed equation did not express it. This finding was sent to the integrator before acceptance.

I checked the complete revision delta. Revision 2 changes only its revision paragraph and inserts those two plus signs. The mathematical statements, coefficients and proof steps are otherwise identical. CS-I1 is resolved at the exact revision-2 hash above. Revision 1 is preserved.

## 3. Actual cluster normalization

The physical lift is the graph-defined map

\[
 J(a,v)=(a u+RBv/\sqrt8,\ v/\sqrt8).
\]

With `H=mathcal A-3I`, direct block multiplication gives the identities used by the source:

\[
 J^\top J=I+\Gamma,\qquad HJ=sVT,\qquad J^\top HJ=sT,
\]

where `V(a,v)=(a u,sqrt(8)v)` and the host coordinate of Gamma is zero. In particular, the response term RB is perpendicular to u, so there is no omitted Gram cross term.

Let P be the full near-3 graph-cluster projection. The fixed complementary host gap and `HJ=sVT` imply `||(I-P)J||=O_P(s)`. Consequently

\[
 M=J^\top P J=I+\Gamma+O_P(s^2).
\]

Since `||Gamma||=o_P(1)`, scalar functional calculus for the self-adjoint M near the identity gives

\[
 M^{-1/2}=I-\Gamma/2+O_P(\|\Gamma\|^2+s^2).
\]

This expansion does not require Gamma to commute with T. The source correctly retains both products in their original order.

Commutation of P with H gives

\[
 J^\top P H P J/s
 =T-J^\top(I-P)H(I-P)J/s=T+O_P(s).
\]

The error estimate follows from `||(I-P)J||=O_P(s)` and `||(I-P)HJ||=O_P(s)`. Inserting M to form the actual graph isometry U yields

\[
 A_{\rm eff}=T-\tfrac12(\Gamma T+T\Gamma)
             +O_P(\|\Gamma\|^2+s).
\]

The retained norm `||T||=O_P(1)` is enough here. No moment convergence or deterministic bound on its random maximum is required. The derivative rate `||Gamma||=O_P(s log^2 n)` gives

\[
 (\|\Gamma\|^2+s)/(sr)
 =O_P(s\log^4(n)/r+1/r)\longrightarrow0.
\]

Thus Section 7 supplies the precise actual-graph bridge left open by the logarithmic probability proof. It is an operator statement on the full cluster, rather than an inference from eigenvalue agreement alone.

## 4. The isolated-subspace lemma

The finite lemma in Section 5 is dimension independent. The block-diagonal reference has spectral distance at least a constant times g from the circle of radius g/2 about the target level. A sufficiently small off-diagonal norm b preserves that contour gap. Integrating the resolvent identity gives `||P_0-Q||<=C b/g`, and a projection difference less than one gives rank equality.

The canonical polar isometry satisfies

\[
 QW=(QP_0Q)^{1/2},\qquad
 \|I-QP_0Q\|=\|(I-P_0)Q\|^2.
\]

Therefore its within-Q displacement is quadratic in b, although its perpendicular displacement is linear. Expanding its compression yields the stated `O((g^(-1)+||A_0||g^(-2))b^2)` error. The mixed terms contain one original off-diagonal block and one perpendicular displacement, so they are also quadratic. This verifies why the squared selected-column error is the relevant hypothesis for the finer effective operator.

The application obtains the complementary gap by fixing a distance cutoff, using the exact matching model, and then increasing that cutoff in the limiting failure bound. The actual reference space depends only on the distance-r pairs, so it does not change with the auxiliary cutoff. No result for a growing cutoff is assumed.

For the logarithmic step, replacing the corrected retained matrix by A_eff adds `o_P(sr)` to the compressed block. Its squared additional column norm is also `o_P(sr)`. The original complementary coupling has square `O_P(1/m)=o_P(sr)`, so the finite lemma applies at that finer scale. Rank and separated-group projector conclusions follow as stated.

## 5. Positive and negative finite reductions

For the positive reference vector `c_+=(h+f)/sqrt(2)`, its coupling to one symmetric pair vector is exactly `kappa/sqrt(m)`. The factor sqrt(2) from the pair is cancelled by the collective host amplitude `1/sqrt(2)`. The p-dimensional bright sum therefore has coefficient `kappa sqrt(p)` after division by `delta=m^(-1/2)`.

The retained collective diagonal differs from kappa by `O_P(1/m)`. Other finitely many retained pairs contribute only this order to its compressed diagonal. Their complementary couplings have order `m^(-1/2)`, so their eliminated correction is again order `1/m`. Together with the selected probability bounds and the graph isometry estimate, this proves the positive effective matrix to error `o_P(delta)`.

For p>=1 its two bright roots are distinct and separated from the dark value tau by positive constants in delta units. Thus the two actual graph branches have rank one with probability tending to one. The dark statement is correctly made for a grouped subspace. For p=0 only the collective branch remains.

The negative pair vectors are antisymmetric, so their host-star couplings vanish exactly. The negative compression at scale delta is therefore diagonal, as in equation (9). At logarithmic precision the source uses the full corrected operator, including both the collective quadratic drift and the selected derivative metric. It does not transfer the isolated finite-star coefficient at scale `1/m`.

At `a!=-kappa^2/2`, the two logarithmic coefficients are separated. This identifies one collective line and the whole p-dimensional pair subspace. At the equality value, the source correctly retains only the combined negative space and leaves its finer basis unresolved.

## 6. Physical scales and mass conversion

The first physical scale is exact:

\[
 s\delta=\sqrt{m/n}/\sqrt m=n^{-1/2}.
\]

Thus multiplying the positive or same-scale negative displacement by `sqrt(n)` gives the displayed coefficients. The logarithmic retained displacement is sr, so its graph adjacency displacement is `s^2r`, of order `n^(-2/3)log n`.

If A is the squared coefficient of a retained collective coordinate c_sigma in a unit resonant vector, its retained host coordinate has squared mass A/2. The remaining retained marked norm is `1-A/2`. The exact lift and its approximation by the isometry give the graph masses

\[
 (A/2,\ (1-A/2)/8,\ 7(1-A/2)/8).
\]

This verifies equation (6) and the exact-resonance bright values `(1/4,3/32,21/32)`. Setting A=1 gives the pure collective triple `(1/2,1/16,7/16)`, while A=0 gives `(0,1/8,7/8)`. The operator form of the mass estimate makes the pair-subspace conclusions uniform over its unit sphere, including arbitrary combinations inside a repeated group.

The physical lift includes the host response RB. Treating retained added coordinates as the whole graph vector would give different and incorrect masses, but the reviewed source does not make that substitution.

## 7. Integer tuning and actual nonuniqueness

The finite positive tuning construction has bounded rounding errors in n and m, while `n=Theta(m^3)`. Its relative n error vanishes even after multiplication by `sqrt(m)`. The phase remains in the interior neighborhood of 1/2, so its floor is exactly the prescribed integer j for all sufficiently large j. This realizes every finite tau while retaining the same first-order phase limit and critical c.

For the logarithmic construction in equation (21), write

\[
 b_j=a j s_0/\kappa.
\]

Then `b_j->0`, and before rounding,

\[
 s=s_0/(1+b_j),\qquad
 w-\kappa=a j s_0.
\]

Nearest-even rounding contributes relative error `O(1/n)`, negligible after division by sr. Hence r=j eventually and

\[
 (w-\kappa)/(sr)\longrightarrow a.
\]

Also `m/n^(1/3)->c` and `sqrt(m)(w-kappa)->0`. At a=0 the proposed n is already the even integer `2m4^j`, so exact phase holds at every size in that sequence.

Conditional on p=1, a=0 gives collective coefficient `-kappa^2/2` above the pair coefficient `-kappa^2`. At `a=-kappa^2`, the pair coefficient is zero and is above the collective coefficient. The larger eigenvalue within the fixed negative window therefore has limiting constant-host mass 1/2 in the first sequence and zero in the second. This verifies an actual graph distinction after normalization and projector transfer, rather than merely an abstract perturbation example.

The limiting probability of p=1 is positive. More generally conditioning on any fixed p is legitimate because its probability tends to a positive Poisson mass. Unconditional probability estimates transfer to such conditioning by division by a probability bounded away from zero. No rare-pair conditioning was introduced inside the probability calculations.

## 8. Boundaries of acceptance

The application concerns the critical unweighted cubic zero-interaction augmentation with predetermined marks. It treats fixed spectral windows away from zero, not a global assertion that the resonant window contains the largest eigenvalues. It does not identify individual vectors inside repeated pair groups.

The exactly retuned logarithmic crossing remains open at finer precision. The source makes no normalized-Laplacian, mixing-time or historical-firstness claim. This review checks the paper bridge and application, not the independent validity of its authored probability premises or the scope of the separate finite formal packet.

No proof source was edited during this review. The only required source correction was CS-I1, now resolved in the accepted revision 2.
