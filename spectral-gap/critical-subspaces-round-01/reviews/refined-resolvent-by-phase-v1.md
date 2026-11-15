# Independent review of the selected-sector resolvent estimates

Date: November 15, 2026, America/Los_Angeles.

Decision: accepted at the exact frozen revision. The selected compression, selected-column square, derivative and retained-matrix interface estimates are justified. No unresolved mathematical finding remains. The finer tree calculation is correctly separated from a finite-graph theorem.

## Revision and exposure

The complete file `probability/refined-resolvent-v1.md` was read at SHA256

`bd00db6c2f69813d480f5a86d5d22c8b6fe4922d9cc3d233f72840dddb29f8df`.

Prior exposure includes the accepted earlier probability and effective-operator proofs, the author's proposed rare-pair selection route and claimed rates, the finite resonance calculation written by this reviewer, and the new graph isometry proof reviewed separately. The reviewer did not develop or write this probability proof. Its selected sums, inclusion factors, scaling and projector consequences were reconstructed from the frozen text rather than accepted from agreement between authors.

## 1. Exact sampling and nonnegative quantities

Relabelling invariance permits an independent uniform m-subset after the host is sampled. Each subsequent sum uses the inclusion probability of its actual number of distinct vertices. No expectation is conditioned on a selected pair or on the host-gap event.

The nonbacktracking tail U is symmetric and entrywise nonnegative. Every positive-length term has row sum 3/2 after normalization by 2 to the path length, so the asserted deterministic O(L) row and entry bounds are exact upper bounds. The older two-walk estimate gives the stated unconditioned squared Frobenius bound. Diagonal deletion only decreases the nonnegative sums used below.

On the host-gap and short-path uniqueness events, the expansion into the positive marked tail, diagonal error, stationary off-diagonal correction and operator tail is algebraically correct. In particular, the stationary coefficient includes both the Q term and all L nonbacktracking terms. The diagonal estimate divided by s is O_P(L^3/m), and the stationary operator norm divided by s is O(L/m). Failure of the expansion event has probability tending to zero, which is sufficient for the asserted O_P rates without a quantitative rate for that exceptional probability.

## 2. Pair selection without dividing by its probability

For (15), the distance indicator is bounded by the number of nonbacktracking walks at the short length ell. Every tail length exceeds ell, so the two compared incidence sequences are distinct. In a collision-free exposed tree, they cannot have the same endpoint. Multiplication of the collision probability by the exact walk counts and the number of starting vertices gives the required expectation. The counted quantity is nonnegative, so conditioning on simplicity costs only the fixed reciprocal lower bound on its probability. Summation of the normalized long-walk counts gives C 2^ell L^3. Multiplication by the deterministic entry bound CL proves (16).

The three selected estimates use the following distinct-vertex counts:

| Bound | Coincident partner case | Other endpoint case |
| --- | --- | --- |
| (21), selected collective entries | Two marked vertices, (15), and factor 1/sqrt(m) | Three marked vertices, distance row bound C 2^ell and tail row bound CL |
| (22), selected-column squares | Two marked vertices and (16) | Three marked vertices, distance row bound C 2^ell and the full Frobenius estimate |
| (23), selected compressed entries | Two marked vertices and (15) | Four distinct marked vertices on the matching event, two distance row bounds and the total tail row sum |

For (21), summing possible short partners overcounts the indicator that a vertex was selected. Nonnegativity makes this a valid upper bound even if several partners exist. The same argument applies to (22).

For (23), matching is used exactly where needed. If two selected endpoints are not partners, their two selected pairs have four distinct vertices. Dropping the matching indicator after bounding by this four-vertex sum only increases it. Conditional on the host, the inclusion probability is then p_4, not a probability conditional on the rare pair event. Summing the two partner indicators for fixed row and column vertices gives at most C 2^(2ell), and summing U gives at most C n L. This reconstructs the displayed bound.

At criticality, n is comparable to m cubed, s to 1/m, 2^ell to m and H_R to m squared. Direct substitution gives precisely

\[
 \|P_VTe/s\|=O_P(L/m^{3/2}+L^3/m^{5/2}),
\]

\[
 \|TP_V/s\|_F^2=O_P(L^4/m),
 \qquad
 \|P_VTP_V/s\|=O_P(L^3/m^2).
\]

The phase remains in bounded factors because the fractional part lies between zero and one. The claimed uniformity in phase is therefore valid for fixed offsets.

## 3. Collective and projector estimates

The collective quadratic form uses two selected vertices. Expanding its column norm square separates identical second endpoints, which use p_2, from distinct second endpoints, which use p_3. This gives (17)-(20) with the correct factor 1/m from the normalized constant vector. The additional logarithmic terms in (20) are smaller than 1/m.

For the family consisting of e and the selected coordinate vectors, the only nontrivial Gram overlaps are 1/sqrt(m) with e. Its smallest eigenvalue is 1-sqrt(|V|/m), and its largest eigenvalue is 1+sqrt(|V|/m). Tightness of |V| supplies fixed upper and lower Gram bounds with probability tending to one. Thus the column and compressed-block estimates transfer to orthogonal projector estimates without a growing dimension factor.

The nonnegative tail contributes O_P(L/m) to the compression and O_P(L^4/m) to the squared column norm. The diagonal and stationary remainder contributes O_P(L^3/m) to compression and O_P(L^6/m^2) to the squared column bound. The latter is smaller than L^4/m. This proves (5).

The global tail Frobenius estimate gives ||B_K||=O_P(1). It is not promoted to a vanishing fixed-cutoff global error.

For the free-vector variant, write f=e+d with ||d||=O_P(m^(-1/2)). Compressed blocks change by O_P(L^2/m), using the already established selected columns. For the squared column bound one may use explicitly

\[
 \|B_K f\|^2\le2\|B_K e\|^2+2\|B_K d\|^2.
\]

The second term is O_P(1/m), while the first has order L^4/m. This supplies the claimed bound without needing a bound of O_P(1/m) on the raw difference of the two squared norms. The new coordinate family is orthonormal because f vanishes on every selected endpoint. The free-vector conclusions follow.

## 4. Rates, actual retained matrix and cutoff order

The old j=1 estimate remains valid at criticality. Its substitution and the exact derivative formula give (31), including the stationary correction and D=8. Both L^3/m and L^4/m are o(m^(-3/4)) and hence o(m^(-1/2)). These statements concern the compression and the squared selected-column norm respectively, not an assertion that the selected-column norm itself is o(m^(-1/2)).

The exact retained-matrix identity has coefficient 9/8 multiplying B_K and stationary coefficient 3/(4ns). Its stationary operator norm is 3s/4=O(1/m). The exceptional marked-adjacency term vanishes on an event whose probability tends to one. Extending the selected projector by the host coordinate therefore preserves the estimates.

All selected bounds are for fixed K. The proof separately retains the previous global error probability C eta^(-2) 2^(-K), which is used by first taking n to infinity and then K to infinity. No step requires inserting a growing K into the fixed-cutoff estimates. A future Schur or subspace application must retain that order and the gap hypothesis, as the handoff states.

## 5. Tree correction and precision boundary

The cubic tree recursion gives g_3=t/(1-t squared), with 2t squared-zt+1=0. At z=3, t=1/2, t'/t=-1 and g_3'/g_3=-5/3. Differentiation of z squared g_3 t^ell therefore gives logarithmic derivative -(ell+1), with the displayed sign.

On a compact interval above the tree edge, the first and second logarithmic derivatives are bounded by constants times ell. Since ell times s tends to zero, exponentiating the Taylor expansion gives the relative O(ell squared s squared) remainder in (35), uniformly for bounded x. For nonzero x of constant size and a bounded nonzero pair amplitude, the first correction has size s ell, which exceeds 1/m and is below m^(-3/4).

This is an exact tree computation. The proof explicitly declines to identify the finite-graph correction at order 1/m or to select a negative resonant basis from these bounds alone. That distinction is necessary and correct.

## Accepted scope

The accepted result is the quantitative selected-sector estimate, its free-vector version, the derivative rate and the exact actual-matrix interface. They can support a separate graph resonance argument with a justified complementary gap and Schur reduction. This review does not promote such an application before its own proof is frozen and checked.
