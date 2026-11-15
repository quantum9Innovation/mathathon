# Review of the logarithm-free two-walk upper bound

Date: November 15, 2026, America/Los_Angeles.

Disposition: accepted at the stated scope. No unsupported inference was found in the frozen proof. The argument establishes the marked-resolvent collective-scale approximation and fixed-order derivative convergence under m cubed divided by n tending to zero. It uses the earlier fixed host gap, without requiring quantitative convergence to the tree spectral edge.

Exact reviewed file: root/nonbacktracking-upper-v1.md.

SHA256: `d21878acf9a31191b8386748c87ea7933be966c08c0b5a46fe66d685f39e5896`.

The entire frozen proof was read and its hash checked. The reviewer had developed a separate polynomial-locality proof before receiving the coordinator's nonbacktracking idea. That alternative was frozen before this proof file was read. The route was therefore disclosed before review, while the two-walk estimate and all transfers below were reconstructed from the exact frozen revision. This is not a claim of blind discovery or independent origin.

## 1. Incidence conventions and the generating identity

The incidence convention correctly handles configuration loops and parallel edges. Each root has d first-step choices and q=d-1 subsequent choices. Reversing the immediately preceding incidence is forbidden, including for a loop, but an older incidence may be traversed again. Thus the exact number of length-r walks is d q^(r-1) for r>=1.

The initial matrices and recurrence are correct under that convention:

\[
 N_0=I,\quad N_1=A,\quad N_2=A^2-dI,\quad
 N_r=AN_{r-1}-qN_{r-2}\quad(r\ge3).
\]

The degree-d subtraction at r=2 removes exactly one immediate reversal for each first incidence. The recurrence gives the stated formal generating function. Reversal of a nonbacktracking incidence path proves symmetry of each N_r.

At t=1/q, the generating denominator restricted to Q is (dI-A_Q)/q. Its numerator is 1-q^(-2). The inverse prefactor is therefore

\[
 \frac{q}{q^2-1}=\frac{q}{d(d-2)}=g.
\]

For r>=1 the row sum of M_r is d/q. This proves the stationary subtraction in equation (2.1), including the separate Q term at r=0.

## 2. Complementary spectral tail

Since d rho lies strictly between 2 sqrt(q) and d, the proposed beta lies strictly between q^(-1/2) and one. The displayed second-kind Chebyshev formula agrees with the initial conditions and recurrence.

On the tree interval, the bound on U_r is r+1. Beyond that interval but within the fixed host spectral bound, the real-root sum gives the bound (r+1)(sqrt(q) beta)^r. The same absolute bound holds on the negative half by parity. It follows that ||M_rQ|| is at most C(r+1)beta^r.

This proves norm convergence of the projected series and its geometric tail. A sufficiently large fixed multiple of log(n) makes that tail at most n^(-4), while also meeting the specified lower bound for L. The full unprojected series is not asserted to converge at t=1/q.

## 3. The two-walk second moment

The important event inclusion is valid without conditioning the independent-path probability on collision-freeness:

\[
 \{\text{endpoints coincide}\}
 \subseteq
 \{\text{the two incidence sequences agree}\}
 \cup\{\text{an accidental pairing collision occurs}\}.
\]

After revealing at most two length-r paths from the same root, a collision-free revealed graph is a tree. A nonbacktracking path in a tree from its root is simple, and its endpoint determines its complete path. Thus endpoint coincidence on that event forces identical incidence sequences.

For every fixed completed configuration and first walk, the second independent walk follows that exact sequence with probability 1/(d q^(r-1)). This remains true when the first path itself has collisions, because it is still a valid incidence sequence with the same number of successive choices. No independence between the collision event and sequence agreement is needed.

During adaptive exposure, unmatched half-edge partners remain uniform conditional on all previously exposed pairings and walk choices. Those choices depend only on the exposed path and do not inspect unpaired partners. At most 2r pairs and 2r+1 vertices are involved. The denominator nd-4r-1 is a safe lower bound on the available partners. Under the stated condition 4r+1<=nd/2 it is at least nd/2, so

\[
 \frac{2rd(2r+1)}{nd-4r-1}\le\frac{12r^2}{n}.
\]

Previously exposed edges require no new pairing. Loops and second edges to an already discovered vertex fall in the collision event. The argument therefore covers both kinds of configuration defects.

For a fixed configuration the endpoint-collision probability is exactly the squared Euclidean norm of the root's normalized N_r row. Summing over roots and multiplying by (d/q) squared gives precisely the constants in equation (3.1). Conditioning the nonnegative squared Frobenius norm on simplicity costs only the reciprocal simplicity probability. No spectral-gap conditioning is introduced into this calculation.

## 4. The uncentered tail and coordinate sampling

Minkowski's inequality is applied in the Hilbert space of square-integrable matrix entries. It does not require independence between different lengths. Summing the two parts of the square-root moment bound gives order sqrt(n) q^(-R/2)+L squared. Squaring proves equation (3.3). The uncentered Perron contribution is harmless at this stage and is compatible with the L^4 term.

Equation (4.1) follows exactly from exchangeability of all ordered distinct vertex pairs. It is used under the unconditional uniform simple graph law. The matrix U_(R,L) is a relabelling-equivariant polynomial sum in the adjacency, so that hypothesis is satisfied.

On the stated separation event, graph distance excludes every walk of length at most R between distinct marked vertices, hence excludes every short nonbacktracking contribution. Combining the ball-volume union bound with the sampled Frobenius bound gives the two errors

\[
 O\!\left(\sqrt{m^3/n}\right),\qquad
 O\!\left(\sqrt{m^3/n}+mL^4/n\right).
\]

For R=floor(log_q(1/s)), both radius inequalities and R<=L are correct. Under m cubed divided by n tending to zero, m<=n^(1/3) eventually, so mL^4/n tends to zero.

The stationary compression contributes a scalar multiple of J_m-I_m, whose operator norm is at most m. Thus its size divided by s is O(s log(n)), which tends to zero. Deleting the diagonal of the compressed tail costs at most twice its operator norm. These bounds complete the off-diagonal approximation without multiplying a tail error by m squared.

## 5. Diagonal, derivative and spectral application

The diagonal argument correctly retains only one copy of the deterministic return-series tail and stationary bound when passing to a maximum. The nonnegative random contribution is bounded by the sum over marked vertices, with expectation O(m log(n)^3/n). Its ratio to s is O(s log(n)^3), which tends to zero in the new range.

The previously proved fixed-order derivative estimate holds for arbitrary deterministic m and was not confined to the older collective-scale range. Its right side tends to zero for every fixed derivative order when m cubed divided by n tends to zero. The fixed host gap still gives the required dimension-free local Taylor bounds. The probability of any marked host edge also tends to zero.

The claimed extension of the already reviewed cluster and eigenvector conclusions is justified. Inspection of the frozen eigenvector-mass proof confirms that its only probabilistic inputs are the cluster comparison, derivative convergence and uniform local Taylor control. None of those arguments uses the old logarithmic range elsewhere. The uniformity over bounded H and the restrictions of the H=0 eigenvector statement are preserved rather than enlarged.

## 6. Corroboration and boundaries

As an incidence-convention check, direct enumeration of all 15 pairings of six half-edges verified the N_r matrix recurrence against nonbacktracking path counts for lengths one through six. These 90 matrix checks include loops and parallel edges. They corroborate the conventions only and are not premises of the general proof or the second-moment inequality.

No corrective finding is required. This review does not establish historical firstness, a matching lower bound, actual spectral failure at the boundary, or end-to-end formalization. The separately frozen polynomial-locality argument remains an alternative upper proof with an additional quantitative host-spectrum dependency.
