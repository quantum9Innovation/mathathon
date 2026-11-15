# A log-free marked resolvent bound from two walks

Date: November 15, 2026. Owner: root. Revision 1, frozen for review.

## 1. Statement and dependencies

Fix d>=3 and q=d-1. Let A be the adjacency matrix of a uniformly random simple labelled d-regular graph on n vertices, with nd even. Let c_1,...,c_m be distinct labels chosen before the graph. Write E for their coordinate inclusion, Pi=11^T/n and Q=I-Pi. On the event

    H = { ||A-d Pi|| <= d rho },

where 2 sqrt(q)/d < rho < 1 is fixed, define R_Q(d) as the inverse of dI-A on the range of Q, extended by zero on the range of Pi. Put G_E(d)=E^T R_Q(d) E and g=q/[d(d-2)].

The claim is

    m^3/n -> 0  implies  ||G_E(d)-g I_m|| = o_P(sqrt(m/n)).

The random matrix can be extended arbitrarily outside H. The published fixed-gap theorem gives Pr(H^c)->0. The proof needs no quantitative rate towards the tree spectral edge. It also uses the standard positive limiting probability of simplicity in the configuration model, and the reviewed single-walk diagonal estimate in SG-19. The new estimate below is proved directly by exposing two nonbacktracking walks.

Constants can depend on d, rho and a positive lower bound for the simplicity probability. All conclusions are uniform in the predetermined choice of labels. This is not a common event for all sets of labels.

## 2. The nonbacktracking polynomials

Let N_r(u,v) count length-r nonbacktracking incidence walks from u to v. Incidences are used so that configuration-model loops and multiple edges have their usual degree-d meaning. A walk may traverse the inverse of an earlier edge, but not immediately reverse its preceding incidence.

The matrices are symmetric and satisfy

    N_0=I,  N_1=A,  N_2=A^2-dI,
    N_r=A N_(r-1)-q N_(r-2)  for r>=3.

There are a_r=d q^(r-1) such walks from each root for r>=1. Write M_r=q^(-r)N_r and M_0=I. The polynomial generating function is

    sum_(r>=0) t^r N_r = (1-t^2)(I-tA+q t^2 I)^(-1).

This follows by multiplying the power series by its denominator and checking the coefficients r=0,1,2 and r>=3. Initially it is a formal identity, and it is an analytic identity whenever the series converges.

On H, there is beta in (q^(-1/2),1), depending only on rho and d, such that

    ||M_r Q|| <= C(r+1) beta^r.

For completeness, one can take beta=(d rho+sqrt(d^2 rho^2-4q))/(2q). For r>=2,

    N_r(lambda)=q^(r/2)[U_r(lambda/(2 sqrt(q)))-q^(-1)U_(r-2)(lambda/(2 sqrt(q)))].

Here U_r is the Chebyshev polynomial of the second kind. On |x|<=1, |U_r(x)|<=r+1. On 1<=|x|<=d rho/(2 sqrt(q)), its two-root formula is bounded by (r+1)(sqrt(q) beta)^r. These statements follow from U_r(cos t)=sum_(j=0)^r exp(i(r-2j)t) and the corresponding real-root sum. The cases r=0,1 are absorbed into C. Since beta<1, the series converges in operator norm on Q. Substituting t=1/q gives the exact identity

    R_Q(d)=g [Q+sum_(r>=1)(M_r-(d/q)Pi)].                    (2.1)

Choose L=ceil(C_0 log n), with C_0 large enough that

    ||R_Q(d)-g[Q+sum_(r=1)^L(M_r-(d/q)Pi)]|| <= n^(-4)     (2.2)

on H. We also take C_0 large enough that L>=log_q(sqrt(n)) for large n.

## 3. A two-walk second moment

For 1<=r and 4r+1<=nd/2, in the unconditioned pairing model,

    E ||M_r||_F^2 <= (d/q)n q^(-r)+12(d/q)^2 r^2.          (3.1)

Proof. Fix a root. Independently choose two uniformly random nonbacktracking incidence walks of length r in the sampled configuration. Reveal the pairings required by the first walk and then the second. There are at most 2r pairing discoveries. Immediately before any discovery, at most 2r+1 vertices have been visited. Given all previous discoveries and walk choices, the other endpoint of a newly paired incidence is uniform among the remaining unpaired incidences. The probability it belongs to an already visited vertex is at most

    d(2r+1)/(nd-4r-1).

A union bound therefore bounds the probability of any such collision by

    2rd(2r+1)/(nd-4r-1) <= 12r^2/n.

If there is no such collision, the revealed graph is a tree. Two nonbacktracking walks on a tree starting at the same root have the same endpoint only if their entire directed incidence sequences coincide. For every fixed configuration and first walk, the probability that the second chooses precisely that sequence is 1/a_r. Consequently

    Pr(the endpoints coincide) <= 1/a_r+12r^2/n.

For a fixed configuration the endpoint-coincidence probability is sum_v (N_r(u,v)/a_r)^2. Sum over all n roots and multiply by a_r^2 q^(-2r)=(d/q)^2. This proves (3.1). Possible loops or repeated vertices are already included in the collision event.

Let alpha_n be the simplicity probability. Because the squared Frobenius norm is nonnegative, conditioning on simplicity yields

    E_simple ||M_r||_F^2 <= C[n q^(-r)+r^2]                (3.2)

for all r<=L and large n. No conditioning on H is used in this step.

For U_(R,L)=sum_(r=R+1)^L M_r, Minkowski's inequality in the Hilbert space of square-integrable matrix entries gives

    (E ||U_(R,L)||_F^2)^(1/2)
      <= C sum_(r=R+1)^L [sqrt(n) q^(-r/2)+r]
      <= C[sqrt(n) q^(-R/2)+L^2].

Thus

    E ||U_(R,L)||_F^2 <= C[n q^(-R)+L^4].                 (3.3)

This deliberately uses an uncentered second moment. It pays only a harmless L^4 term after coordinate sampling.

## 4. Label symmetry and exclusion of short interactions

For a relabelling-equivariant random matrix U and fixed distinct marks, exchangeability gives

    E sum_(a!=b) |U(c_a,c_b)|^2
      = m(m-1)/[n(n-1)] E sum_(u!=v) |U(u,v)|^2.          (4.1)

The same conclusion follows by first drawing an independent uniform m-subset of vertices in an unlabelled graph. We use this equality only under the unconditional simple-graph law.

In any d-regular graph, a radius-R ball contains at most

    1+d(q^R-1)/(q-1)

vertices. Therefore, by label symmetry and a union bound, the probability that two distinct marked vertices have distance at most R is at most

    C m(m-1) q^R/n.                                      (4.2)

Let O(V)=V-diag(V) denote deletion of the diagonal. On the complementary separation event, O(E^T M_r E)=0 for all 1<=r<=R. Equations (3.3) and (4.1) imply

    E ||O(E^T U_(R,L) E)||_F^2
      <= C m^2/n^2 [n q^(-R)+L^4].                       (4.3)

Set s=sqrt(m/n) and R=floor(log_q(1/s)). Under m^3/n->0, R->infinity, R<=L, q^R<=1/s and q^(-R)<=q s. Write theta=m s=sqrt(m^3/n). The separation failure probability is O(theta), while (4.3) divided by s^2 is

    O(theta+m L^4/n)=o(1).                               (4.4)

The projected stationary correction in (2.2) has off-diagonal operator norm at most

    C m(1+L)/n=o(s).

Indeed, its matrix is a scalar multiple of J_m-I_m, whose norm is at most m. For every symmetric matrix V, ||O(V)||<=2||V||, so the tail in (2.2) contributes at most 2n^(-4). Applying Markov's inequality to (4.3), and then adding the probabilities of H^c and separation failure, proves

    ||O(G_E(d))||=o_P(s).                                (4.5)

More explicitly, for any t>0, the off-diagonal error exceeds C t s+C m(1+L)/n+2n^(-4) with probability at most

    Pr(H^c)+C theta+C t^(-2)(theta+m L^4/n).

## 5. Diagonal terms and the derivative bridge

Take an ordinary random-walk truncation T=ceil(C_1 log n) with host and tree tails at most n^(-4). The reviewed SG-19 single-walk estimate states that D_k(c)=P^k(c,c)-tau_k>=0 and E_simple D_k(c)<=C k(k+1)/n. Consequently, on H,

    max_a |G_E(d)_(aa)-g|
      <= (1/d)sum_a sum_(k=0)^T D_k(c_a)+(T+1)/(dn)+2n^(-4).

The expectation of the nonnegative sum is O(m T^3/n). Dividing this by s gives O(s T^3)=o(1) when m^3/n->0. The deterministic terms are also o(s). Markov's inequality proves the diagonal error is o_P(s). Together with (4.5), this proves the statement in Section 1.

For each fixed j>=1, the existing general SG-19 estimate is

    ||G_E^(j)(d)-g_d^(j)(d) I||
      = O_P([m log^(j+3)n+m(m-1)log^(j+1)n]/n
              +log^j(n)n^(-4)).

This tends to zero under m^3/n->0. The dimension-free local derivative bounds from the host gap are unchanged. The probability of an edge between two marks is O(m^2/n)=o(1).

## 6. Consequence and exact scope

All hypotheses used by the reviewed deterministic transfer, weighted cluster theorem and zero-interaction eigenvector theorem now hold under m^3/n->0. Thus SG-20 and SG-21 extend to this log-free range, with all their original constants, fixed-degree weighted conventions, uniformity in bounded H, and eigenvector qualifications preserved.

This is a paper proof. Section 3 is an elementary configuration-model estimate. The formal component of this round covers only its separately stated finite identities, not the random graph law, analytic series, asymptotic probability or full spectral transfer.
