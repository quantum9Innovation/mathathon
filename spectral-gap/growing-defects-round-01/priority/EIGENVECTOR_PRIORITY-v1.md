# Eigenvector mass comparison addendum

November 15, 2026, America/Los_Angeles.

Scope: a bounded extension of [PRIORITY-v1.md](PRIORITY-v1.md), after acceptance of [eigenvector-masses-v1.md](../root/eigenvector-masses-v1.md) at SHA256 a98fa21b356991a4e3d6a51f1568984f9d0592d3c81c893e0ec81f6fb11561d6. The [separate review](../reviews/eigenvector-masses-v1-review.md) accepts the paper argument, not historical firstness or formal verification. No broad literature search was reopened.

## Existing overlap formulas

Benaych-Georges and Nadakuditi already derive an outlier's squared projection onto the relevant spike eigenspace from the derivative of the limiting Cauchy transform. Their Theorem 2.2 gives the limit -1/(theta^2 G'(rho)). The inspected setting has fixed rank, independent host and perturbation, and invariance of one of them. Resolvent reconstruction and derivative normalization are established methods. Inspection: version 3, Section 2.1, Theorem 2.2, Proposition 5.1 and the normalization passage in Section 7. The full source proof was not re-audited here. [Primary source](https://arxiv.org/html/0910.2120v3).

Huang's Theorem 2.7 already treats projected eigenvector norms and approximate spike-eigenvector directions for mesoscopic rank in the orthogonally or unitarily independent model. It permits any eigenvector of a repeated outlier and gives a failure bound of the form C exp(-c_1 N epsilon^2+c_2 M), under fixed separation hypotheses. Inspection: version 2, Section 2.1, Theorem 2.7 and its resolvent and squared-resolvent identities (8) through (16), together with the earlier audit of Theorems 2.1 and 2.8. This confirms a close methodological precedent, not applicability to the present dependent regular graph. [Primary source](https://arxiv.org/html/1412.4193v2).

## What the present extension adds to its graph theorem

The possible distinguishing claim is the explicit three-way mass law at a finite-host Perron resonance, for deterministic localized marks with growing m in a fixed-degree random regular graph. The attachment B=sqrt(d-2)AE depends on the host, and the host has an isolated constant eigenvector. The accepted graph-specific resolvent estimates yield extreme masses 1/2, 1/(2D_d) and (D_d-1)/(2D_d), plus uniform middle-eigenvector masses 0, 1/D_d and (D_d-1)/D_d. The inspected deformation theorems do not directly supply this model and calibration.

This is an explicit corollary of the accepted probability and effective-matrix inputs, not a new general theory of overlaps. Historical firstness remains unverified. Subspace masses alone do not prove spatial localization or graph-distance decay. The same fixed marked-set and weighted-model boundaries from the main audit continue to apply.
