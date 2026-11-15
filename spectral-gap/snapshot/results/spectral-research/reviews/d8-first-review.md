# Review of the spectral-multiplicity submission

## Assessment

The exact Seidel multiplicity bound and its graph corollary have complete, correct proofs. The equality case via two eigenvalues is correct. The proof that equality for a connected $d$-regular graph implies at most three distinct eigenvalues and the diameter-two Moore bound $n\le d^2+1$ is also valid. The stability identity is a sum of squared deviations over the remaining $n-k$ eigenvalues, exactly as derived in the appendix.

The $K_4\square C_k$ example is correct: paired cycle modes give $\lambda_2=\lambda_3$ and the stated positive fraction above the degree-relative threshold. This is different from an accidental numerical coincidence. The more general $d\ge9$ obstruction to a defect count bounded by $(d,\varepsilon)$ follows from the given Cartesian product formulas.

## Checks run

- Ran `seidel_core.py`, `mult_bound.py`, `defect_count.py`, `fold_and_equi.py`, `three_eig.py`, and `srg_families.py`.
- Ran the complete bounded `nauty` enumeration of connected cubic graphs through $n=18$, quartic graphs through $n=14$, and quintic graphs through $n=12$. It completed in about 29 seconds and reproduced the reported graph counts and record multiplicities.
- Checked the primary abstract of Haiman, Schildkraut, Zhang and Zhao, arXiv:2109.13131v3, against the cited lower bounds and the approximate-multiplicity barrier.
- Independently reconstructed the first two Seidel trace moments, the equality variance identity, and the cycle-pair multiplicity argument.

## Incidental correction

Section 4.4 must not list $Q_4$ with zero slack and zero variance. Its own output has slack $230.4$ and four distinct Seidel eigenvalues. Remove $Q_4$ from that particular list. This does not affect the identity proved in Theorem 3.4.

The discussion of $Q_4$ as a near-equality or non-equality example is compatible with the numerical output. Several closed walk and enumeration statements were checked numerically and are not formal proof certificates.

## Review boundary

Acceptance covers the exact proofs and the computations checked above. It does not certify every bibliographic assertion, every record-holder identification or the literature-novelty claim. No Pushforward Cayley or Plancherel-mass research target in the future-work section is accepted as an already established theorem.
