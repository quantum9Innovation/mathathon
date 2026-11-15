# Formal statement and application-scope audit, revision 2

Date: November 15, 2026, America/Los_Angeles.

Disposition: accepted as formalized finite matrix components with the exact scope below. The random-graph theorem is not formalized end to end. No hidden assumption of the requested spectral conclusion, admitted proof or custom axiom was found in the inspected source.

## 1. Exact reviewed material and independence

The three source files were read in full. The reviewer did not author these formal files. The reviewer did author the separate probability paper proof and had already audited the paper application, so this is an independent inspection of the formal implementation with that mathematical exposure declared. It is not another independent proof of the probability theorem.

| Frozen source | SHA256 |
| --- | --- |
| source-v2/CollectiveModes.lean | 3d7f369c5230e5c63246f8f1ecabb0c6786cf0a6e472cab952b70860c26d6858 |
| source-v2/ProjectedResolvent.lean | 1ef860f88e9c39c0b3898c7cd0b7ab3861286270a6e2ac5501d6374c431a2084 |
| source-v2/InverseBridge.lean | ef84856396a1c4063a4f6abc612c3e4600f047274afd79c4b26e99f2c6b0321c |
| validate.py, replayed revision | 5688229ad45ece58f0982740a48e9c176b37c0d1fd03710d9ed87887ad0b328f |
| validate.py, final equivalent style revision | 2c55a5b9f12fe78e3b0446a9f16523e8c5544268da07fd28456255a41267bce2 |

SOURCE_MANIFEST-v2.json binds these three sources and the toolchain, package configuration and dependency manifest. The first two source files are unchanged from revision 1. Revision 2 adds the constructed inverse bridge described below.

## 2. What the collective-mode file proves

The definition collectiveMatrix is an actual real matrix indexed by Option (Fin m). The none coordinate is the single host mode. The some coordinates are the m defects. The only nonzero entries join the host coordinate to every defect with the same weight b. This is precisely the finite star matrix used in the paper when H=0.

The effectiveMatrix definition sets b=(3/sqrt(8))/sqrt(m). Thus for positive m it is the actual normalized cubic effective matrix, not an unspecified operator assumed to have the desired spectrum.

The checked statements establish:

- The exact coordinate formula for multiplication by the star matrix.
- The bright-vector eigen-equation under t squared equals m, and nonzero eigenvectors when m is positive.
- The two actual effective eigenvectors with eigenvalues 3/sqrt(8) and its negative.
- A characterization of the general star kernel, for m positive and b nonzero, by zero host coordinate and zero sum of defect coordinates.
- Every real eigenvalue of the effective matrix is zero or one of the two displayed nonzero values.

The eigenvector premise in nonzero_eigenvalue_square and the eigenvalue premise in eigenvalue_trichotomy are the ordinary definitions being classified. Neither assumes the resulting value or square identity. The positive and negative effective-mode theorems separately prove existence of their nonzero vectors.

The file does not explicitly prove that the kernel has dimension m-1, an orthonormal eigenbasis, the characteristic polynomial, or the complete ordered spectrum with multiplicities. In particular, the trichotomy permits zero as a candidate and is not an existence assertion for a zero mode at m=1. The paper uses a full multiplicity statement. That additional bridge has not been encoded here.

## 3. Actual selection matrices and stationary compression

The selectionMatrix is constructed from an injection Fin m into Fin n. Its entries are the coordinate-selection indicators. The theorem selection_isometry proves its transpose product is the identity. Thus the formalization does not merely assume that a generic E represents distinct marked labels.

The stationaryMatrix is the actual n by n matrix with every entry 1/n. The markedStationary matrix is the actual m by m matrix with the same entries. The theorem marked_stationary_matrix proves the exact compression E transpose P E=J_m/n.

The polynomial and Schur identities include the stationary correction with its correct negative sign. In particular, the marked identity has the term minus (z+d) times markedStationary. This checks the correction that was missing in some historical paper arguments.

Revision 1 left R as an arbitrary matrix satisfying the two resolvent equations. Those equations at z=d alone do not force its stationary component to vanish. This was a declared application boundary, not a false identity. Revision 2 strengthens the implementation by constructing R and proving its centering.

## 4. The new constructed inverse bridge

The formal construction is

\[
 S=dI-A+P,\qquad R=S^{-1}-P.
\]

Invertibility of S is an explicit typeclass assumption. Under AP=PA=dP and P squared equals P, the source proves

\[
 SP=PS=P,\qquad S^{-1}P=PS^{-1}=P,
\]

then

\[
 (dI-A)R=R(dI-A)=I-P,\qquad PR=RP=0.
\]

The centering conclusion is proved and is not supplied as a hypothesis. The inverse is constructed from the actual shifted matrix. There is no assumption that R already satisfies the desired resolvent identity.

For the stationary P, the source proves idempotence when n is positive. It derives AP=dP from constant row sums and PA=dP from constant column sums. The final theorem actual_constructed_marked_identity instantiates the exact selected-coordinate identity at z=d using this R. Its remaining assumptions are positive n, distinct selected labels, constant row and column sums, and invertibility of dI-A+P. These are meaningful matrix hypotheses, not a disguised assumption of the marked identity or collective spectral theorem.

The formal result is not restricted to symmetric adjacency matrices and does not encode a SimpleGraph object. Its broader matrix statement is valid. A graph application still needs to establish its regularity and invertibility hypotheses for the actual graph matrix.

## 5. Exact remaining application bridges

The following parts of the reviewed paper theorem remain outside these formal sources:

1. The finite simple regular graph sample space, its adjacency matrix and the relation between graph degree and the formal row and column sums.
2. Derivation of invertibility of dI-A+P from the host spectral-gap event. The new algebraic construction removes the arbitrary-R premise, but it does not prove the event or this spectral implication.
3. Configuration pairing, simplicity conditioning, universal-cover walk comparison, label-symmetry estimates and all probability limits for the growing marked set.
4. Identification with the analytic restricted resolvent as a function of z, derivative and norm estimates, and the growing-set approximation at the collective scale.
5. The finite quantitative transfer by Schur complement inertia, Taylor bounds, Weyl comparison, root counts, ordering and interlacing.
6. The full effective spectrum with multiplicities, and the weighted general-degree and arbitrary bounded H interaction theorem.
7. The asymptotic passage from those ingredients to the augmented graph eigenvalues, uniformly over H.

These are proof-assistant application boundaries. They do not retract the separately reviewed paper proofs. The current implementation should be described as formalized matrix components supporting the proof, not as a formal proof of the complete growing-defect theorem.

## 6. Inspected validator and independent replay

The replayed validator was read before execution. It checks the source and configuration hashes, the installed Lean 4.31.0 version, and the recorded HEAD revision of each cached dependency. It invokes the compiler directly with two threads, a 4096 MB memory setting and a 120-second timeout for each source. A temporary compiled-output directory is placed first on the import path so InverseBridge imports the freshly compiled ProjectedResolvent from the same frozen source.

The validator requires a successful, warning-free compile. It also checks that every declared theorem has a printed axiom report and that each report contains only propext, Classical.choice and Quot.sound. The inspected source contains no sorry, admit, custom axiom or unsafe declaration. The replay found no additional axiom dependency.

An independent replay was performed from a copy of the frozen files in /tmp/spectral-formal-scope-rbp_6g_4. It completed on November 15, 2026 at 08:30:52 UTC, corresponding to 00:30:52 Pacific. All 27 theorem and axiom checks passed, comprising 11 collective-mode statements, six projected identities and ten inverse-bridge statements. The replay receipt SHA256 is

`2d1dc1690636d7ace242c718637bedd75d5b3f2277b11660c1303bef4f368218`.

The receipt confirms that its source bindings match SOURCE_MANIFEST-v2.json. Author validation files and all source files were left unchanged. The installed dependency cache was reused and was not rebuilt from a clean dependency checkout. This is a fresh compile of the supplied component sources against those recorded cached dependencies, not a complete bootstrap of the proof system and its library.

After that replay, the author replaced one literal character in the validator's prohibited-character list with the equivalent expression chr(59). The complete diff was inspected. It changes no behavior, source binding, compiler command or theorem. The final wrapper hash is recorded above. No duplicate compilation was run for that style-only change. The final formalization README was also read and accurately states the component scope and remaining bridges.

## 7. Conclusion

No correction is required in the frozen formal sources at the audited scope. Revision 2 substantively improves the result by constructing and centering the inverse before applying the actual marked-coordinate identity. The remaining claims must retain their separate paper-proof, review and formalization status. Declaration count does not enlarge the mathematical scope of the encoded statements.
