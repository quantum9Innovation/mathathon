# Finite attachment components, revision 1

Frozen November 15, 2026. The packet checks 48 new declarations in four new source files. Two byte-for-byte copies from the growing-defects packet contribute 16 reused declarations. These are supporting declarations, not 48 new research results.

The [source manifest](SOURCE_MANIFEST-v1.json) binds every source and project file. The [validation receipt](validation-v1/CHECK.json) records the successful source-only compilation of all 64 declarations. The paper target is [port-interaction-v1](../root/port-interaction-v1.md), SHA256 `5e41e11cccc76df15cb61f4fffa59a2f8e0a5b3d6ad92554298b294df2d10d17`.

## Actual motif energy

[PortEnergy.lean](source-v1/PortEnergy.lean) starts from an actual finite real matrix D, a supplied `Invertible D` instance, and a vector b. It defines

\[
f=b^\top D^{-1}b,\qquad M=f^{-1}D^{-1}b,
\qquad y_\perp=y-(b^\top y)M.
\]

Under f nonzero it proves b transpose M=1, b transpose y_perp=0, and M nonzero. For symmetric D it proves the exact energy decomposition

\[
y^\top Dy=f^{-1}(b^\top y)^2+y_\perp^\top Dy_\perp.
\]

The profile and remainder are constructed from the inverse, rather than supplied with the desired identity as an assumption. The code also proves the exact profile Gram identity. It does not prove positivity of D, positivity of f, or a derivative formula for f.

## Actual repeated attachment matrix and lift

[AttachmentLift.lean](source-v1/AttachmentLift.lean) uses arbitrary finite host, marked, and motif coordinate types. Its actual coupling and repeated motif entries are

\[
B_{i,(j,k)}=L_{ij}b_k,\qquad
\widehat C_{(i,a),(j,b)}=\mathbf1_{i=j}C_{ab}.
\]

It defines the full block matrix H with diagonal blocks A and C-hat and off-diagonal blocks B and B transpose. It proves symmetry when A and C are symmetric, and proves its coordinate action on repeated motif profiles.

For a unit vector u with Au=du and symmetric A, set P=uu transpose. The code constructs

\[
R=(dI-A+P)^{-1}-P
\]

from the actual shifted inverse. Assuming that shifted matrix is invertible, it proves (dI-A)R=I-P, R transpose=R, and Ru=0. The port profile M is separately constructed from the actual inverse of D=dI-C. These finite inverse assumptions remain explicit.

In unscaled retained coordinates x=(alpha,v), the actual maps are

\[
Jx=(\alpha u+RLv,\ v\otimes M),\qquad
Vx=(\alpha u,\ v\otimes b),
\]

\[
Sx=\left((L^\top u)^\top v,
\ \alpha L^\top u+(L^\top RL-f^{-1}I)v\right).
\]

The checked identities are

\[
(H-dI)Jx=VSx,
\qquad
\langle Jx,Vy\rangle=\alpha\beta+v^\top w,
\]

\[
\langle Jx,Jy\rangle
=\alpha\beta+\|M\|^2v^\top w+(RLv)^\top(RLw)
\]

for y=(beta,w). The final three application theorems use the constructed inverses, not an arbitrary R assumed to satisfy the desired resolvent identities. The source is unscaled. Substituting L=p(A)E, changing v to v divided by sqrt(a), and relating the resulting coefficient to a derivative are paper application steps.

## Exact signed cancellation modes

[CancellationModes.lean](source-v1/CancellationModes.lean) uses the actual selection matrix E of an injective list of marked vertices and defines

\[
B=\begin{pmatrix}A&(dI-A)E\\E^\top(dI-A)&0\end{pmatrix}.
\]

It proves that B is symmetric when A is symmetric. If every entry A(c_i,c_j) vanishes, it derives E transpose A E=0 and proves

\[
B(Et,t)=d(Et,t).
\]

Every nonzero t gives a nonzero eigenvector. For a coordinate vector t, the source proves that the resulting vector has value one at the selected host coordinate and its new coordinate, and zero elsewhere. It also proves the host mode and an injective linear lift of the joint host and marked space. Given a nonzero u with Au=du, the eigenspace at d has formal dimension at least m+1.

This is the signed weighted cancellation model. It is not a counterexample among nonnegative simple unweighted attachments. Random independent-mark probability and polynomial calibration are outside the formal theorem.

## Concrete unweighted star motif

[StarSeven.lean](source-v1/StarSeven.lean) defines the actual adjacency matrix of K1,7 on `Option (Fin 7)`. The center is `none`. It constructs and checks both inverse products for 3I-C. The inverse has center entry 3/2, center-to-leaf entries 1/2, and leaf block delta_ij/3+1/6.

For the actual center port b it proves

\[
f=3/2,\qquad M=(1,1/3,\ldots,1/3),\qquad \|M\|^2=16/9.
\]

It specializes the motif energy decomposition with coefficient 2/3. The tree Green function, its derivative, a=26/9, and the resulting kappa, h and eta are not formally proved by this file. The packet verifies the nontrivial finite motif input to those calculations.

## New declaration inventory

Every name below has namespace `StructuralDefects`. The declarations listed by source are exact, and each has a corresponding `#print axioms` command.

| Source | New declarations |
| --- | --- |
| PortEnergy | `portProfile_equation`, `portProfile_boundary`, `portRemainder_boundary`, `port_decomposition`, `port_energy_orthogonal`, `portProfile_energy`, `port_energy_split`, `actual_port_energy_decomposition`, `portProfile_nonzero`, `portProfile_gram` |
| CancellationModes | `cancellationMatrix_symmetric`, `independent_mark_compression`, `selected_cancellation_compression`, `compactFamily_eigen_equation`, `compactFamily_injective`, `compactFamily_hasEigenvector`, `compact_single_coordinates`, `stationary_cancellation_eigen`, `cancellationLift_injective`, `cancellationLift_eigen_equation`, `cancellation_eigenspace_dimension` |
| AttachmentLift | `repeatedMotif_symmetric`, `attachmentMatrix_symmetric`, `repeatedProfile_add`, `repeatedProfile_smul`, `repeatedProfile_dot`, `repeatedMotif_action`, `portCoupling_action`, `portCoupling_transpose_action`, `attachmentMatrix_action`, `outer_projection_action`, `centered_lift_orthogonal`, `physicalLift_residual_pairing`, `physicalLift_gram`, `attachment_lift_action`, `constructed_host_resolvent_contract`, `actual_attachment_lift_action`, `actual_attachment_lift_pairing`, `actual_attachment_lift_gram` |
| StarSeven | `starSeven_symmetric`, `starSevenInverse_symmetric`, `starSeven_inverse_right`, `starSeven_inverse_left`, `starSeven_invOf`, `starSeven_response`, `starSeven_profile`, `starSeven_profile_gram`, `starSeven_port_energy` |

The copied `ProjectedResolvent.lean` and `InverseBridge.lean` preserve the earlier source-v2 bytes and namespace `GrowingDefects`. Their six and ten declarations are reused, not new. Earlier frozen packets were not edited.

## Reproducible bounded replay

From the workspace root:

```text
python3 mathathon/spectral-gap/structural-defects-round-01/formalization/validate.py --revision v1
```

The compiler is pinned to Lean 4.31.0. The mathlib source revision is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The wrapper verifies every source hash and every dependency checkout revision, reads the existing dependency cache, and compiles each packet source in dependency order into a fresh temporary directory. There is no network step and no dependency rebuild.

Each file receives two threads, a 4096 MB memory bound, and a 120-second timeout. The wrapper rejects compilation warnings, placeholder proofs, custom axioms, and unexpected axiom dependencies. All 64 printed declaration lists contain only `propext`, `Classical.choice`, and `Quot.sound`. No native computation certificate is used.

The receipt binds compiler, validator, manifest, dependency revisions, source hashes and compilation logs. A previous success receipt is removed before replay. To preserve the frozen receipt during independent replay, copy this formalization directory to a temporary location and execute the copied validator. The installed compiler and cached compiled dependencies remain trusted inputs. Their compiled contents were not rebuilt or individually authenticated.

## Unformalized bridges and exposure

- Spectral-gap hypotheses implying invertibility of the shifted host matrix, and the positive-definite eliminated blocks.
- The full inertia identity, exact top-cluster count, and spectral-projector normalization.
- Polynomial locality, the tree resolvent and derivative calculations, and identification of the metric coefficient a.
- Uniform growing-mark probability estimates, matching geometry, Poisson limits, phase dependence and both cutoff tails.
- Transfer from the finite physical lift to actual normalized graph eigenspaces and mass limits.
- The retuned negative crossing and all next-scale graph estimates.
- Any vector-polynomial multiport extension or historical priority claim.

The author previously wrote the earlier finite formal packets and reviewed the accepted negative logarithmic probability and integration files. The present code was written after reading the scalar-port candidate and the bounded priority audit. It is supporting finite verification, not independent confirmation of the whole research theorem.
