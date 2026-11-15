# Independent finite-formal scope audit and replay

November 15, 2026. Reviewer: root.

Targets: SOURCE_MANIFEST-v2.json, SHA256 a1f64406dab4bbbeeb18eed65aa3daace3b11f1483f1bb1ebffcb0401ff98095, and README-v2.md, SHA256 43735ac99f1a4695fec21a3c802ec726aa4066b44b01f7d181e02f14df9b3431, under formalization.

Verdict: accepted at the documented finite scope. A fresh copy compiled every source in the manifest. All 73 declaration checks passed. Of these, 57 belong to this round and 16 are unchanged earlier declarations. Revision 2 includes the 48 current-round declarations already present in revision 1, so its totals must not be added to the earlier totals.

## What was independently checked

The reviewer read the actual definitions and theorems in PortEnergy, AttachmentLift, CancellationModes and ArrowSchur, and checked the concrete star-motif statement against its explicit inverse and profile. The formal statements use actual matrices and constructed maps. Their inverse and nonzero assumptions remain visible.

PortEnergy constructs M from the supplied matrix inverse and constructs the orthogonal remainder from y. Its energy decomposition is therefore not obtained by assuming the desired decomposition. Positivity and the derivative interpretation remain outside the formal statement, as documented.

AttachmentLift constructs the repeated motif matrix and the full host-to-motif coupling. Its final application theorems construct the projected host inverse from (dI-A+uu transpose)^(-1)-uu transpose and construct the motif profile from (dI-C)^(-1). They prove the residual action, dual pairing and Gram bilinear form for those actual objects. The source does not formally show that a host spectral gap implies the supplied inverse instances, nor identify the profile norm with an analytic derivative.

CancellationModes derives the zero marked compression from the entrywise independent-mark condition. It proves the exact graph action on (Et,t), nonzero eigenvectors, two-coordinate support for individual compact modes, and the injective joint host-plus-mark lift. Its eigenspace dimension lower bound is an actual finite-dimensional statement. The signed weights and random independent-mark application remain paper scope boundaries.

StarSeven supplies an explicit two-sided inverse for the actual shifted eight-vertex star adjacency. Its port response is 3/2 and its profile is one at the center and 1/3 on every leaf. Thus its squared profile norm is 16/9. The source checks this finite motif, not the tree response or random-graph constants.

ArrowSchur defines actual finite diagonal and arrow matrices. Its inverse interpretation requires nonzero denominators, and the guarded inverse theorems state that condition. The quadratic identities with total real inverses remain algebraically true even at a zero denominator, but they are used as resolvent identities only where the guarded hypotheses hold. The code verifies the corrected leading column, its projection, the diagonal complementary quadratic, an actual arrow Rayleigh-Schur witness, and the finite combination kappa w/(kappa+w).

The first-order reference correction in ArrowSchur is explicitly defined in the finite model. Its identification as the derivative of the normalized growing finite-arrow basis is a paper asymptotic step, not a formal theorem in this packet. The documentation preserves this distinction.

## Fresh execution

The complete formalization directory was copied to a new temporary directory. The copied validate-v2.py was executed with its own temporary compiled outputs. The original compiler receipt, source files and validation logs were not overwritten. The retained independent result is formal-replay-v2.json, with the associated formal-replay-v2.log.

The wrapper checked pinned source hashes, Lean 4.31.0 and each dependency checkout revision, then compiled all seven sources in dependency order. Every source had a two-thread, 4096 MB and 120-second bound. No network action or dependency rebuild occurred.

All printed axiom lists contained only propext, Classical.choice and Quot.sound. There were no placeholder proofs, custom axioms, warnings or native computation certificates. The installed compiler and existing compiled dependency cache remain trusted inputs. The replay does not independently rebuild or authenticate all compiled dependency objects.

## Remaining application bridges

The graph probability space, marked geometry, nonbacktracking moment estimates, Poisson convergence, infinite compensated series, Fourier density argument and integer asymptotics are not formally encoded.

The packet also does not encode the full inertia theorem, the physical spectral-projection normalization, the exact nonlinear root comparison, or the nonseparable polynomial-port extension. Those remain independently reviewed paper arguments.

No complete open random-graph result is claimed formally proved by counting these supporting declarations. The finite checking materially supports the attachment reconstruction and screened Schur mechanism at their exact stated scope.
