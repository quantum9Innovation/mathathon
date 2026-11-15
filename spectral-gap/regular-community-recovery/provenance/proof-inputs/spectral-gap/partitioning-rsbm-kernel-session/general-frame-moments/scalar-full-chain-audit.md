# Fresh scalar full-chain audit: exact moment and all-parameter RSBM simplicity

Prepared November 15, 2026 by `frame_chain_audit`. This file is a new independent audit; no proof source or frozen manuscript was edited. The actual source was read in full. The review concerns mathematical correctness and scope, not historical novelty.

**Verdict: PASS.** The scalar assembly and its two independently written scalar modules correctly derive

`E_config |ker_Fp(A_N-lambda I)| = 2 p^t+o(1)`,

where `t=dim_Fp ker(Q-lambda I)`, for a connected nonbipartite common-degree-at-least-three frame and each fixed odd prime. Together with the already checked central and boundary modules, this proves planted real-eigenvalue simplicity with high probability for every fixed regular-SBM pair `d1>d2>0`, at every admissible block size. The fixed-prime argument does not provide a polynomial real failure rate.

## Actual source versions

- `scalar-regular-frame-theorem.md`: final SHA256 `50bf9df8032bab7817a0239e5fe850ff0a0b4640a3a684c0206d94fae755b80d`. The final delta explicitly says `K0 intersect L` has finite index in `K0`, not that `K0` has finite index in the larger-span `L0`; this is a correct precision improvement and was reread.
- `scalar-central-equidistribution.md`: SHA256 `2ca675978aa450a3db04d33d33b571bb0f455e33e006c04f2fde7227c49023e0`.
- `scalar-lattice-rank.md`: SHA256 `7738f0c8d2aa86f7e4aaf50ff02f2b6741885076a60625f368c593d5755cc2e2`.
- `central-frame.md`: SHA256 `e64d46ae873a6ce568b76784788b1605a38e249c2f8983451372486eff0315a7`.
- `boundary-frame.md`: SHA256 `cbfd5c6c8372bbbb1a4e2ef01426bfd93225e54cc7842e9efadc7802fe07f5e4`.
- Master assembly `bounded-frame-moment-theorem.md`: SHA256 `6c6da08c6d944e1f9cd76706f08b660fb9be82579549fbae347404e8b99e7e0b`.
- Standalone `regular-frame-moments.tex`: final SHA256 `ef7b862873f7501149dcf0525eaa18b8fd6e16ecbfe77fd12746e57b3f26ba42`; PDF SHA256 `e276858cf236b00b38ed7f695818d82086b10935f2f80bb7e3db44cad0d6b845`. The complete TeX mathematical source was read and matches the audited modules. Its final two spacing-command corrections were checked as a formatting-only delta. The eight-page PDF build has no warnings, unresolved references, or overfull boxes.

The new central and boundary modules were independently reconstructed and audited before this sharpening; details are in `full-chain-audit.md`. The central source was reread after its final section-reference correction. Its required relative local estimate and weighted-reference concentration are proved inputs, not assumptions left outstanding here.

## 1. Integer compatible lattice and its legal sublattice

Keep all physical-slot tables. Their unrestricted direction lattice `L0` consists of integer arrays with zero total in every slot and one common root-row vector at each old type. This is the actual maximal independent-star difference lattice. The compatible subgroup `K0` additionally imposes pooled cross transpose constraints and pooled internal symmetry with even diagonal. These are exactly the integer equality and parity constraints of the pairing weights.

The local legal lattice `L` has index `I=p^(kp)` inside `L0` and is the kernel of the `kp` root-row congruences

`C_i,a(m)=sum_s sum_b b m_i,s(a,b)-lambda a r_i(a)` in `F_p`.

This maximal-lattice characterization was separately proved by the additive-character argument in the central module. It includes the root label zero and every physical slot; no old degree multiplicity is divided out.

At every admissible size, the all-zero star table is both compatible and legal. It supplies a common affine origin. Thus the independent compatible support lattice is `m0(N)+K0`, and the legal compatible support lattice is `m0(N)+(K0 intersect L)`. These are support lattices, not a claim that congruences characterize actual legal-star realizability everywhere. Actual positivity of their central points is supplied by the proven uniform lattice local limit theorem. This distinction is sufficient for every subsequent step.

## 2. The compatible congruence image has exactly the asserted rank

Let a coefficient family `h_i:F_p->F_p` annihilate `C(K0)`. For every cross factor, place a zero-row/zero-column two-by-two interaction in one physical slot and its transpose in one reverse slot. The common root margins stay zero, so this is an actual integer direction in `K0`. It is not multiplied by `q_ij` or `q_ji`; it remains available if those integers vanish modulo the prime.

The annihilator equation is

`[h_i(a)-h_i(a')](b-b')+[h_j(b)-h_j(b')](a-a')=0`.

Anchoring at labels zero and one shows that both functions are affine, with opposite slopes. This uses only nonzero differences of field labels, never a type size or degree factor.

An internal factor admits the parity-preserving integer direction

`2(e_aa+e_bb-e_ab-e_ba)`

in one internal slot. Its rows are zero, its pooled table is symmetric, and its diagonal is even. Its annihilator value is `2(a-b)[h_i(a)-h_i(b)]`. Odd characteristic therefore makes `h_i` constant. This constancy propagates over cross edges. If no internal factor exists, a cross-support odd cycle makes the alternating slopes equal their own negatives and hence zero. Connected nonbipartite support therefore leaves precisely constant functions `h_i(a)=c_i`.

The remaining functional is indeed `(Q-lambda I)c`, not its transpose. For a pooled cross table, transpose compatibility makes the sum of neighbor labels in type `i`'s slots to `j` equal to `q_ji S_j`, with `S_j=sum_a a r_j(a)`. Therefore collecting the coefficient of `S_j` gives `sum_i q_ji c_i-lambda c_j=(Qc)_j-lambda c_j`. Internal symmetry gives the same diagonal contribution.

The root moments `S_i` are independently variable in the actual integer lattice. This is proved explicitly, avoiding saturation assumptions. For arbitrary integer zero-total root vectors `r_i`, construct a cross table with row margins `q_ij r_i` and column margins `q_ji r_j` using the zero row and column as anchors. For an internal table with desired rows `v=q_ii r_i`, put `v(a)` in entries `(a,0),(0,a)` for nonzero labels and `2v(0)` in `(0,0)`; its zero row has total `v(0)` and its diagonal is even. Split each pooled table among its physical slots using anchor-column tables with common row vector `r_i` and a residual last slot. Negative entries are permissible in a direction.

This realizes arbitrary `r_i` over the integers. In particular `r_i=e_1-e_0` varies exactly one `S_i` by one. The scalar assembly's alternative use of twice arbitrary margins is also sufficient because two is invertible. Thus the annihilator is exactly `ker(Q-lambda I)` of dimension `t`, without any condition involving `p|q_ij` or `p|a_i`.

The image `C(K0)` is an additive subgroup of `F_p^(kp)` and hence an `F_p`-subspace. Its annihilator dimension `t` proves

`J=[K0:K0 intersect L]=|C(K0)|=p^(kp-t)`.

## 3. Weighted finite-coset equidistribution is justified

The normalized weighted independent law `nu_N=K_N Q_N W` is an exact probability law: sample the independent configuration factors, then iid uniform root labels. The central proof gives its subgaussian concentration about the uniform physical-slot mean, with only a bounded internal-loop correction. Its mass in the `sqrt(N)log N` window tends to one.

Fix an integer direction `z in K0`. The unrestricted full-slot relative local limit estimate gives `Q_N(m+z)/Q_N(m)=1+o(1)` uniformly on the logarithmic window and its fixed-width enlargement. The exponent changes by `O(log N/sqrt(N))`; all relevant affine lattice points have positive unrestricted mass.

The exact graph weight has the same ratio. In a cross pool, the finite factorial ratio has leading logarithm equal to its zero total shift times the logarithm of the uniform pooled mean. In an internal pool, the diagonal shifts are even: a shift `2h` changes `(m-1)!!` by a finite product asymptotic to `m^h`. The combined leading exponent is half the total symmetric table shift, again zero. There is no extra factor of two in this asymptotic. All counts are `Theta(N)` in the window, and fixed translations preserve nonnegativity, reversal, and parity.

It follows that `nu_N(m+z)/nu_N(m)=1+o(1)` there. Extending the law by zero outside its finite actual support is harmless: both complementary masses outside an inner window tend to zero, and a fixed translation moves the radial threshold by only `O(1)`. This proves convergence in total variation between `nu_N` and its translate by `z`.

The quotient `K0/(K0 intersect L)` has the fixed finite size `J`. Choose fixed integer representatives. Their translations permute its affine cosets, so all coset masses differ by `o(1)` and each is `1/J+o(1)`. This argument does not assert that a finite-support probability law is exactly translation invariant or that every congruence class has positive mass at small sizes. It proves the required asymptotic equidistribution.

On the legal affine lattice the central likelihood ratio is `I(1+o(1))`. Combining it with the legal compatible coset mass gives logarithmic-window contribution `I/J+o(1)=p^t+o(1)`. The full fixed-neighborhood annulus is `o(1)` by the already-proved cubic likelihood-ratio/subgaussian-tail integration. Hence the sharp uniform-phase coefficient is exactly `p^t`.

## 4. Completing the sharp scalar moment

For the scalar alphabet `F_p`, the only linear subspaces are `0` and `F_p`. The complete nonbipartite zero-phase classification therefore consists of the full-uniform phase and the type-constant point phases in `ker(Q-lambda I)`, exactly `p^t` of them. Every point phase gives one exact eigenvector for every configuration, irrespective of the scale or its residue modulo the prime.

The sparse boundary estimate applies with zero-dimensional restricted space. Each point neighborhood consequently contributes exactly `1+o(1)`, with excess bounded by `O(N^{-(d-2)/2})`. The possible singleton configuration support is retained in that rate.

Distinct point maps differ on a full old class of fixed positive proportion, so fixed small defect neighborhoods can be chosen disjoint. The full-uniform table neighborhood can also be shrunk away from them because a point root law is a fixed positive distance from uniform at fixed `p`. Their complement in the feasible type space is compact and has no zero of the continuous entropy exponent. The exact finite type count with its polynomial prefactor therefore makes that complement `o(1)`.

Thus the two contributions add without double counting:

`E_config |ker_Fp(A_N-lambda I)| = p^t+p^t+o(1)=2p^t+o(1)`.

This verifies the full scalar assembly, not merely its central lattice coefficient. It does not claim the same sharp numerical moment after simplicity conditioning.

## 5. All-parameter regular-SBM consequence

For `Q=[[d1,d2],[d2,d1]]`, the old support is connected because `d2>0` and nonbipartite because `d1>0` gives self-incidences. Common degree is `d1+d2>=3`; fixed positive degrees `d1>d2` ensure this even in the hard pair `(2,1)`. All admissible block sizes satisfy `N d1` even; no further parity assumption is introduced by the lattice calculation.

At the integer planted eigenvalue `lambda=d1-d2`, every fixed odd prime not dividing `d2` gives

`Q-lambda I=[[d2,d2],[d2,d2]]`,

so `t=1`. The configuration-model finite-field moment is `2p+o_p(1)`.

The planted integer sign vector supplies a deterministic real kernel line. If real nullity is at least two, every integer minor of order `2N-1` vanishes, so the finite-field nullity is at least two. Markov gives limiting probability at most `2/p`. Subtracting the deterministic modular planted line would improve this to `1/(p-1)`, but is unnecessary. For every fixed admissible prime the size limit is taken first; infinitely many such primes exist. Sending them to infinity proves configuration-model excess real nullity probability tends to zero. No unproved growing-prime uniformity is used.

The two internal and cross factors have a positive degree-dependent limiting simplicity probability, independent of the prime. Direct conditioning therefore carries the real high-probability conclusion to precisely the requested uniform-simple RSBM. This is a probability-event transfer, not a claim that the sharp fixed-prime moment remains unchanged under conditioning.

Hence, within the proved model, `dim ker_R(A-(d1-d2)I)=1` with high probability for every fixed `d1>d2>0`, including `(2,1)` and odd block sizes when `d1` is even. The localized `(2,1)` lower bound of order `N^-2` on failure is consistent with a qualitative high-probability theorem. No polynomial upper error rate follows from this fixed-prime argument.

## 6. Master bounded-moment assembly and algorithm delta

The master `bounded-frame-moment-theorem.md` correctly assembles the central, phase, sparse, and compact-complement inputs for every fixed finite vector dimension and target matrix. Its direct simplicity conditioning is legitimate for the raw moment. Its enlarged bipartite two-space induction is closed, with exact equal total physical side sizes even if individual old classes are unequal.

The master also correctly records all fixed power moments: pointwise `Z_R^s=Z_diag(R,...,R)` for every fixed integer `s`. Thus the general theorem supplies `E p^(s h_R)=O(1)` at fixed enlarged target dimension. Projection to the right kernel before enumeration remains the economical algorithmic composition, but doubled-kernel enumeration could also be bounded using the separately available doubled-target moment. The updated `full-chain-audit.md` states this distinction explicitly.

No substantive mathematical defect was found in the reviewed scalar sources or master assembly. The statements still require fixed frame/field parameters and nonbipartite old support with odd prime for the sharp scalar formula. The general bounded vector moment does not require those last two scalar restrictions. Historical priority, optimized rates, and finite-size numerical constants remain separate questions.
