import HierarchicalAbsoluteSpectral.CoarseAlgebraSingularInertiaCost

/-! Ambient Gaussian congruence before support compression. The sufficient
event consists of polynomial minors of the original matrix and the fixed
ambient Gaussian array, independent of the computed support basis. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n r : ℕ}

def leadingGaussianColumns (n r : ℕ) (hr : r ≤ n) (g : Fin (n*n) → ℝ) :
    Matrix (Fin n) (Fin r) ℝ :=
  (gaussianSquareMatrix n g).submatrix id (Fin.castLEEmb hr)

theorem leading_columns_congruence_minor (D G : Core n) (r : ℕ) (hr : r ≤ n)
    (j : ℕ) (hj : j ≤ r) :
    leadingPrincipal ((G.submatrix id (Fin.castLEEmb hr))ᵀ*D*
      G.submatrix id (Fin.castLEEmb hr)) j hj =
        leadingPrincipal (Gᵀ*D*G) j (hj.trans hr) := by
  ext a b
  simp [leadingPrincipal,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply]

theorem InertiaSupport.projected_congruence {D : Core n} (support : InertiaSupport D)
    (G : Matrix (Fin n) (Fin support.dimension) ℝ) :
    (support.basisᵀ*G)ᵀ*support.compressed*(support.basisᵀ*G) = Gᵀ*D*G := by
  calc
    _ = Gᵀ*(support.basis*support.compressed*support.basisᵀ)*G := by
      simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
    _ = _ := congrArg (fun A => Gᵀ*A*G) support.decomposition.symm

theorem InertiaSupport.congruenceMinorPolynomial_ne_zero {D : Core n}
    (support : InertiaSupport D) (hD : Dᵀ = D) (j : ℕ) (hj : j ≤ support.dimension) :
    congruenceMinorPolynomial D j (hj.trans support.dimension_le) ≠ 0 := by
  let H := support.compressed
  have hH : H.toEuclideanLin.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
      using support.compressed_transpose hD
  let U := strongSpectralQ H hH
  let e := Fin.castLEEmb support.dimension_le
  let W : Core n := Matmul.UniversalPaddedAlgorithm.pad
    (Function.Embedding.refl (Fin n)) e (support.basis*U)
  have hW : W.submatrix id e = support.basis*U := by
    ext a b
    exact Matmul.UniversalPaddedAlgorithm.pad_apply (Function.Embedding.refl (Fin n)) e
      (support.basis*U) a b
  have hS : support.basisᵀ*(W.submatrix id e) = U := by
    rw [hW,← Matrix.mul_assoc,support.basis_orthogonal,Matrix.one_mul]
  have hForm : (W.submatrix id e)ᵀ*D*(W.submatrix id e) = Uᵀ*H*U := by
    rw [← support.projected_congruence,hS]
  have hReg := spectral_congruence_leading_regular H hH support.compressed_isUnit
  have hMinor : IsUnit (leadingPrincipal (Wᵀ*D*W) j (hj.trans support.dimension_le)).det := by
    rw [← leading_columns_congruence_minor D W support.dimension support.dimension_le j hj,
      hForm]
    exact hReg j hj
  intro hz
  have he := congruenceMinorPolynomial_eval D W j (hj.trans support.dimension_le)
  rw [hz,map_zero] at he
  exact (isUnit_iff_ne_zero.mp hMinor) he.symm

def projectedReducedInertiaProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D : Core n} (support : InertiaSupport D) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ) :
    ArithmeticProgram (Option (FiniteCongruenceDiagonal support.compressed)) := do
  let S ← (kernels support.dimension n support.dimension).program support.basisᵀ
    (leadingGaussianColumns n support.dimension support.dimension_le g)
  congruenceInertiaProgram kernels support.compressed (support.compressed_transpose hD) S

theorem projectedReducedInertiaProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D : Core n} (support : InertiaSupport D) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ) :
    (projectedReducedInertiaProgram kernels support hD g).admissible := by
  simp only [projectedReducedInertiaProgram,admissible_bind,
    ArithmeticKernel.program_admissible,congruenceInertiaProgram_admissible,and_self]

theorem projectedReducedInertiaProgram_success
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {D : Core n} (support : InertiaSupport D) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ)
    (hReg : ∀ (j : ℕ) (hj : j ≤ support.dimension), IsUnit
      (leadingPrincipal ((gaussianSquareMatrix n g)ᵀ*D*gaussianSquareMatrix n g)
        j (hj.trans support.dimension_le)).det) :
    ∃ out, (projectedReducedInertiaProgram kernels support hD g).eval = some out := by
  let G := leadingGaussianColumns n support.dimension support.dimension_le g
  have hregular : LeadingPrincipalRegular ((support.basisᵀ*G)ᵀ*
      support.compressed*(support.basisᵀ*G)) := by
    rw [support.projected_congruence]
    intro j hj
    rw [show leadingPrincipal (Gᵀ*D*G) j hj =
      leadingPrincipal ((gaussianSquareMatrix n g)ᵀ*D*gaussianSquareMatrix n g)
        j (hj.trans support.dimension_le) from
          leading_columns_congruence_minor D _ _ support.dimension_le j hj]
    exact hReg j hj
  unfold projectedReducedInertiaProgram
  rw [eval_bind,ArithmeticKernel.program_eval]
  exact congruenceInertiaProgram_success kernels _ (support.compressed_transpose hD) _ hregular

def projectedSingularInertiaProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ) :
    ArithmeticProgram (Option (FiniteCongruenceDiagonal D)) := do
  let support ← inertiaSupportProgram kernels D hD
  let out? ← projectedReducedInertiaProgram kernels support hD g
  match out? with
  | none => ArithmeticProgram.pure none
  | some out => do
    let lifted ← inertiaLiftProgram kernels support out
    ArithmeticProgram.pure (some lifted)

theorem projectedSingularInertiaProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ) :
    (projectedSingularInertiaProgram kernels n D hD g).admissible := by
  simp only [projectedSingularInertiaProgram,admissible_bind,
    inertiaSupportProgram_admissible,projectedReducedInertiaProgram_admissible,true_and]
  split
  · trivial
  · simp only [admissible_bind,inertiaLiftProgram_admissible,admissible_pure,and_self]

theorem projectedSingularInertiaProgram_success
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ)
    (hReg : ∀ (j : ℕ) (hj : j ≤ (inertiaSupportProgram kernels D hD).eval.dimension),
      IsUnit (leadingPrincipal ((gaussianSquareMatrix n g)ᵀ*D*gaussianSquareMatrix n g)
        j (hj.trans (inertiaSupportProgram kernels D hD).eval.dimension_le)).det) :
    ∃ out, (projectedSingularInertiaProgram kernels n D hD g).eval = some out := by
  let support := (inertiaSupportProgram kernels D hD).eval
  obtain ⟨out,ho⟩ := projectedReducedInertiaProgram_success kernels support hD g hReg
  unfold projectedSingularInertiaProgram
  rw [eval_bind,eval_bind,ho,eval_bind,eval_pure]
  exact ⟨_,rfl⟩

theorem projectedSingularInertiaProgram_success_of_polynomial_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ)
    (hg : ∀ (j : ℕ) (hjn : j ≤ n), congruenceMinorPolynomial D j hjn ≠ 0 →
      MvPolynomial.eval (fun x : Fin n × Fin n => g (finProdFinEquiv x))
        (congruenceMinorPolynomial D j hjn) ≠ 0) :
    ∃ out, (projectedSingularInertiaProgram kernels n D hD g).eval = some out := by
  apply projectedSingularInertiaProgram_success
  intro j hj
  apply isUnit_iff_ne_zero.mpr
  rw [← congruenceMinorPolynomial_eval]
  exact hg j _ ((inertiaSupportProgram kernels D hD).eval.congruenceMinorPolynomial_ne_zero hD j hj)

theorem projectedSingularInertiaProgram_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) :
    ∀ᵐ g ∂gaussianVector (n*n),
      ∃ out, (projectedSingularInertiaProgram kernels n D hD g).eval = some out := by
  have hall : ∀ᵐ g ∂gaussianVector (n*n), ∀ (j : ℕ) (hj : j ≤ n),
      congruenceMinorPolynomial D j hj ≠ 0 →
        MvPolynomial.eval (fun x : Fin n × Fin n => g (finProdFinEquiv x))
          (congruenceMinorPolynomial D j hj) ≠ 0 := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro hj
    by_cases hp : congruenceMinorPolynomial D j hj ≠ 0
    · filter_upwards [gaussian_polynomial_reindex_ne_zero_ae (n*n) finProdFinEquiv _ hp] with g hg
      exact fun _ => hg
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hp h))
  filter_upwards [hall] with g hg
  exact projectedSingularInertiaProgram_success_of_polynomial_event kernels n D hD g hg

end
end HierarchicalAbsoluteSpectral
