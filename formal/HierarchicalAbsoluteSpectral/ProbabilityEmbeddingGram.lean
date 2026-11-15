import HierarchicalAbsoluteSpectral.ProbabilityEmbeddingFrame
import HierarchicalAbsoluteSpectral.StrongFilterRange

/-! The embedding acts on an arbitrary input matrix. A basis of its range
is used only inside the proof; dependent columns and the zero matrix require
no algorithmic rank assumption. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix WithLp SparseFock SRHT
open SparseFock.MatrixTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

theorem rectangular_gram_quadratic {ι : Type*} [Fintype ι] {m : ℕ}
    (A : Matrix ι (Fin m) ℝ) (x : Fin m → ℝ) :
    quadratic (Aᵀ*A) x = ‖applyRectMatrix A (toLp 2 x)‖^2 := by
  rw [quadratic, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [applyRectMatrix, dotProduct, pow_two]

theorem rectangular_orthonormal_norm {ι : Type*} [Fintype ι] {m : ℕ}
    (U : Matrix ι (Fin m) ℝ) (hU : Uᵀ*U = 1) (v : EuclideanSpace ℝ (Fin m)) :
    ‖applyRectMatrix U v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hh := rectangular_gram_quadratic U (ofLp v)
  rw [hU] at hh
  simpa only [toLp_ofLp, quadratic_one_norm] using hh.symm

theorem applyRectMatrix_mul {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) (v : EuclideanSpace ℝ ν) :
    applyRectMatrix (A*B) v = applyRectMatrix A (applyRectMatrix B v) := by
  simp only [applyRectMatrix, ofLp_toLp, Matrix.mulVec_mulVec]

theorem sampledFrame_mul {k r m : ℕ} (U : Matrix (WalshIndex k) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin m) ℝ) (x y : SignAssignment k) (T : Finset (WalshIndex k)) :
    sampledFrame (U*W) x y T = sampledFrame U x y T*W := by
  ext i j
  unfold sampledFrame transformedFrame
  rw [← Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

def IsRelativeEmbedding {k m : ℕ} (A : Matrix (WalshIndex k) (Fin m) ℝ)
    (x y : SignAssignment k) (T : Finset (WalshIndex k)) (ε : ℝ) : Prop :=
  (1-ε) • (Aᵀ*A) ≤ (sampledFrame A x y T)ᵀ*sampledFrame A x y T ∧
    (sampledFrame A x y T)ᵀ*sampledFrame A x y T ≤ (1+ε) • (Aᵀ*A)

theorem relative_embedding_of_range_ose {k r m : ℕ}
    (U : Matrix (WalshIndex k) (Fin r) ℝ) (W : Matrix (Fin r) (Fin m) ℝ)
    (hU : Uᵀ*U = 1) (x y : SignAssignment k) (T : Finset (WalshIndex k)) (ε : ℝ)
    (hE : FixedSizeTail.IsOSE U x y T ε) : IsRelativeEmbedding (U*W) x y T ε := by
  have hv : ∀ v : EuclideanSpace ℝ (Fin m),
      (1-ε)*‖applyRectMatrix (U*W) v‖^2 ≤
        ‖applyRectMatrix (sampledFrame (U*W) x y T) v‖^2 ∧
      ‖applyRectMatrix (sampledFrame (U*W) x y T) v‖^2 ≤
        (1+ε)*‖applyRectMatrix (U*W) v‖^2 := by
    intro v
    rw [applyRectMatrix_mul, rectangular_orthonormal_norm U hU, sampledFrame_mul,
      applyRectMatrix_mul]
    exact hE (applyRectMatrix W v)
  have hG : ((U*W)ᵀ*(U*W)).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self (U*W)).isHermitian
  have hB : ((sampledFrame (U*W) x y T)ᵀ*sampledFrame (U*W) x y T).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self (sampledFrame (U*W) x y T)).isHermitian
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub (hG.smul (by rfl)))
    intro v
    change 0 ≤ quadratic _ v
    rw [quadratic_sub, quadratic_smul, rectangular_gram_quadratic, rectangular_gram_quadratic]
    exact sub_nonneg.mpr (hv (toLp 2 v)).1
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((hG.smul (by rfl)).sub hB)
    intro v
    change 0 ≤ quadratic _ v
    rw [quadratic_sub, quadratic_smul, rectangular_gram_quadratic, rectangular_gram_quadratic]
    exact sub_nonneg.mpr (hv (toLp 2 v)).2

theorem orthonormal_walsh_range_factorization {k m : ℕ}
    (A : Matrix (WalshIndex k) (Fin m) ℝ) :
    ∃ r : ℕ, r ≤ m ∧ ∃ U : Matrix (WalshIndex k) (Fin r) ℝ,
      Uᵀ*U = 1 ∧ ∃ W : Matrix (Fin r) (Fin m) ℝ, A = U*W := by
  let e := gaussianWalshEquiv k
  let B : Matrix (Fin (2^k)) (Fin m) ℝ := A.submatrix e.symm id
  obtain ⟨r,hr,U,hU,W,X,hB,hX⟩ := orthonormal_range_factorization B
  let V : Matrix (WalshIndex k) (Fin r) ℝ := U.submatrix e id
  refine ⟨r,hr,V,?_,W,?_⟩
  · ext i j
    change (∑ a : WalshIndex k, U (e a) i*U (e a) j) = (1 : Core r) i j
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans
      (congrArg (fun M : Core r => M i j) hU)
  · ext i j
    have hh := congrArg (fun M : Matrix (Fin (2^k)) (Fin m) ℝ => M (e i) j) hB
    simpa [B,V,Matrix.mul_apply] using hh

theorem gaussian_embedding_arbitrary_matrix_prescribed {k m M q : ℕ}
    (A : Matrix (WalshIndex k) (Fin m) ℝ)
    (hM : M ≤ 2^k) (hM0 : 0 < M) (hq : 1 ≤ q)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfailure : (m : ℝ)*(1/2 : ℝ)^(2*q) ≤ δ)
    (hsize : M < 2^k → 8192*(effectiveDimension m q : ℝ)/ε^2 ≤ M) :
    ∃ E : Set ((Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))),
      MeasurableSet E ∧ (gaussianSRHTInputLaw k).real E ≥ 1-δ ∧
        ∀ g ∈ E, let z := (gaussianSRHTSampleProgram k M hM g).eval
          IsRelativeEmbedding A z.1 z.2.1 z.2.2.val ε := by
  obtain ⟨r,hr,U,hU,W,hA⟩ := orthonormal_walsh_range_factorization A
  let E := gaussianSRHTSample k M hM ⁻¹'
    {z | FixedSizeTail.IsOSE U z.1 z.2.1 z.2.2.val ε}
  have hEm : MeasurableSet E :=
    (Set.toFinite _).measurableSet.preimage (gaussianSRHTSample_measurable k M hM)
  have hfr : (r : ℝ)*(1/2 : ℝ)^(2*q) ≤ δ := by
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by positivity)).trans hfailure
  have hsz : M < 2^k → 8192*(effectiveDimension r q : ℝ)/ε^2 ≤ M := by
    intro hm
    apply le_trans _ (hsize hm)
    apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact_mod_cast (show effectiveDimension r q ≤ effectiveDimension m q by
      dsimp [effectiveDimension]; omega)
  refine ⟨E,hEm,?_,?_⟩
  · change 1-δ ≤ (gaussianSRHTInputLaw k).real
      {g | FixedSizeTail.IsOSE U (gaussianSRHTSample k M hM g).1
        (gaussianSRHTSample k M hM g).2.1 (gaussianSRHTSample k M hM g).2.2.val ε}
    simpa only [gaussianSRHTSampleProgram_eval] using
      gaussian_embedding_frame_prescribed k r M q hM hM0 hq U hU ε δ hε hε1 hfr hsz
  · intro g hg
    simp only [gaussianSRHTSampleProgram_eval]
    rw [hA]
    exact relative_embedding_of_range_ose U W hU _ _ _ ε hg

end
end HierarchicalAbsoluteSpectral
