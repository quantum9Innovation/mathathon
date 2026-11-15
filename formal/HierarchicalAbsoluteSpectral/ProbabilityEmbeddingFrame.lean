import HierarchicalAbsoluteSpectral.GaussianEmbeddingProgram

/-! The exact SRHT theorem for caller-prescribed integer parameters. The
parameters need no logarithm or ceiling oracle: only the displayed power and
row-count inequalities are used. Zero-dimensional frames are included. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix SparseFock SRHT
open SparseFock.FiniteLocalMoments
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem gaussian_embedding_frame_prescribed (k d M q : ℕ)
    (hM : M ≤ 2^k) (hM0 : 0 < M) (hq : 1 ≤ q)
    (U : Matrix (WalshIndex k) (Fin d) ℝ) (hU : Uᵀ*U = 1)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfailure : (d : ℝ)*(1/2 : ℝ)^(2*q) ≤ δ)
    (hsize : M < 2^k → 8192*(effectiveDimension d q : ℝ)/ε^2 ≤ M) :
    1-δ ≤ (gaussianSRHTInputLaw k).real
      {g | let z := (gaussianSRHTSampleProgram k M hM g).eval
        FixedSizeTail.IsOSE U z.1 z.2.1 z.2.2.val ε} := by
  simp only [gaussianSRHTSampleProgram_eval]
  change 1-δ ≤ (gaussianSRHTInputLaw k).real
    (gaussianSRHTSample k M hM ⁻¹'
      {z | FixedSizeTail.IsOSE U z.1 z.2.1 z.2.2.val ε})
  rw [gaussian_srht_sampling_probability]
  apply FixedSizeTail.success_of_tail U hM (signLaw k) (signLaw k) ε δ hε.le
  by_cases hf : M = 2^k
  · have he : {z : SignAssignment k × (SignAssignment k × RowSet k M) |
        ε ≤ ‖sampledGram U z.1 z.2.1 z.2.2.val-1‖} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      have hT : z.2.2.val = Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa using z.2.2.property.trans hf
      rw [hT, sampledGram_univ U hU]
      simpa using not_le.mpr hε
    rw [he, FiniteLaw.prob_empty]
    exact (mul_nonneg (Nat.cast_nonneg d) (by positivity)).trans hfailure
  · have hMn : M < 2^k := lt_of_le_of_ne hM hf
    have hBern := BernoulliMoment.moment_bound U hU q hq hM0 hMn
    have hmoment := FixedSizeTail.moment_of_bernoulli_bound U hU hM0 hMn q
      (signLaw k) (signLaw k) (matchesUpTo_refl _ _) (matchesUpTo_refl _ _) _ hBern
    have hD : (0 : ℝ) ≤ effectiveDimension d q := Nat.cast_nonneg _
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
    exact (FixedSizeTail.tail_of_moment_bound U hM (signLaw k) (signLaw k) q
      (by omega) ε (4*momentEnvelope (effectiveDimension d q) M) hε
      (by positivity [envelope_nonneg hD hMr])
      (amplified_envelope_le_half hD hMr hε hε1 (hsize hMn)) hmoment).trans hfailure

end
end HierarchicalAbsoluteSpectral
