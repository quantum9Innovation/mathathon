import HierarchicalAbsoluteSpectral.ProbabilityInitializerProgram
import HierarchicalAbsoluteSpectral.MinMaxNear

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem strongEigenvalues_pos_of_posDef {k : ℕ} (T : Core k)
    (hT : T.toEuclideanLin.IsSymmetric) (hPD : T.PosDef) (i : Fin k) :
    0 < strongEigenvalues T hT i := by
  let v := strongSpectralBasis T hT i
  have hv : v ≠ 0 := (strongSpectralBasis T hT).orthonormal.ne_zero i
  have hv' : WithLp.ofLp v ≠ 0 := by
    intro hz
    apply hv
    simpa using congrArg (WithLp.toLp 2) hz
  have hpos := hPD.dotProduct_mulVec_pos hv'
  have heq : quadratic T (WithLp.ofLp v) = strongEigenvalues T hT i := by
    rw [quadratic_eq_inner]
    exact eigenvalue_rayleigh T.toEuclideanLin hT finrank_euclideanSpace_fin i
  have hpos' : 0 < quadratic T (WithLp.ofLp v) := by
    simpa only [quadratic, star_trivial] using hpos
  rwa [heq] at hpos'

/-- The actual program's computed value brackets the target eigenvalue on
one explicit measurable event; no range or Frobenius result is an oracle. -/
theorem gaussian_initializer_program_good_event {k r : ℕ}
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) (hr : r < k)
    (hd : ∀ i, 0 ≤ strongEigenvalues T hT i)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ E : Set (Fin r → Fin k → ℝ), MeasurableSet E ∧
      (gaussianColumns k r).real E ≥ 1-β ∧ ∀ G ∈ E,
        let out := (gaussianInitializerProgram kernels T (columnsMatrix G) β).eval
        strongEigenvalues T hT ⟨r,hr⟩ ≤ out.value ∧
          out.value ≤ initializerRatio k β*strongEigenvalues T hT ⟨r,hr⟩ := by
  obtain ⟨E,hEm,hEp,hE⟩ := gaussian_initializer_good_event T hT hr hd β hβ hβ1
  refine ⟨E,hEm,hEp,?_⟩
  intro G hG
  let out := (gaussianInitializerProgram kernels T (columnsMatrix G) β).eval
  have hb := hE G hG out.range.dimension out.range.dimension_le_cols out.range.basis
    out.range.orthogonal out.range.coefficients (out.raw_eq.symm.trans out.range.spans)
  change strongEigenvalues T hT ⟨r,hr⟩ ≤ out.value ∧
    out.value ≤ initializerRatio k β*strongEigenvalues T hT ⟨r,hr⟩
  rw [out.value_eq]
  exact hb

theorem gaussian_initializer_positive_bracket_event {k r : ℕ}
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.toEuclideanLin.IsSymmetric) (hr : r < k)
    (hd : ∀ i, 0 ≤ strongEigenvalues T hT i)
    (hpos : 0 < strongEigenvalues T hT ⟨r,hr⟩)
    (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ E : Set (Fin r → Fin k → ℝ), MeasurableSet E ∧
      (gaussianColumns k r).real E ≥ 1-β ∧ ∀ G ∈ E,
        let out := (gaussianInitializerProgram kernels T (columnsMatrix G) β).eval
        ∃ l u : ℝ, out.result = .bracket l u ∧ 0 < l ∧
          l ≤ strongEigenvalues T hT ⟨r,hr⟩ ∧ strongEigenvalues T hT ⟨r,hr⟩ ≤ u ∧
            u/l = initializerRatio k β := by
  obtain ⟨E,hEm,hEp,hE⟩ := gaussian_initializer_program_good_event kernels T hT hr hd β hβ hβ1
  refine ⟨E,hEm,hEp,?_⟩
  intro G hG
  let out := (gaussianInitializerProgram kernels T (columnsMatrix G) β).eval
  have hb := hE G hG
  have ht : 0 < out.value := hpos.trans_le hb.1
  have hC : 0 < initializerRatio k β := initializerRatio_pos k β (by omega) hβ
  refine ⟨out.value/initializerRatio k β,out.value,?_,by positivity,?_,hb.1,?_⟩
  · rw [out.result_eq, if_neg (not_le.mpr ht)]
  · exact (div_le_iff₀ hC).mpr (by nlinarith [hb.2])
  · field_simp

/-- A concrete fast cost consequence of the actual operation bound. The
kernel hypothesis is discharged by the repository's native fast circuits. -/
theorem gaussianInitializerProgram_work_bound {k r : ℕ}
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N : ℝ)^p)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ)
    (hk : 1 ≤ k) (hr : r ≤ k) :
    ((gaussianInitializerProgram kernels T Ξ β).work : ℝ) ≤ 100*(C+1)*(k : ℝ)^p := by
  have he := kernelEnvelope_bound kernels C p hC hK k hk
  have hpsd : (psdGramCost kernels r : ℝ) ≤ 9*(C+1)*(k : ℝ)^p := by
    by_cases hr1 : 1 ≤ r
    · apply (psdGramCost_bound kernels C p hC hp hK r hr1).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hr) (by linarith)
    · have hr0 : r = 0 := by omega
      rw [hr0, psdGramCost]
      simp only [Nat.cast_zero]
      positivity
  have hb : ((gaussianInitializerProgram kernels T Ξ β).work : ℝ) ≤
      5*(kernelEnvelope kernels k : ℝ)+(psdGramCost kernels r : ℝ)+3*(k : ℝ)*(k : ℝ)+k+10 := by
    exact_mod_cast gaussianInitializerProgram_work_le kernels T Ξ β hk hr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (k : ℝ)^2 ≤ (k : ℝ)^p := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hk1 hp
  have hkp0 : 0 ≤ (k : ℝ)^p := Real.rpow_nonneg (by positivity) _
  have hkp1 : 1 ≤ (k : ℝ)^p := by nlinarith
  have hklin : (k : ℝ) ≤ (k : ℝ)^p := by nlinarith
  nlinarith

end
end HierarchicalAbsoluteSpectral
