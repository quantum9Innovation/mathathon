import HierarchicalAbsoluteSpectral.MinMaxScale
import HierarchicalAbsoluteSpectral.ProbabilityInitializerCorrectness

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder
variable {k : ℕ}

/-- Coarse constant factors suffice for the positive initializer. The
near-threshold and final error proofs continue to use the sharp mass bounds. -/
theorem initializer_mass_comparison (Q Q₀ Rb : Core k)
    (hQ : Q.PosSemidef) (hQ₀ : Q₀.IsHermitian) (hRb : IsUnit Rb.det)
    (hQlo : (1/2:ℝ) • Q ≤ Q₀) (hQup : Q₀ ≤ (2:ℝ) • Q)
    (hBlo : (1/2:ℝ) • (1 : Core k) ≤ inverseMetric Rb)
    (hBup : inverseMetric Rb ≤ (2:ℝ) • (1 : Core k)) (j : Fin k) :
    orderedEigenvalue Q₀ hQ₀ j/4 ≤
      orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.isHermitian.eq) j ∧
    orderedEigenvalue (Rbᵀ*Q*Rb) (normalized_isHermitian Rb Q hQ.isHermitian.eq) j ≤
      4*orderedEigenvalue Q₀ hQ₀ j := by
  have hqlo := orderedEigenvalue_mono ((1/2:ℝ) • Q) Q₀
    (hQ.isHermitian.smul (by simp [IsSelfAdjoint])) hQ₀ hQlo j
  have hqup := orderedEigenvalue_mono Q₀ ((2:ℝ) • Q) hQ₀
    (hQ.isHermitian.smul (by simp [IsSelfAdjoint])) hQup j
  rw [orderedEigenvalue_smul_nonneg Q hQ.isHermitian (1/2) (by norm_num) j] at hqlo
  rw [orderedEigenvalue_smul_nonneg Q hQ.isHermitian 2 (by norm_num) j] at hqup
  have hmlo := generalizedEigenvalue_lower Q (1 : Core k) Rb hQ (by simp) hRb 2 (by norm_num)
    (by simpa only [inverseMetric,inv_one,Matrix.transpose_one,Matrix.one_mul] using hBup) j
  have hBrev : inverseMetric (1 : Core k) ≤ (2:ℝ) • inverseMetric Rb := by
    have hh := smul_le_smul_of_nonneg_left hBlo (by norm_num : (0:ℝ)≤2)
    norm_num only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] at hh
    simpa only [inverseMetric,inv_one,Matrix.transpose_one,Matrix.one_mul] using hh
  have hmup := generalizedEigenvalue_lower Q Rb (1 : Core k) hQ hRb (by simp) 2 (by norm_num) hBrev j
  simp only [Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one] at hmlo hmup
  constructor <;> nlinarith only [hqlo,hqup,hmlo,hmup]

theorem initializer_widened_mass_bracket
    (mu0 target l u : ℝ) (hl : 0<l) (hlo : l ≤ mu0) (hhi : mu0 ≤ u)
    (hcompare : mu0/4 ≤ target ∧ target ≤ 4*mu0) :
    0<l/4 ∧ l/4≤target ∧ target≤4*u := by
  refine ⟨by positivity,?_,?_⟩ <;> linarith

theorem initializer_widened_ratio (l u C : ℝ) (hl : 0<l) (hratio : u/l=C) :
    (4*u)/(l/4)=16*C := by
  rw [← hratio]
  field_simp
  <;> ring

end
end HierarchicalAbsoluteSpectral
