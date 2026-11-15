import HierarchicalAbsoluteSpectral.BaseCore
import HierarchicalAbsoluteSpectral.CholeskyFinite

/-! The base metric from a fully specified finite field-and-square-root
Cholesky construction and a finite Newton iteration. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

def finiteBaseMetric (D K0 : Core k) (hD : D.PosDef) (h : ℝ) (hh : 0 < h) : Core k :=
  baseCoreMetric (finiteCholesky k D hD).upper K0 h hh

theorem finite_base_invariant (D K0 K : Core k) (hD : D.PosDef) (h : ℝ)
    (hK0 : K0ᵀ = K0) (hK : Kᵀ = K) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hK0lo : -D ≤ K0) (hK0up : K0 ≤ D)
    (helo : -((2*h) • D) ≤ K-K0) (heup : K-K0 ≤ (2*h) • D) :
    let F := finiteBaseMetric D K0 hD h hh
    F.PosDef ∧ (8*h) • D ≤ F ∧ F ≤ (2:ℝ) • D ∧
      (6*h) • D ≤ F-K ∧ (6*h) • D ≤ F+K ∧
      (F-K).PosDef ∧ (F+K).PosDef ∧
      (0 : Core k) ≤ F-K*F⁻¹*K ∧ F-K*F⁻¹*K ≤ (36*h) • D := by
  exact base_core_invariant _ D K0 K h
    ((Matrix.isUnit_iff_isUnit_det _).mp (finiteCholesky k D hD).isUnit)
    (finiteCholesky k D hD).gram hK0 hK hh hh' hK0lo hK0up helo heup

theorem finiteBaseMetric_posDef (D K0 : Core k) (hD : D.PosDef) (hK0 : K0ᵀ = K0)
    (h : ℝ) (hh : 0 < h) : (finiteBaseMetric D K0 hD h hh).PosDef := by
  let J := (finiteCholesky k D hD).upper
  have hf := baseNewtonMetric_posDef (baseNormalized J K0)
    (normalized_isHermitian J⁻¹ K0 hK0) h hh (baseNewtonSteps h hh)
  have hi : Function.Injective J.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (finiteCholesky k D hD).isUnit
  simpa only [finiteBaseMetric, baseCoreMetric, J,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hf.conjTranspose_mul_mul_same hi

def finiteBaseInverseFactor (D K0 : Core k) (hD : D.PosDef) (hK0 : K0ᵀ = K0)
    (h : ℝ) (hh : 0 < h) : Core k :=
  (finiteCholesky k (finiteBaseMetric D K0 hD h hh)
    (finiteBaseMetric_posDef D K0 hD hK0 h hh)).inverse

theorem finiteBaseInverseFactor_isUnit (D K0 : Core k) (hD : D.PosDef)
    (hK0 : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    IsUnit (finiteBaseInverseFactor D K0 hD hK0 h hh).det := by
  let p := finiteCholesky k (finiteBaseMetric D K0 hD h hh)
    (finiteBaseMetric_posDef D K0 hD hK0 h hh)
  change IsUnit p.inverse.det
  rw [p.inverse_eq]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_nonsing_inv_iff.mpr p.isUnit)

theorem finiteBaseInverseFactor_metric (D K0 : Core k) (hD : D.PosDef)
    (hK0 : K0ᵀ = K0) (h : ℝ) (hh : 0 < h) :
    inverseMetric (finiteBaseInverseFactor D K0 hD hK0 h hh) = finiteBaseMetric D K0 hD h hh := by
  let p := finiteCholesky k (finiteBaseMetric D K0 hD h hh)
    (finiteBaseMetric_posDef D K0 hD hK0 h hh)
  letI := p.isUnit.invertible
  change (p.inverse⁻¹)ᵀ*p.inverse⁻¹ = _
  rw [p.inverse_eq, Matrix.inv_inv_of_invertible]
  exact p.gram

end
end HierarchicalAbsoluteSpectral
