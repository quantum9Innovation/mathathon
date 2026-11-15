import HierarchicalAbsoluteSpectral.BasePerturbation

/-!
The complete physical base invariant after a finite factorization of D.
The construction normalizes using that factor, executes the finite Newton
iteration, and conjugates back. The factor is supplied by the finite
Cholesky construction, not by an analytical square-root operation.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k : ℕ}

def baseNormalized (J A : Core k) : Core k := (J⁻¹)ᵀ*A*J⁻¹

def baseCoreMetric (J K0 : Core k) (h : ℝ) (hh : 0 < h) : Core k :=
  Jᵀ*baseNewtonMetric (baseNormalized J K0) h (baseNewtonSteps h hh)*J

theorem baseNormalized_one (J D : Core k) (hJ : IsUnit J.det) (hD : Jᵀ*J = D) :
    baseNormalized J D = 1 := by
  rw [baseNormalized, ← hD]
  calc
    _ = (J*J⁻¹)ᵀ*(J*J⁻¹) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv J hJ]; simp

theorem baseNormalized_undo (J A : Core k) (hJ : IsUnit J.det) :
    Jᵀ*baseNormalized J A*J = A := by
  rw [baseNormalized]
  calc
    _ = (J⁻¹*J)ᵀ*A*(J⁻¹*J) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = A := by rw [Matrix.nonsing_inv_mul J hJ]; simp

theorem normalized_norm_of_bounds (E : Core k) (hE : Eᵀ = E) (a : ℝ) (ha : 0 < a)
    (hl : -(a • (1 : Core k)) ≤ E) (hu : E ≤ a • (1 : Core k)) : ‖E‖ ≤ a := by
  have hs := weighted_error_square (1 : Core k) E a Matrix.PosDef.one hE ha hl hu
  have hsq : E*Eᵀ ≤ (a^2) • (1 : Core k) := by simpa only [inv_one, Matrix.mul_one, hE] using hs
  apply spectral_norm_le_of_rayleigh E a ha.le
  intro x
  simpa only [quadratic_smul] using quadratic_mono hsq x

theorem base_core_invariant (J D K0 K : Core k) (h : ℝ)
    (hJ : IsUnit J.det) (hJD : Jᵀ*J = D) (hK0 : K0ᵀ = K0) (hK : Kᵀ = K)
    (hh : 0 < h) (hh' : h ≤ 1/64)
    (hK0lo : -D ≤ K0) (hK0up : K0 ≤ D)
    (helo : -((2*h) • D) ≤ K-K0) (heup : K-K0 ≤ (2*h) • D) :
    let F := baseCoreMetric J K0 h hh
    F.PosDef ∧ (8*h) • D ≤ F ∧ F ≤ (2:ℝ) • D ∧
      (6*h) • D ≤ F-K ∧ (6*h) • D ≤ F+K ∧
      (F-K).PosDef ∧ (F+K).PosDef ∧
      (0 : Core k) ≤ F-K*F⁻¹*K ∧ F-K*F⁻¹*K ≤ (36*h) • D := by
  let S := baseNormalized J K0
  let E := baseNormalized J (K-K0)
  let Fb := baseNewtonMetric S h (baseNewtonSteps h hh)
  have hS : S.IsHermitian := normalized_isHermitian J⁻¹ K0 hK0
  have hE : E.IsHermitian := normalized_isHermitian J⁻¹ (K-K0) (by simp [hK, hK0])
  have hslo := star_left_conjugate_le_conjugate hK0lo J⁻¹
  have hsup := star_left_conjugate_le_conjugate hK0up J⁻¹
  have helo' := star_left_conjugate_le_conjugate helo J⁻¹
  have heup' := star_left_conjugate_le_conjugate heup J⁻¹
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul] at hslo hsup helo' heup'
  change -baseNormalized J D ≤ S at hslo
  change S ≤ baseNormalized J D at hsup
  change -((2*h) • baseNormalized J D) ≤ E at helo'
  change E ≤ (2*h) • baseNormalized J D at heup'
  rw [baseNormalized_one J D hJ hJD] at hslo hsup helo' heup'
  have hspec : ∀ x ∈ spectrum ℝ S, -1 ≤ x ∧ x ≤ 1 := by
    have hl := (algebraMap_le_iff_le_spectrum (p := IsSelfAdjoint) hS).mp
      (show algebraMap ℝ (Core k) (-1) ≤ S by simpa using hslo)
    have hu := (le_algebraMap_iff_spectrum_le (p := IsSelfAdjoint) hS).mp
      (show S ≤ algebraMap ℝ (Core k) 1 by simpa using hsup)
    exact fun x hx => ⟨hl x hx, hu x hx⟩
  have hEt : Eᵀ = E := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hE.eq
  have heNorm := normalized_norm_of_bounds E hEt (2*h) (by positivity) helo' heup'
  have hn := finite_base_normalized S E hS hE h hh hh' hspec heNorm
  have hnorm : S+E = baseNormalized J K := by dsimp [S, E, baseNormalized]; noncomm_ring
  have hundo : Jᵀ*(S+E)*J = K := by rw [hnorm, baseNormalized_undo J K hJ]
  have hi : Function.Injective J.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det J).mpr hJ)
  have hF : (baseCoreMetric J K0 h hh).PosDef := by
    simpa only [baseCoreMetric, S, Fb, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hn.1.conjTranspose_mul_mul_same hi
  have hl := star_left_conjugate_le_conjugate hn.2.1 J
  have hu := star_left_conjugate_le_conjugate hn.2.2.1 J
  have hm := star_left_conjugate_le_conjugate hn.2.2.2.1 J
  have hp := star_left_conjugate_le_conjugate hn.2.2.2.2.1 J
  have hmPD := hn.2.2.2.2.2.1.conjTranspose_mul_mul_same hi
  have hpPD := hn.2.2.2.2.2.2.1.conjTranspose_mul_mul_same hi
  have hdlo := star_left_conjugate_le_conjugate hn.2.2.2.2.2.2.2.1 J
  have hdup := star_left_conjugate_le_conjugate hn.2.2.2.2.2.2.2.2 J
  have hdef := congruence_defect J (S+E) Fb hJ
  rw [hundo] at hdef
  change baseCoreMetric J K0 h hh-K*(baseCoreMetric J K0 h hh)⁻¹*K =
    Jᵀ*(Fb-(S+E)*Fb⁻¹*(S+E))*J at hdef
  have hmEq : Jᵀ*(Fb-(S+E))*J = baseCoreMetric J K0 h hh-K := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hundo]; rfl
  have hpEq : Jᵀ*(Fb+(S+E))*J = baseCoreMetric J K0 h hh+K := by
    rw [Matrix.mul_add, Matrix.add_mul, hundo]; rfl
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hJD] at hl hu hm hp hmPD hpPD hdlo hdup
  change (6*h) • D ≤ Jᵀ*(Fb-(S+E))*J at hm
  change (6*h) • D ≤ Jᵀ*(Fb+(S+E))*J at hp
  change (Jᵀ*(Fb-(S+E))*J).PosDef at hmPD
  change (Jᵀ*(Fb+(S+E))*J).PosDef at hpPD
  rw [hmEq] at hm hmPD
  rw [hpEq] at hp hpPD
  change (8*h) • D ≤ baseCoreMetric J K0 h hh at hl
  change baseCoreMetric J K0 h hh ≤ (2:ℝ) • D at hu
  change (6*h) • D ≤ baseCoreMetric J K0 h hh-K at hm
  change (6*h) • D ≤ baseCoreMetric J K0 h hh+K at hp
  change (baseCoreMetric J K0 h hh-K).PosDef at hmPD
  change (baseCoreMetric J K0 h hh+K).PosDef at hpPD
  rw [← hdef] at hdlo hdup
  simpa only [Matrix.mul_zero, Matrix.zero_mul] using
    And.intro hF (And.intro hl (And.intro hu (And.intro hm
      (And.intro hp (And.intro hmPD (And.intro hpPD (And.intro hdlo hdup)))))))

end
end HierarchicalAbsoluteSpectral
