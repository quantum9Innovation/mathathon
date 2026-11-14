import HierarchicalAbsoluteSpectral.Spectral
import HierarchicalAbsoluteSpectral.InverseMetric
import Mathlib.Tactic.NoncommRing

/-!
Derive the quadratic strong-action certificate from the actual operator norm
of the filtered symmetric pencil. This supplies the strong-action input of
the spectral transfer; it is not an assumed quadratic residual.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k r : ℕ}

theorem spectral_norm_transpose {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℝ) :
    ‖Mᵀ‖ = ‖M‖ := by
  simpa using Matrix.l2_opNorm_conjTranspose M

theorem strong_action_quadratic
    (C : Core k) (U : Matrix (Fin k) (Fin r) ℝ) (c : ℝ)
    (hC : Cᵀ = C) (hc : 0 ≤ c)
    (hnorm : ‖(1 - U * Uᵀ) * (1 - C)‖ ≤ c)
    (v : Fin k → ℝ) (hv : Uᵀ *ᵥ v = 0) :
    quadratic (C * C) v - 2 * quadratic C v ≤ (c^2 - 1) * quadratic 1 v := by
  let E : Core k := 1 - U * Uᵀ
  let T : Core k := 1 - C
  have hET : Eᵀ = E := by simp [E, Matrix.transpose_mul]
  have hTT : Tᵀ = T := by simp [T, hC]
  have htrans : ‖T * E‖ ≤ c := by
    have heq : (E * T)ᵀ = T * E := by rw [Matrix.transpose_mul, hET, hTT]
    rw [← heq, spectral_norm_transpose]
    exact hnorm
  have hEv : E *ᵥ v = v := by
    simp [E, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv]
  have hm := Matrix.l2_opNorm_mulVec (T * E) (toLp 2 v)
  change ‖toLp 2 ((T * E) *ᵥ v)‖ ≤ ‖T * E‖ * ‖toLp 2 v‖ at hm
  rw [← Matrix.mulVec_mulVec, hEv] at hm
  have hTv : ‖toLp 2 (T *ᵥ v)‖ ≤ c * ‖toLp 2 v‖ :=
    hm.trans (mul_le_mul_of_nonneg_right htrans (norm_nonneg _))
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hTv
  have hqT : quadratic (T * T) v = ‖toLp 2 (T *ᵥ v)‖^2 := by
    have hq := quadratic_mul_transpose T v
    rw [hTT] at hq
    exact hq.trans (quadratic_one_norm (toLp 2 (T *ᵥ v)))
  have hqI := quadratic_one_norm (toLp 2 v)
  have hTTexpand : T * T = 1 - (C + C) + C * C := by
    dsimp [T]
    noncomm_ring
  rw [← hqT, mul_pow, ← hqI] at hsq
  rw [hTTexpand, quadratic_add, quadratic_sub, quadratic_add] at hsq
  nlinarith

def normalizedPencil (R K : Core k) : Core k := Rᵀ * K * R

/-- Undo the inverse-factor congruence in the strong residual, exactly as in
Lemma 6 with w=R^-1 y and F=R^-T R^-1.
-/
theorem strong_action_dual_certificate
    (R K : Core k) (U : Matrix (Fin k) (Fin r) ℝ) (c : ℝ)
    (hR : IsUnit R.det) (hK : Kᵀ = K) (hc : 0 ≤ c)
    (hnorm : ‖(1 - U * Uᵀ) * (1 - normalizedPencil R K)‖ ≤ c)
    (y : Fin k → ℝ) (hy : Uᵀ *ᵥ (R⁻¹ *ᵥ y) = 0) :
    quadratic (K * (inverseMetric R)⁻¹ * K) y - 2 * quadratic K y ≤
      (c^2 - 1) * quadratic (inverseMetric R) y := by
  have hC : (normalizedPencil R K)ᵀ = normalizedPencil R K := by
    simp [normalizedPencil, Matrix.transpose_mul, Matrix.mul_assoc, hK]
  have hbase := strong_action_quadratic (normalizedPencil R K) U c hC hc hnorm
    (R⁻¹ *ᵥ y) hy
  have hRy : R *ᵥ (R⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R hR, Matrix.one_mulVec]
  have hCq : quadratic (normalizedPencil R K) (R⁻¹ *ᵥ y) = quadratic K y := by
    have hq := quadratic_congruence K Rᵀ (R⁻¹ *ᵥ y)
    simpa [normalizedPencil, hRy] using hq
  have hCCq : quadratic (normalizedPencil R K * normalizedPencil R K) (R⁻¹ *ᵥ y) =
      quadratic (K * (inverseMetric R)⁻¹ * K) y := by
    have hm : normalizedPencil R K * normalizedPencil R K =
        Rᵀ * (K * (inverseMetric R)⁻¹ * K) * R := by
      rw [inverseMetric_inv R hR]
      simp [normalizedPencil, Matrix.mul_assoc]
    rw [hm]
    have hq := quadratic_congruence (K * (inverseMetric R)⁻¹ * K) Rᵀ (R⁻¹ *ᵥ y)
    simpa [hRy] using hq
  have hIq : quadratic (1 : Core k) (R⁻¹ *ᵥ y) = quadratic (inverseMetric R) y := by
    have hq := quadratic_congruence (1 : Core k) (R⁻¹)ᵀ y
    simpa [inverseMetric] using hq.symm
  rwa [hCq, hCCq, hIq] at hbase

/-- A physical orthonormalization with the same lifted column span preserves
the exact dual complement. `W` records the change of column coordinates.
-/
theorem physical_strong_action_certificate {n w : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℝ) (R K : Core k)
    (U : Matrix (Fin k) (Fin r) ℝ) (V : Matrix (Fin n) (Fin w) ℝ)
    (W : Matrix (Fin w) (Fin r) ℝ) (c : ℝ)
    (hR : IsUnit R.det) (hK : Kᵀ = K) (hc : 0 ≤ c)
    (hcolumns : Z * (R⁻¹)ᵀ * U = V * W)
    (hnorm : ‖(1 - U * Uᵀ) * (1 - normalizedPencil R K)‖ ≤ c)
    (x : Fin n → ℝ) (hx : Vᵀ *ᵥ x = 0) :
    quadratic (K * (inverseMetric R)⁻¹ * K) (Zᵀ *ᵥ x) -
        2 * quadratic K (Zᵀ *ᵥ x) ≤
      (c^2 - 1) * quadratic (inverseMetric R) (Zᵀ *ᵥ x) := by
  apply strong_action_dual_certificate R K U c hR hK hc hnorm
  have horth := congrArg (fun A => Aᵀ *ᵥ x) hcolumns
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero] using horth

end
end HierarchicalAbsoluteSpectral
