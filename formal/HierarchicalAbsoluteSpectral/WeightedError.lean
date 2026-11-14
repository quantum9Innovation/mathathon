import HierarchicalAbsoluteSpectral.Refinement

/-!
Weighted normalization of a two-sided Loewner error. The proof uses a
positive block matrix and its Schur complement, with no commutation and no
matrix-square-root assumption. This supplies both error estimates of Lemma 5.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

theorem block_posSemidef_of_sum_sub (P E : Core k)
    (hplus : (P+E).PosSemidef) (hminus : (P-E).PosSemidef) :
    (Matrix.fromBlocks P E E P).PosSemidef := by
  let Jp : Matrix (Fin k) (Fin k ⊕ Fin k) ℝ :=
    fun i j => Sum.elim (fun j => (1 : Core k) i j) (fun j => (1 : Core k) i j) j
  let Jm : Matrix (Fin k) (Fin k ⊕ Fin k) ℝ :=
    fun i j => Sum.elim (fun j => (1 : Core k) i j) (fun j => -(1 : Core k) i j) j
  have hp := hplus.conjTranspose_mul_mul_same Jp
  have hm := hminus.conjTranspose_mul_mul_same Jm
  have hs := (hp.add hm).smul (show (0:ℝ) ≤ 1/2 by norm_num)
  convert hs using 1
  ext i j
  cases i <;> cases j <;>
    simp [Jp, Jm, Matrix.mul_apply, Matrix.one_apply] <;> ring

/-- A symmetric error in [-a D,a D] satisfies E D^-1 E <= a^2 D. -/
theorem weighted_error_square (D E : Core k) (a : ℝ)
    (hD : D.PosDef) (hE : Eᵀ = E) (ha : 0 < a)
    (hlow : -(a • D) ≤ E) (hupper : E ≤ a • D) :
    E * D⁻¹ * E ≤ (a^2) • D := by
  have hplus : (a • D + E).PosSemidef := by
    have hp : (E - -(a • D)).PosSemidef := hlow
    simpa [sub_neg_eq_add, add_comm] using hp
  have hminus : (a • D - E).PosSemidef := hupper
  have hblock := block_posSemidef_of_sum_sub (a • D) E hplus hminus
  have hPa : (a • D).PosDef :=
    (IsStrictlyPositive.smul ha hD.isStrictlyPositive).posDef
  letI : Invertible a := invertibleOfNonzero ha.ne'
  letI := hPa.isUnit.invertible
  have hschur := (Matrix.PosDef.fromBlocks₁₁ E (a • D) hPa).mp
    (by simpa [hE] using hblock)
  rw [Matrix.inv_smul _ _ ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit),
    invOf_eq_inv] at hschur
  have horder : a⁻¹ • (E * D⁻¹ * E) ≤ a • D := by
    simpa [Matrix.le_iff, Matrix.mul_smul, Matrix.smul_mul, hE] using hschur
  have hs := smul_le_smul_of_nonneg_left horder ha.le
  simpa [smul_smul, mul_inv_cancel₀ ha.ne', pow_two] using hs

/-- General weighted error bound from the physical Loewner floor of F. -/
theorem weighted_error_from_floor (D F E : Core k) (a c : ℝ)
    (hD : D.PosDef) (hE : Eᵀ = E) (ha : 0 < a) (hc : 0 < c)
    (hlow : -(a • D) ≤ E) (hupper : E ≤ a • D) (hfloor : c • D ≤ F) :
    E * F⁻¹ * E ≤ (a^2/c) • D := by
  have hPD : (c • D).PosDef :=
    (IsStrictlyPositive.smul hc hD.isStrictlyPositive).posDef
  have hinv := inverse_order hPD hfloor
  letI : Invertible c := invertibleOfNonzero hc.ne'
  rw [Matrix.inv_smul _ _ ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit),
    invOf_eq_inv] at hinv
  have hcong := star_left_conjugate_le_conjugate hinv E
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hE, Matrix.mul_smul, Matrix.smul_mul] at hcong
  have hbound := weighted_error_square D E a hD hE ha hlow hupper
  have hscaled := smul_le_smul_of_nonneg_left hbound (inv_pos.mpr hc).le
  apply hcong.trans
  simpa [smul_smul, div_eq_mul_inv, mul_comm] using hscaled

/-- The 8 h^2/H bound used to inflate the coarse invariant. -/
theorem fine_error_previous_metric (D F E : Core k) (h H : ℝ)
    (hD : D.PosDef) (hE : Eᵀ = E) (hh : 0 < h) (hH : 0 < H)
    (hlow : -((8*h) • D) ≤ E) (hupper : E ≤ (8*h) • D)
    (hfloor : (8*H) • D ≤ F) :
    E * F⁻¹ * E ≤ (8*h^2/H) • D := by
  have hb := weighted_error_from_floor D F E (8*h) (8*H) hD hE
    (by positivity) (by positivity) hlow hupper hfloor
  convert hb using 1
  congr 1
  field_simp

/-- The h/2 bound after constructing the ideal absolute-root metric. -/
theorem fine_error_ideal_metric (D F E : Core k) (h : ℝ)
    (hD : D.PosDef) (hE : Eᵀ = E) (hh : 0 < h)
    (hlow : -((8*h) • D) ≤ E) (hupper : E ≤ (8*h) • D)
    (hfloor : (128*h) • D ≤ F) :
    E * F⁻¹ * E ≤ (h/2) • D := by
  have hb := weighted_error_from_floor D F E (8*h) (128*h) hD hE
    (by positivity) (by positivity) hlow hupper hfloor
  convert hb using 1
  congr 1
  field_simp
  ring

end
end HierarchicalAbsoluteSpectral
