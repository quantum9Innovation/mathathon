import HierarchicalAbsoluteSpectral.Refinement

/-!
Derive the physical pencil identity and the mass/D bounds used by the
spectral transfer. The inputs are a product-support factorization, its Gram
matrix and the coarse Loewner estimates, not physical-error certificates.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k n p : ℕ}

theorem rectangular_congruence_mono (A B : Core k) (hAB : A ≤ B)
    (Z : Matrix (Fin n) (Fin k) ℝ) : Z*A*Zᵀ ≤ Z*B*Zᵀ := by
  have hd : (B-A).PosSemidef := hAB
  have hc := hd.mul_mul_conjTranspose_same Z
  simpa [Matrix.le_iff, Matrix.mul_sub, Matrix.sub_mul] using hc

theorem gram_projection_le_one (Z : Matrix (Fin n) (Fin k) ℝ)
    (hG : (Zᵀ*Z).PosDef) : Z*(Zᵀ*Z)⁻¹*Zᵀ ≤ (1 : Core n) := by
  let W : Matrix (Fin n) (Fin k ⊕ Fin n) ℝ :=
    fun i j => Sum.elim (fun j => Z i j) (fun j => (1 : Core n) i j) j
  have hgram : (Matrix.fromBlocks (Zᵀ*Z) Zᵀ Z (1 : Core n)).PosSemidef := by
    convert Matrix.posSemidef_conjTranspose_mul_self W using 1
    ext i j
    cases i <;> cases j <;> simp [W, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  letI := hG.isUnit.invertible
  have hs := (Matrix.PosDef.fromBlocks₁₁ Zᵀ (1 : Core n) hG).mp
    (by simpa using hgram)
  simpa [Matrix.le_iff] using hs

/-- The two Gram matrices have the same scalar upper bound, even when Z is
rectangular and rank deficient. This follows from the two Schur complements
of the same positive block matrix.
-/
theorem outer_gram_bound (Z : Matrix (Fin n) (Fin k) ℝ) (a : ℝ) (ha : 0 < a)
    (hinner : Zᵀ*Z ≤ a • (1 : Core k)) : Z*Zᵀ ≤ a • (1 : Core n) := by
  have hblock : (Matrix.fromBlocks (a • (1 : Core k)) Zᵀ Z (1 : Core n)).PosSemidef := by
    letI : Invertible (1 : Core n) := (isUnit_one : IsUnit (1 : Core n)).invertible
    simpa using (Matrix.PosDef.fromBlocks₂₂ (a • (1 : Core k)) Zᵀ
      (Matrix.PosDef.one : (1 : Core n).PosDef)).mpr
      (by simpa using (show (a • (1 : Core k) - Zᵀ*Z).PosSemidef from hinner))
  have hA : (a • (1 : Core k)).PosDef :=
    (IsStrictlyPositive.smul ha Matrix.PosDef.one.isStrictlyPositive).posDef
  letI : Invertible a := invertibleOfNonzero ha.ne'
  letI := hA.isUnit.invertible
  have hs := (Matrix.PosDef.fromBlocks₁₁ Zᵀ (1 : Core n) hA).mp
    (by simpa using hblock)
  rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv] at hs
  have ho : a⁻¹ • (Z*Zᵀ) ≤ (1 : Core n) := by
    simpa [Matrix.le_iff, Matrix.mul_smul, Matrix.smul_mul] using hs
  have hb := smul_le_smul_of_nonneg_left ho ha.le
  simpa [smul_smul, mul_inv_cancel₀ ha.ne'] using hb

theorem physical_mass_bound (Z : Matrix (Fin n) (Fin k) ℝ) (Bm : Core k)
    (ε : ℝ) (hε : 0 ≤ ε) (hG : (Zᵀ*Z).PosDef)
    (hmass : Bm ≤ (1+ε) • (Zᵀ*Z)⁻¹) :
    Z*Bm*Zᵀ ≤ (1+ε) • (1 : Core n) := by
  have hc := rectangular_congruence_mono Bm ((1+ε) • (Zᵀ*Z)⁻¹) hmass Z
  have hp := gram_projection_le_one Z hG
  apply hc.trans
  simpa [Matrix.mul_smul, Matrix.smul_mul] using
    smul_le_smul_of_nonneg_left hp (show 0 ≤ 1+ε by linarith)

theorem physical_pencil_identity (Z : Matrix (Fin n) (Fin k) ℝ)
    (B : Matrix (Fin k) (Fin p) ℝ) (Bm : Core k) (t : ℝ) :
    Z*(t • Bm - B*Bᵀ)*Zᵀ = t • (Z*Bm*Zᵀ) - (Z*B)*(Z*B)ᵀ := by
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

theorem physical_D_bound (Z : Matrix (Fin n) (Fin k) ℝ)
    (B : Matrix (Fin k) (Fin p) ℝ) (Q₀ : Core k) (t : ℝ) (ht : 0 ≤ t)
    (hG : Zᵀ*Z ≤ (2 : ℝ) • (1 : Core k)) (hQ : Q₀ ≤ (2 : ℝ) • (B*Bᵀ)) :
    Z*(t • (1 : Core k) + Q₀)*Zᵀ ≤
      (2*t) • (1 : Core n) + (2 : ℝ) • ((Z*B)*(Z*B)ᵀ) := by
  have hg := smul_le_smul_of_nonneg_left (outer_gram_bound Z 2 (by norm_num) hG) ht
  have hq := rectangular_congruence_mono Q₀ ((2 : ℝ) • (B*Bᵀ)) hQ Z
  have hs := add_le_add hg hq
  simpa [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.transpose_mul, Matrix.mul_assoc, smul_smul, mul_comm] using hs

end
end HierarchicalAbsoluteSpectral
