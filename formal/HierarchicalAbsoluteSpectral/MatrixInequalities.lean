import HierarchicalAbsoluteSpectral.Scalars
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Module

set_option maxHeartbeats 1000000

/-!
Real symmetric matrix inequalities. The scope `MatrixOrder` is essential:
`A ≤ B` means `(B - A).PosSemidef`, exactly the paper's Loewner order.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {k : ℕ}
abbrev Core (k : ℕ) := Matrix (Fin k) (Fin k) ℝ

def quadratic (A : Core k) (x : Fin k → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

theorem quadratic_mono {A B : Core k} (hAB : A ≤ B) (x : Fin k → ℝ) :
    quadratic A x ≤ quadratic B x := by
  have h := (show (B - A).PosSemidef from hAB).dotProduct_mulVec_nonneg x
  simpa [quadratic, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using h

@[simp] theorem quadratic_sub (A B : Core k) (x : Fin k → ℝ) :
    quadratic (A - B) x = quadratic A x - quadratic B x := by
  simp [quadratic, Matrix.sub_mulVec, dotProduct_sub]

@[simp] theorem quadratic_add (A B : Core k) (x : Fin k → ℝ) :
    quadratic (A + B) x = quadratic A x + quadratic B x := by
  simp [quadratic, Matrix.add_mulVec, dotProduct_add]

@[simp] theorem quadratic_smul (a : ℝ) (A : Core k) (x : Fin k → ℝ) :
    quadratic (a • A) x = a * quadratic A x := by
  simp [quadratic, Matrix.smul_mulVec, dotProduct_smul]

theorem quadratic_nonneg {A : Core k} (hA : A.PosSemidef) (x : Fin k → ℝ) :
    0 ≤ quadratic A x := by
  simpa [quadratic] using hA.dotProduct_mulVec_nonneg x

/-- Inversion reverses Loewner order on positive definite real matrices. -/
theorem inverse_order {A B : Core k} (hA : A.PosDef) (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hdiff : (B - A).PosSemidef := hAB
  have hB : B.PosDef := by simpa using hA.add_posSemidef hdiff
  cases hA.isUnit.nonempty_invertible
  cases hB.isUnit.nonempty_invertible
  have hbase : (fromBlocks A (1 : Core k) 1 A⁻¹).PosSemidef := by
    simpa using (Matrix.PosDef.fromBlocks₁₁ (1 : Core k) A⁻¹ hA).mpr
      (by simpa using (Matrix.PosSemidef.zero : (0 : Core k).PosSemidef))
  let J : Matrix (Fin k) (Fin k ⊕ Fin k) ℝ :=
    fun i j => Sum.elim (fun j => (1 : Core k) i j) (fun _ => 0) j
  have hdiag : (fromBlocks (B - A) (0 : Core k) 0 0).PosSemidef := by
    convert hdiff.conjTranspose_mul_mul_same J using 1
    ext i j
    cases i <;> cases j <;>
      simp [J, Matrix.mul_apply, Matrix.one_apply]
  have hblock : (fromBlocks B (1 : Core k) 1 A⁻¹).PosSemidef := by
    convert hbase.add hdiag using 1
    rw [fromBlocks_add]
    congr 1 <;> module
  have hschur := (Matrix.PosDef.fromBlocks₁₁ (1 : Core k) A⁻¹ hB).mp (by simpa using hblock)
  simpa [Matrix.le_iff] using hschur

/-- Lemma 3, with its noncommuting congruence and ordinary matrix inverses. -/
theorem relative_perturbation
    (Fstar Fbar K D : Core k) (δ κ C h : ℝ)
    (hstar : Fstar.PosDef) (hbar : Fbar.PosDef) (hK : Kᵀ = K)
    (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hupper : Fbar ≤ (1 + δ) • Fstar)
    (hinvariant : Fstar - κ • (K * Fstar⁻¹ * K) ≤ (C * h) • D) :
    Fbar - (κ * (1 + δ)^2) • (K * Fbar⁻¹ * K) ≤
      (1 + δ) • (Fstar - κ • (K * Fstar⁻¹ * K)) ∧
    (1 + δ) • (Fstar - κ • (K * Fstar⁻¹ * K)) ≤
      ((1 + δ) * C * h) • D := by
  have ha : 0 < 1 + δ := by linarith
  letI : Invertible (1 + δ) := invertibleOfNonzero ha.ne'
  have hinv := inverse_order hbar hupper
  rw [Matrix.inv_smul _ _ ((Matrix.isUnit_iff_isUnit_det Fstar).mp hstar.isUnit),
    invOf_eq_inv] at hinv
  have hcong := star_left_conjugate_le_conjugate hinv K
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, hK,
    Matrix.mul_smul, Matrix.smul_mul] at hcong
  constructor
  · calc
      Fbar - (κ * (1 + δ)^2) • (K * Fbar⁻¹ * K) ≤
          (1 + δ) • Fstar -
            (κ * (1 + δ)^2) • ((1 + δ)⁻¹ • (K * Fstar⁻¹ * K)) :=
        sub_le_sub hupper (smul_le_smul_of_nonneg_left hcong (by positivity))
      _ = (1 + δ) • (Fstar - κ • (K * Fstar⁻¹ * K)) := by
        simp only [smul_smul, smul_sub]
        congr 1
        congr 1
        field_simp
  · simpa [smul_smul, mul_assoc] using
      smul_le_smul_of_nonneg_left hinvariant ha.le

/-- The key dual-complement inequality from Lemma 6, expressed on any vector. -/
theorem relaxed_strong_action_transfer
    (F K D : Core k) (κ C h b : ℝ)
    (hF : F.PosDef) (hK : Kᵀ = K)
    (hb : 0 ≤ b) (hκb : κ * b ≤ 1)
    (hinvariant : F - κ • (K * F⁻¹ * K) ≤ (C * h) • D)
    (y : Fin k → ℝ)
    (hstrong : quadratic (K * F⁻¹ * K) y - 2 * quadratic K y ≤
      b * quadratic F y) :
    -(b * C * h * quadratic D y) ≤ 2 * quadratic K y := by
  have hpsd : (K * F⁻¹ * K).PosSemidef := by
    simpa [hK] using hF.posSemidef.inv.conjTranspose_mul_mul_same K
  apply relaxed_strong_transfer_scalar (quadratic F y) (quadratic K y)
    (quadratic (K * F⁻¹ * K) y) (quadratic D y) κ C h b
    (quadratic_nonneg hpsd y) hb hκb
  · simpa using quadratic_mono hinvariant y
  · exact hstrong

theorem quadratic_congruence {n : ℕ} (A : Core k)
    (Z : Matrix (Fin n) (Fin k) ℝ) (x : Fin n → ℝ) :
    quadratic (Z * A * Zᵀ) x = quadratic A (Zᵀ *ᵥ x) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
    ← Matrix.mulVec_transpose]

/-- Equation (13), as the physical Rayleigh bound before taking the operator norm.
The mass and D inequalities are the three physical estimates in Lemma 6.
This version uses the sharper `u = b*C*h`; the paper replaces b by 7*alpha.
-/
theorem physical_transfer_rayleigh {n p : ℕ}
    (M : Matrix (Fin n) (Fin p) ℝ) (Z : Matrix (Fin n) (Fin k) ℝ)
    (F K D Bm : Core k) (κ C h b t ε : ℝ)
    (hF : F.PosDef) (hK : Kᵀ = K)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (hκb : κ * b ≤ 1) (hu : b * C * h < 1)
    (hinvariant : F - κ • (K * F⁻¹ * K) ≤ (C * h) • D)
    (hidentity : Z * K * Zᵀ = t • (Z * Bm * Zᵀ) - M * Mᵀ)
    (hmass : Z * Bm * Zᵀ ≤ (1 + ε) • (1 : Core n))
    (hD : Z * D * Zᵀ ≤ (2 * t) • (1 : Core n) + (2 : ℝ) • (M * Mᵀ))
    (x : Fin n → ℝ)
    (hstrong : quadratic (K * F⁻¹ * K) (Zᵀ *ᵥ x) -
        2 * quadratic K (Zᵀ *ᵥ x) ≤ b * quadratic F (Zᵀ *ᵥ x)) :
    quadratic (M * Mᵀ) x ≤
      ((1 + b * C * h + ε) / (1 - b * C * h)) * t * quadratic 1 x := by
  have htransfer := relaxed_strong_action_transfer F K D κ C h b hF hK
    hb hκb hinvariant (Zᵀ *ᵥ x) hstrong
  have hmassx := quadratic_mono hmass x
  have hDx := quadratic_mono hD x
  have hidentityx := congrArg (fun A => quadratic A x) hidentity
  simp only [quadratic_sub, quadratic_smul, quadratic_add, quadratic_congruence]
    at hmassx hDx hidentityx
  apply physical_transfer_scalar _ _ _ (b * C * h) ε hu
  have hm := mul_le_mul_of_nonneg_left hmassx ht
  have hd := mul_le_mul_of_nonneg_left hDx (show 0 ≤ b * C * h by positivity)
  nlinarith

end
end HierarchicalAbsoluteSpectral
