import HierarchicalAbsoluteSpectral.MassSpectrumSingular

/-! Exact support-to-physical spectral bridge. The theorem refers directly to
the manuscript's `M = Z Bcal`, `G = Zᵀ Z`, and `Q = Bcal Bcalᵀ`, and to the
same `tailSingularValue` used in the final approximation theorem. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {n k p : ℕ}

theorem support_mass_eigenvalue_eq_sq_tail
    (Z : Matrix (Fin n) (Fin k) ℝ) (Bcal : Matrix (Fin k) (Fin p) ℝ)
    (hG : (Zᵀ*Z).PosDef) (j : Fin k) (hjp : j.val < p) :
    massEigenvalue (Bcal*Bcalᵀ) (Zᵀ*Z)⁻¹
      (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.posSemidef_self_mul_conjTranspose Bcal).isHermitian) j =
      tailSingularValue (Z*Bcal) j.val^2 := by
  let G := Zᵀ*Z
  let Q := Bcal*Bcalᵀ
  let X := CFC.sqrt G*Bcal
  have hQ : Q.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose Bcal
  have hgram : Xᵀ*X = (Z*Bcal)ᵀ*(Z*Bcal) := by
    calc
      Xᵀ*X = Bcalᵀ*(CFC.sqrt G*CFC.sqrt G)*Bcal := by
        simp only [X, Matrix.transpose_mul, massRoot_transpose, Matrix.mul_assoc]
      _ = Bcalᵀ*G*Bcal := by rw [CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
      _ = (Z*Bcal)ᵀ*(Z*Bcal) := by simp only [G, Matrix.transpose_mul, Matrix.mul_assoc]
  have hreverse : X*Xᵀ = CFC.sqrt G*Q*CFC.sqrt G := by
    simp only [X, Q, Matrix.transpose_mul, massRoot_transpose, Matrix.mul_assoc]
  have hs := sq_tailSingularValue_eq_reverseGram X j.val j.isLt hjp
  rw [tailSingularValue_eq_of_gram X (Z*Bcal) hgram j.val] at hs
  apply (massEigenvalue_inverse Q G hQ hG j).trans
  symm
  simpa only [hreverse] using hs

theorem support_approximate_mass_compare
    (Z : Matrix (Fin n) (Fin k) ℝ) (Bcal : Matrix (Fin k) (Fin p) ℝ) (Bm : Core k)
    (hG : (Zᵀ*Z).PosDef) (hBm : Bm.PosDef) (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε < 1)
    (hlo : (1-ε) • (Zᵀ*Z)⁻¹ ≤ Bm) (hhi : Bm ≤ (1+ε) • (Zᵀ*Z)⁻¹)
    (j : Fin k) (hjp : j.val < p) :
    tailSingularValue (Z*Bcal) j.val^2/(1+ε) ≤
      massEigenvalue (Bcal*Bcalᵀ) Bm
        (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          (Matrix.posSemidef_self_mul_conjTranspose Bcal).isHermitian) j ∧
    massEigenvalue (Bcal*Bcalᵀ) Bm
        (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          (Matrix.posSemidef_self_mul_conjTranspose Bcal).isHermitian) j ≤
      tailSingularValue (Z*Bcal) j.val^2/(1-ε) := by
  have hQ : (Bcal*Bcalᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose Bcal
  have hh := massEigenvalue_compare (Bcal*Bcalᵀ) (Zᵀ*Z)⁻¹ Bm hQ hG.inv hBm
    ε hε hε' hlo hhi j
  simpa only [support_mass_eigenvalue_eq_sq_tail Z Bcal hG j hjp] using hh

end
end HierarchicalAbsoluteSpectral
