import HierarchicalAbsoluteSpectral.StrongAction
import Mathlib.Tactic.NoncommRing

/-!
The deterministic last step in the strong Gaussian filter argument. A
finite right-inverse candidate approximating the strong spectral projector
is turned into the actual operator-norm residual used by `StrongAction`.
No quadratic or operator residual certificate is assumed here.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k w r : ℕ}

theorem filter_graph_identity {h t : ℕ}
    (J : Matrix (Fin k) (Fin h) ℝ) (L : Matrix (Fin k) (Fin t) ℝ)
    (Dh : Core h) (Dt : Core t)
    (Ωh : Matrix (Fin h) (Fin r) ℝ) (Ωt : Matrix (Fin t) (Fin r) ℝ)
    (H : Matrix (Fin r) (Fin h) ℝ) (F : Matrix (Fin h) (Fin k) ℝ)
    (hH : Ωh*H = 1) :
    J*(Dh*F)-(J*(Dh*Ωh)+L*(Dt*Ωt))*(H*F) = -(L*(Dt*(Ωt*H))*F) := by
  have hc : J*(Dh*Ωh)*(H*F) = J*(Dh*F) := by
    calc
      _ = J*(Dh*((Ωh*H)*F)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hH, Matrix.one_mul]
  rw [Matrix.add_mul, hc]
  simp only [Matrix.mul_assoc]
  module

theorem filter_graph_norm_bound {h t : ℕ}
    (J : Matrix (Fin k) (Fin h) ℝ) (L : Matrix (Fin k) (Fin t) ℝ)
    (Dh : Core h) (Dt : Core t)
    (Ωh : Matrix (Fin h) (Fin r) ℝ) (Ωt : Matrix (Fin t) (Fin r) ℝ)
    (H : Matrix (Fin r) (Fin h) ℝ) (F : Matrix (Fin h) (Fin k) ℝ)
    (d R : ℝ) (hd : 0 ≤ d) (hR : 0 ≤ R) (hH : Ωh*H = 1)
    (hL : ‖L‖ ≤ 1) (hDt : ‖Dt‖ ≤ d) (hΩ : ‖Ωt*H‖ ≤ R) (hF : ‖F‖ ≤ 1) :
    ‖J*(Dh*F)-(J*(Dh*Ωh)+L*(Dt*Ωt))*(H*F)‖ ≤ d*R := by
  rw [filter_graph_identity J L Dh Dt Ωh Ωt H F hH, norm_neg]
  calc
    _ ≤ ‖L*(Dt*(Ωt*H))‖*‖F‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖L‖*(‖Dt‖*‖Ωt*H‖))*‖F‖ := by
      gcongr
      exact (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*(d*R))*1 := by gcongr
    _ = d*R := by ring

theorem orthogonal_complement_norm_le_one (U : Matrix (Fin k) (Fin w) ℝ)
    (hU : Uᵀ*U = 1) : ‖(1 : Core k)-U*Uᵀ‖ ≤ 1 := by
  have h := projection_error_of_complement_bound (1 : Core k) U hU 1 (by norm_num)
    (fun x _ => by simp)
  simpa using h

/-- An approximate strong-space right inverse yields the paper's strong
operator residual. `Y=U*W` is the actual filtered span, including rank loss. -/
theorem strong_filter_residual_of_right_inverse
    (T P : Core k) (Y : Matrix (Fin k) (Fin r) ℝ)
    (X : Matrix (Fin r) (Fin k) ℝ) (U : Matrix (Fin k) (Fin w) ℝ)
    (W : Matrix (Fin w) (Fin r) ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hU : Uᵀ*U = 1) (hspan : Y = U*W) (hcomm : P*T = T*P)
    (happrox : ‖P-Y*X‖ ≤ α/2) (hT : ‖T‖ ≤ 2)
    (hweak : ‖T*(1-P)‖ ≤ 1+2*α) :
    ‖((1 : Core k)-U*Uᵀ)*T‖ ≤ 1+3*α := by
  let E : Core k := 1-U*Uᵀ
  have hE : ‖E‖ ≤ 1 := orthogonal_complement_norm_le_one U hU
  have hEY : E*Y = 0 := by
    rw [hspan]
    simp [E, Matrix.sub_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hU]
  have hEP : E*(P-Y*X) = E*P := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc E Y, hEY, Matrix.zero_mul, sub_zero]
  have heq : E*T = E*(P-Y*X)*T + E*(T*(1-P)) := by
    rw [hEP]
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc E P T, hcomm]
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖E*(P-Y*X)*T‖+‖E*(T*(1-P))‖ := norm_add_le _ _
    _ ≤ (‖E‖*‖P-Y*X‖)*‖T‖+‖E‖*‖T*(1-P)‖ := by
      exact add_le_add ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_mul_le _ _)
    _ ≤ (1*(α/2))*2+1*(1+2*α) := by gcongr
    _ = 1+3*α := by ring

end
end HierarchicalAbsoluteSpectral
