import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLift
import HierarchicalAbsoluteSpectral.ThresholdInertiaBridge

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix

def exactGramNegatedShiftDiagonal {k : ℕ} (Hc : Core k) (t : ℝ)
    (out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc)) :
    FiniteCongruenceDiagonal (Hc-t • (1 : Core k)) where
  basis := out.basis
  inverse := out.inverse
  diagonal := fun i => -out.diagonal i
  left_inverse := out.left_inverse
  right_inverse := out.right_inverse
  congruence := by
    calc
      _ = -(out.basisᵀ*(t • (1 : Core k)-Hc)*out.basis) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul]
        module
      _ = -Matrix.diagonal out.diagonal := congrArg Neg.neg out.congruence
      _ = _ := by ext i j; by_cases hij : i=j <;> simp [Matrix.diagonal_apply, hij]

theorem exactGramNegatedShiftDiagonal_positiveCount {k : ℕ} (Hc : Core k) (t : ℝ)
    (out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc)) :
    (exactGramNegatedShiftDiagonal Hc t out).positiveCount = out.negativeCount := by
  simp only [FiniteCongruenceDiagonal.positiveCount, FiniteCongruenceDiagonal.negativeCount,
    exactGramNegatedShiftDiagonal, neg_pos]

theorem exactGramAppendixLift_negativeCount_le {k : ℕ}
    (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc))
    (r : ℕ) (hr : r < k) (heigen : orderedEigenvalue Hc hHc ⟨r,hr⟩ ≤ t) :
    out.negativeCount ≤ r := by
  have hh := (exactGramNegatedShiftDiagonal Hc t out).shifted_eigenvalue_gt_iff
    Hc hHc t ⟨r,hr⟩
  rw [exactGramNegatedShiftDiagonal_positiveCount] at hh
  have hnot : ¬r < out.negativeCount := by
    intro hlt
    have hb := hh.mpr hlt
    exact (not_lt_of_ge heigen) hb
  omega

end
end HierarchicalAbsoluteSpectral
