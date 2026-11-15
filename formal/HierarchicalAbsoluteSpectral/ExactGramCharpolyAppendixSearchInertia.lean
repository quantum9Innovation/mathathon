import HierarchicalAbsoluteSpectral.ThresholdInertiaBridge

/-! The exact negative-pivot bound required by the appendix lift after an
upward shift above the target eigenvalue. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix

theorem exactGramAppendix_shifted_negativeCount_le {n : ℕ}
    (A : Core n) (hA : A.IsHermitian) (t : ℝ)
    (out : FiniteCongruenceDiagonal (t • (1 : Core n)-A)) (j : Fin n)
    (hbound : orderedEigenvalue A hA j ≤ t) :
    out.negativeCount ≤ j.val := by
  let reversed : FiniteCongruenceDiagonal (A-t • (1 : Core n)) := {
    basis := out.basis
    inverse := out.inverse
    diagonal := fun i => -out.diagonal i
    left_inverse := out.left_inverse
    right_inverse := out.right_inverse
    congruence := by
      calc
        out.basisᵀ*(A-t • (1 : Core n))*out.basis =
            -(out.basisᵀ*(t • (1 : Core n)-A)*out.basis) := by
          rw [show A-t • (1 : Core n) = -(t • (1 : Core n)-A) from (neg_sub _ _).symm,
            Matrix.mul_neg, Matrix.neg_mul]
        _ = -Matrix.diagonal out.diagonal := congrArg Neg.neg out.congruence
        _ = Matrix.diagonal (fun i => -out.diagonal i) := by rw [← Matrix.diagonal_neg] }
  have hiff := reversed.shifted_eigenvalue_gt_iff A hA t j
  have hcount : reversed.positiveCount ≤ j.val := by
    apply Nat.le_of_not_gt
    intro hj
    exact not_lt_of_ge hbound (hiff.mpr hj)
  simpa only [FiniteCongruenceDiagonal.positiveCount,
    FiniteCongruenceDiagonal.negativeCount, reversed, neg_pos] using hcount

end
end HierarchicalAbsoluteSpectral
