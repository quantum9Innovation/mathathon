import HierarchicalAbsoluteSpectral.ThresholdInertiaBridge
import HierarchicalAbsoluteSpectral.ThresholdKrylovProgram

set_option backward.isDefEq.respectTransparency false

/-! A compiler from a counted congruence-diagonalization program to exact
shifted Ritz tests. The concrete elimination program is supplied at the
integration call; no eigenvalue instruction occurs in this program. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {k : ℕ}

abbrev InertiaProgramFamily := ∀ (n : ℕ) (D : Core n), D.IsHermitian →
  ArithmeticProgram (FiniteCongruenceDiagonal D)

structure CertifiedEigenvalueTest (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) where
  answer : Bool
  correct : answer = true ↔ c < orderedEigenvalue A hA j

def shiftedMatrixProgram (A : Core k) (c : ℝ) : ArithmeticProgram (Core k) := do
  let scalar ← blockScaleProgram c (1 : Core k)
  blockSubProgram A scalar

@[simp] theorem shiftedMatrixProgram_eval (A : Core k) (c : ℝ) :
    (shiftedMatrixProgram A c).eval = A-c • (1 : Core k) := by
  simp only [shiftedMatrixProgram, eval_bind, blockScaleProgram_eval, blockSubProgram_eval]

@[simp] theorem shiftedMatrixProgram_work (A : Core k) (c : ℝ) :
    (shiftedMatrixProgram A c).work = 2*k*k := by
  simp only [shiftedMatrixProgram, work_bind, blockScaleProgram_work, blockSubProgram_work]
  ring

theorem shiftedMatrixProgram_admissible (A : Core k) (c : ℝ) :
    (shiftedMatrixProgram A c).admissible := by
  simp only [shiftedMatrixProgram, admissible_bind, blockScaleProgram_admissible,
    blockSubProgram_admissible, and_self]

def shiftedEigenvalueTestProgram (inertia : InertiaProgramFamily)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) :
    ArithmeticProgram (CertifiedEigenvalueTest A hA c j) := do
  let shifted ← (shiftedMatrixProgram A c).certify
  have hshift : shifted.val = A-c • (1 : Core k) := shifted.property.trans (shiftedMatrixProgram_eval A c)
  let out ← inertia k shifted.val (by rw [hshift]; exact shifted_isHermitian A hA c)
  let answer ← (ArithmeticProgram.compare ((j.val+1 : ℕ) : ℝ) (out.positiveCount : ℝ)
    ArithmeticProgram.pure).certify
  let out' : FiniteCongruenceDiagonal (A-c • (1 : Core k)) :=
    { basis := out.basis
      inverse := out.inverse
      diagonal := out.diagonal
      left_inverse := out.left_inverse
      right_inverse := out.right_inverse
      congruence := by rw [← hshift]; exact out.congruence }
  have hb : answer.val = true ↔ j.val < out'.positiveCount := by
    rw [answer.property]
    simp only [ArithmeticProgram.eval, decide_eq_true_eq, Nat.cast_le, Nat.succ_le_iff]
    rfl
  .pure ⟨answer.val,hb.trans (out'.shifted_eigenvalue_gt_iff A hA c j).symm⟩

theorem shiftedEigenvalueTestProgram_admissible (inertia : InertiaProgramFamily)
    (hInertia : ∀ n D hD, (inertia n D hD).admissible)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) :
    (shiftedEigenvalueTestProgram inertia A hA c j).admissible := by
  simp only [shiftedEigenvalueTestProgram, admissible_bind, certify_admissible,
    shiftedMatrixProgram_admissible, hInertia, ArithmeticProgram.admissible,
    admissible_pure, and_self]

theorem shiftedEigenvalueTestProgram_work_le (inertia : InertiaProgramFamily)
    (cost : ℕ → ℕ) (hInertia : ∀ n D hD, (inertia n D hD).work ≤ cost n)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) :
    (shiftedEigenvalueTestProgram inertia A hA c j).work ≤ 2*k*k+cost k+1 := by
  simp only [shiftedEigenvalueTestProgram, work_bind, certify_work, shiftedMatrixProgram_work,
    ArithmeticProgram.work, work_pure, add_zero]
  have hh := hInertia k (shiftedMatrixProgram A c).certify.eval.val
    (by rw [(shiftedMatrixProgram A c).certify.eval.property, shiftedMatrixProgram_eval];
        exact shifted_isHermitian A hA c)
  omega

end
end HierarchicalAbsoluteSpectral
