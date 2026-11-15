import HierarchicalAbsoluteSpectral.ThresholdSingularTests
import HierarchicalAbsoluteSpectral.InertiaSignCountProgram

/-! Explicitly counted pivot-sign tests for the appendix inertia query. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n : ℕ}

/-- The existing exact singular-shift elimination, followed by executed
sign comparisons, real counter additions, and the final rank comparison. -/
def exactGramAppendixShiftedEigenvalueTestProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.IsHermitian) (t : ℝ) (j : Fin n) (g : Fin (n*n) → ℝ) :
    ArithmeticProgram (Option (CertifiedEigenvalueTest A hA t j)) := do
  let shifted ← (shiftedMatrixProgram A t).certify
  have hshift : shifted.val = A-t • (1 : Core n) :=
    shifted.property.trans (shiftedMatrixProgram_eval A t)
  let out? ← singularInertiaFamily kernels n g n shifted.val
    (by rw [hshift]; exact shifted_isHermitian A hA t)
  match out? with
  | none => .pure none
  | some out => do
      let count ← (positiveDiagonalCountProgram out.diagonal).certify
      let answer ← (ArithmeticProgram.compare ((j.val+1 : ℕ) : ℝ) count.val
        ArithmeticProgram.pure).certify
      let out' : FiniteCongruenceDiagonal (A-t • (1 : Core n)) := {
        basis := out.basis
        inverse := out.inverse
        diagonal := out.diagonal
        left_inverse := out.left_inverse
        right_inverse := out.right_inverse
        congruence := by rw [← hshift]; exact out.congruence }
      have hb : answer.val = true ↔ j.val < out'.positiveCount := by
        rw [answer.property, count.property, positiveDiagonalCountProgram_eval]
        simp only [ArithmeticProgram.eval, decide_eq_true_eq, Nat.cast_le, Nat.succ_le_iff]
        rfl
      .pure (some ⟨answer.val, hb.trans (out'.shifted_eigenvalue_gt_iff A hA t j).symm⟩)

theorem exactGramAppendixShiftedEigenvalueTestProgram_eval
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.IsHermitian) (t : ℝ) (j : Fin n) (g : Fin (n*n) → ℝ) :
    (exactGramAppendixShiftedEigenvalueTestProgram kernels A hA t j g).eval =
      (shiftedSingularEigenvalueTestProgram kernels A hA t j g).eval := by
  simp only [exactGramAppendixShiftedEigenvalueTestProgram,
    shiftedSingularEigenvalueTestProgram, shiftedEigenvalueTestOptionProgram, eval_bind]
  split
  · rename_i heq
    rw [heq]
  · rename_i out heq
    rw [heq]
    simp only [eval_bind, certify_eval, positiveDiagonalCountProgram_eval]
    rfl

theorem exactGramAppendixShiftedEigenvalueTestProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core n) (hA : A.IsHermitian) (t : ℝ) (j : Fin n) (g : Fin (n*n) → ℝ) :
    (exactGramAppendixShiftedEigenvalueTestProgram kernels A hA t j g).admissible := by
  simp only [exactGramAppendixShiftedEigenvalueTestProgram, admissible_bind,
    certify_admissible, shiftedMatrixProgram_admissible, singularInertiaFamily_admissible,
    true_and]
  split
  · trivial
  · simp only [admissible_bind, certify_admissible, positiveDiagonalCountProgram_admissible,
      ArithmeticProgram.admissible, and_true]

theorem exactGramAppendixShiftedEigenvalueTestProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N : ℝ)^p)
    (A : Core n) (hA : A.IsHermitian) (t : ℝ) (j : Fin n) (g : Fin (n*n) → ℝ) :
    ((exactGramAppendixShiftedEigenvalueTestProgram kernels A hA t j g).work : ℝ) ≤
      105*(C+1)*(n : ℝ)^p := by
  have hn : 1 ≤ n := by have hj := j.isLt; omega
  let D := (shiftedMatrixProgram A t).certify.eval.val
  have hD : D.IsHermitian := by
    dsimp only [D]
    rw [(shiftedMatrixProgram A t).certify.eval.property, shiftedMatrixProgram_eval]
    exact shifted_isHermitian A hA t
  have hi := projectedSingularInertiaProgram_work_bound kernels C p hC hp hK D
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq) hn g
  have hinertia : ((singularInertiaFamily kernels n g n D hD).work : ℝ) ≤
      100*(C+1)*(n : ℝ)^p := by
    simpa only [singularInertiaFamily, initialCoordinates_self] using hi
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (n : ℝ)^2 ≤ (n : ℝ)^p := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hn1 hp
  have hnp0 : 0 ≤ (n : ℝ)^p := Real.rpow_nonneg (by positivity) p
  have hnnp : (n : ℝ) ≤ (n : ℝ)^p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (Nat.cast_nonneg n)]
  have hnp1 : 1 ≤ (n : ℝ)^p := le_trans hn1 hnnp
  dsimp only [D] at hinertia
  simp only [exactGramAppendixShiftedEigenvalueTestProgram, work_bind, certify_work,
    shiftedMatrixProgram_work, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  split
  · simp only [work_pure, Nat.cast_zero]
    nlinarith [mul_nonneg hC.le hnp0]
  · rename_i out hout
    have hsign : ((positiveDiagonalCountProgram out.diagonal).work : ℝ) ≤ 2*(n : ℝ) := by
      exact_mod_cast positiveDiagonalCountProgram_work_le out.diagonal
    simp only [work_bind, certify_work,
      ArithmeticProgram.work, Nat.cast_add, Nat.cast_zero, Nat.cast_one]
    nlinarith [mul_nonneg hC.le hnp0]

end
end HierarchicalAbsoluteSpectral
