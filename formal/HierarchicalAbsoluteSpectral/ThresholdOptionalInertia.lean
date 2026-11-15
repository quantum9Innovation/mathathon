import HierarchicalAbsoluteSpectral.ThresholdRitzTests
import HierarchicalAbsoluteSpectral.CoarseAlgebraFastLDLProgram

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {k r q : ℕ} {T : Core k} {Ω : Matrix (Fin k) (Fin r) ℝ}

abbrev OptionalInertiaProgramFamily := ∀ (n : ℕ) (D : Core n), D.IsHermitian →
  ArithmeticProgram (Option (FiniteCongruenceDiagonal D))

def rawFastInertiaFamily (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) : OptionalInertiaProgramFamily :=
  fun n D hD => fastInertiaDiagonalProgram kernels n D (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq)

theorem rawFastInertiaFamily_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : D.IsHermitian) : (rawFastInertiaFamily kernels n D hD).admissible :=
  fastInertiaDiagonalProgram_admissible kernels n D _

def shiftedEigenvalueTestOptionProgram (inertia : OptionalInertiaProgramFamily)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) :
    ArithmeticProgram (Option (CertifiedEigenvalueTest A hA c j)) := do
  let shifted ← (shiftedMatrixProgram A c).certify
  have hshift : shifted.val = A-c • (1 : Core k) := shifted.property.trans (shiftedMatrixProgram_eval A c)
  let out? ← inertia k shifted.val (by rw [hshift]; exact shifted_isHermitian A hA c)
  match out? with
  | none => .pure none
  | some out => do
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
      simp only [ArithmeticProgram.eval,decide_eq_true_eq,Nat.cast_le,Nat.succ_le_iff]
      rfl
    .pure (some ⟨answer.val,hb.trans (out'.shifted_eigenvalue_gt_iff A hA c j).symm⟩)

theorem shiftedEigenvalueTestOptionProgram_admissible (inertia : OptionalInertiaProgramFamily)
    (hInertia : ∀ n D hD, (inertia n D hD).admissible)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) :
    (shiftedEigenvalueTestOptionProgram inertia A hA c j).admissible := by
  simp only [shiftedEigenvalueTestOptionProgram,admissible_bind,certify_admissible,
    shiftedMatrixProgram_admissible,hInertia,true_and]
  split
  · trivial
  · simp only [admissible_bind,certify_admissible,ArithmeticProgram.admissible,and_true]

theorem shiftedEigenvalueTestOptionProgram_work_le (inertia : OptionalInertiaProgramFamily)
    (cost : ℕ → ℕ) (hInertia : ∀ n D hD, (inertia n D hD).work ≤ cost n)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) :
    (shiftedEigenvalueTestOptionProgram inertia A hA c j).work ≤ 2*k*k+cost k+1 := by
  simp only [shiftedEigenvalueTestOptionProgram,work_bind,certify_work,shiftedMatrixProgram_work]
  have hh := hInertia k (shiftedMatrixProgram A c).certify.eval.val
    (by
      rw [(shiftedMatrixProgram A c).certify.eval.property,shiftedMatrixProgram_eval]
      exact shifted_isHermitian A hA c)
  split
  · simp only [work_pure]
    omega
  · simp only [work_bind,certify_work,ArithmeticProgram.work,work_pure,add_zero]
    omega

def ritzTestsOptionProgram (inertias : Fin 2 → OptionalInertiaProgramFamily)
    (data : KrylovQueryData T Ω q) (j : Fin k) (ε : ℝ) (hε : ε ≤ 1/4) :
    ArithmeticProgram (Option (CertifiedRitzTests (data.ritzValue j) ε)) :=
  if hj : j.val < data.range.dimension then do
    let one? ← shiftedEigenvalueTestOptionProgram (inertias 0) data.compression data.compression_posSemidef.isHermitian 1 ⟨j.val,hj⟩
    match one? with
    | none => .pure none
    | some one => do
      let low ← (lowThresholdProgram ε).certify
      let two? ← shiftedEigenvalueTestOptionProgram (inertias 1) data.compression data.compression_posSemidef.isHermitian low.val ⟨j.val,hj⟩
      match two? with
      | none => .pure none
      | some two =>
        have hritz : data.ritzValue j = orderedEigenvalue data.compression
            data.compression_posSemidef.isHermitian ⟨j.val,hj⟩ := dif_pos hj
        have hlow : low.val = 1-2*ε := low.property.trans (lowThresholdProgram_eval ε)
        .pure (some {
          aboveOne := one.answer
          aboveLow := two.answer
          one_correct := by rw [hritz]; exact one.correct
          low_correct := by rw [hritz,← hlow]; exact two.correct })
  else .pure (some {
    aboveOne := false
    aboveLow := false
    one_correct := by simp only [Bool.false_eq_true,KrylovQueryData.ritzValue,dif_neg hj]; norm_num
    low_correct := by
      simp only [Bool.false_eq_true,KrylovQueryData.ritzValue,dif_neg hj]
      constructor
      · exact False.elim
      · intro hh; linarith })

theorem ritzTestsOptionProgram_admissible (inertias : Fin 2 → OptionalInertiaProgramFamily)
    (hInertia : ∀ i n D hD, (inertias i n D hD).admissible)
    (data : KrylovQueryData T Ω q) (j : Fin k) (ε : ℝ) (hε : ε ≤ 1/4) :
    (ritzTestsOptionProgram inertias data j ε hε).admissible := by
  unfold ritzTestsOptionProgram
  split_ifs
  · simp only [admissible_bind,shiftedEigenvalueTestOptionProgram_admissible _ (hInertia 0),true_and]
    split
    · trivial
    · simp only [admissible_bind,certify_admissible,lowThresholdProgram_admissible,
        shiftedEigenvalueTestOptionProgram_admissible _ (hInertia 1),true_and]
      split <;> trivial
  · trivial

end
end HierarchicalAbsoluteSpectral
