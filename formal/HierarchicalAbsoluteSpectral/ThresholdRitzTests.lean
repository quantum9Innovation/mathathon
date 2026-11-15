import HierarchicalAbsoluteSpectral.ThresholdInertiaProgram

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {k r q : ℕ} {T : Core k} {Ω : Matrix (Fin k) (Fin r) ℝ}

def KrylovQueryData.ritzValue (data : KrylovQueryData T Ω q) (j : Fin k) : ℝ :=
  if hj : j.val < data.range.dimension then
    orderedEigenvalue data.compression data.compression_posSemidef.isHermitian ⟨j.val,hj⟩
  else 0

theorem KrylovQueryData.ritzValue_eq (data : KrylovQueryData T Ω q) (hT : T.IsHermitian)
    (j : Fin k) : data.ritzValue j = thresholdRitzValue T hT data.range.basis j := by
  unfold KrylovQueryData.ritzValue thresholdRitzValue
  split_ifs
  · simp only [data.compression_eq]
  · rfl

structure CertifiedRitzTests (value ε : ℝ) where
  aboveOne : Bool
  aboveLow : Bool
  one_correct : aboveOne = true ↔ 1 < value
  low_correct : aboveLow = true ↔ 1-2*ε < value

def lowThresholdProgram (ε : ℝ) : ArithmeticProgram ℝ := do
  let twice ← mul 2 ε
  sub 1 twice

@[simp] theorem lowThresholdProgram_eval (ε : ℝ) : (lowThresholdProgram ε).eval = 1-2*ε := by
  simp [lowThresholdProgram]
@[simp] theorem lowThresholdProgram_work (ε : ℝ) : (lowThresholdProgram ε).work = 2 := by
  simp [lowThresholdProgram]
theorem lowThresholdProgram_admissible (ε : ℝ) : (lowThresholdProgram ε).admissible := by
  simp [lowThresholdProgram]

def ritzTestsProgram (inertia : InertiaProgramFamily) (data : KrylovQueryData T Ω q)
    (j : Fin k) (ε : ℝ) (hε : ε ≤ 1/4) : ArithmeticProgram (CertifiedRitzTests (data.ritzValue j) ε) :=
  if hj : j.val < data.range.dimension then do
    let one ← shiftedEigenvalueTestProgram inertia data.compression data.compression_posSemidef.isHermitian 1 ⟨j.val,hj⟩
    let low ← (lowThresholdProgram ε).certify
    let two ← shiftedEigenvalueTestProgram inertia data.compression data.compression_posSemidef.isHermitian low.val ⟨j.val,hj⟩
    have hritz : data.ritzValue j = orderedEigenvalue data.compression
        data.compression_posSemidef.isHermitian ⟨j.val,hj⟩ := dif_pos hj
    have hlow : low.val = 1-2*ε := low.property.trans (lowThresholdProgram_eval ε)
    .pure { aboveOne := one.answer
            aboveLow := two.answer
            one_correct := by rw [hritz]; exact one.correct
            low_correct := by rw [hritz, ← hlow]; exact two.correct }
  else .pure { aboveOne := false
               aboveLow := false
               one_correct := by simp only [Bool.false_eq_true, KrylovQueryData.ritzValue, dif_neg hj]; norm_num
               low_correct := by
                 simp only [Bool.false_eq_true, KrylovQueryData.ritzValue, dif_neg hj]
                 constructor
                 · exact False.elim
                 · intro hh; linarith }

theorem ritzTestsProgram_admissible (inertia : InertiaProgramFamily)
    (hInertia : ∀ n D hD, (inertia n D hD).admissible)
    (data : KrylovQueryData T Ω q) (j : Fin k) (ε : ℝ) (hε : ε ≤ 1/4) :
    (ritzTestsProgram inertia data j ε hε).admissible := by
  unfold ritzTestsProgram
  split_ifs
  · simp only [admissible_bind, shiftedEigenvalueTestProgram_admissible inertia hInertia,
      certify_admissible, lowThresholdProgram_admissible, admissible_pure, and_self]
  · trivial

theorem ritzTestsProgram_work_le (inertia : InertiaProgramFamily)
    (cost : ℕ → ℕ) (hInertia : ∀ n D hD, (inertia n D hD).work ≤ cost n)
    (data : KrylovQueryData T Ω q) (j : Fin k) (ε : ℝ) (hε : ε ≤ 1/4) :
    (ritzTestsProgram inertia data j ε hε).work ≤
      4*data.range.dimension*data.range.dimension+2*cost data.range.dimension+4 := by
  unfold ritzTestsProgram
  split_ifs with hj
  · simp only [work_bind, certify_work, lowThresholdProgram_work, work_pure, add_zero]
    have h₁ := shiftedEigenvalueTestProgram_work_le inertia cost hInertia data.compression
      data.compression_posSemidef.isHermitian 1 ⟨j.val,hj⟩
    have h₂ := shiftedEigenvalueTestProgram_work_le inertia cost hInertia data.compression
      data.compression_posSemidef.isHermitian (lowThresholdProgram ε).certify.eval.val ⟨j.val,hj⟩
    nlinarith only [h₁,h₂]
  · simp only [work_pure]
    omega

end
end HierarchicalAbsoluteSpectral
