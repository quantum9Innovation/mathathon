import HierarchicalAbsoluteSpectral.FFTProgram

/-! Scalar preparation programs for Lemma 4. Each real operation is an
instruction, and admissibility proves that roots and divisions are legal. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

def rootSeriesProgram : ℕ → ArithmeticProgram ℝ
  | 0 => ArithmeticProgram.pure 0
  | s+1 => do
      let a ← rootSeriesProgram s
      let b ← add 2 a
      sqrt b

@[simp] theorem rootSeriesProgram_eval (s : ℕ) :
    (rootSeriesProgram s).eval = Real.sqrtTwoAddSeries 0 s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [rootSeriesProgram, ih, Real.sqrtTwoAddSeries]

@[simp] theorem rootSeriesProgram_work (s : ℕ) : (rootSeriesProgram s).work = 2*s := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [rootSeriesProgram, work_bind, ih, work_add, work_sqrt]; omega

@[simp] theorem rootSeriesProgram_admissible (s : ℕ) : (rootSeriesProgram s).admissible := by
  induction s with
  | zero => trivial
  | succ s ih =>
    simp only [rootSeriesProgram, admissible_bind, ih, admissible_add, eval_add,
      admissible_sqrt, rootSeriesProgram_eval, true_and]
    linarith [Real.sqrtTwoAddSeries_zero_nonneg s]

def dyadicRootProgram (s : ℕ) : ArithmeticProgram ℂ := do
  let a ← rootSeriesProgram s
  let c ← div a 2
  let c2 ← mul c c
  let r ← sub 1 c2
  let t ← sqrt r
  ArithmeticProgram.pure ⟨c,t⟩

@[simp] theorem dyadicRootProgram_eval (s : ℕ) : (dyadicRootProgram s).eval = dyadicRoot s := by
  apply Complex.ext <;> simp [dyadicRootProgram, dyadicRoot, dyadicCos, dyadicSin, pow_two]

@[simp] theorem dyadicRootProgram_work (s : ℕ) : (dyadicRootProgram s).work = 2*s+4 := by
  simp [dyadicRootProgram]

@[simp] theorem dyadicRootProgram_admissible (s : ℕ) : (dyadicRootProgram s).admissible := by
  simp only [dyadicRootProgram, admissible_bind, rootSeriesProgram_admissible,
    rootSeriesProgram_eval, admissible_div, eval_div, admissible_mul, eval_mul,
    admissible_sub, eval_sub, admissible_sqrt, admissible_pure, true_and, and_true]
  constructor
  · norm_num
  · simpa only [dyadicCos, pow_two] using (dyadicSin_radicand_pos s).le

def dyadicScaleProgram : ℕ → ArithmeticProgram ℝ
  | 0 => ArithmeticProgram.pure 1
  | s+1 => do
      let a ← dyadicScaleProgram s
      div a 2

@[simp] theorem dyadicScaleProgram_eval (s : ℕ) :
    (dyadicScaleProgram s).eval = 1/(2^s : ℝ) := by
  induction s with
  | zero => simp [dyadicScaleProgram]
  | succ s ih => simp only [dyadicScaleProgram, eval_bind, eval_div, ih, pow_succ, div_div]

@[simp] theorem dyadicScaleProgram_work (s : ℕ) : (dyadicScaleProgram s).work = s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [dyadicScaleProgram, ih]

@[simp] theorem dyadicScaleProgram_admissible (s : ℕ) : (dyadicScaleProgram s).admissible := by
  induction s with
  | zero => trivial
  | succ s ih => simp [dyadicScaleProgram, ih]

def inverseRootValueProgram (η x : ℝ) : ArithmeticProgram ℝ := do
  let x2 ← mul x x
  let η2 ← mul η η
  let r ← add x2 η2
  let q ← sqrt r
  let a ← add q η
  let b ← sqrt a
  div 1 b

@[simp] theorem inverseRootValueProgram_eval (η x : ℝ) :
    (inverseRootValueProgram η x).eval = inverseRootValue η x := by
  simp [inverseRootValueProgram, inverseRootValue, pow_two]

@[simp] theorem inverseRootValueProgram_work (η x : ℝ) :
    (inverseRootValueProgram η x).work = 7 := by simp [inverseRootValueProgram]

theorem inverseRootValueProgram_admissible (η x : ℝ) (hη : 0 < η) :
    (inverseRootValueProgram η x).admissible := by
  simp only [inverseRootValueProgram, admissible_bind, admissible_mul, eval_mul,
    admissible_add, eval_add, admissible_sqrt, eval_sqrt, admissible_div, true_and]
  refine ⟨by nlinarith [sq_nonneg x, sq_nonneg η], by positivity, ?_⟩
  exact (Real.sqrt_pos.mpr (show 0 < Real.sqrt (x*x+η*η)+η by positivity)).ne'

end
end HierarchicalAbsoluteSpectral
