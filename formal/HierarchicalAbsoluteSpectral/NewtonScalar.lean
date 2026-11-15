import HierarchicalAbsoluteSpectral.IdealMetric
import HierarchicalAbsoluteSpectral.NeumannDegree
import HierarchicalAbsoluteSpectral.ArithmeticProgram

/-! The finite upper Newton iteration used by the coarse base metric. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section

def upperNewtonStep (a x : ℝ) : ℝ := (x+a/x)/2

def upperNewtonScalar (a : ℝ) : ℕ → ℝ
  | 0 => 2
  | n+1 => upperNewtonStep a (upperNewtonScalar a n)

theorem upperNewtonScalar_pos_of_pos (a : ℝ) (ha : 0 < a) (n : ℕ) :
    0 < upperNewtonScalar a n := by
  induction n with
  | zero => norm_num [upperNewtonScalar]
  | succ n ih =>
    unfold upperNewtonScalar upperNewtonStep
    positivity

theorem upperNewtonStep_bounds (a ρ x : ℝ) (hρ : 0 < ρ) (hρsq : ρ^2 = a)
    (hx : ρ ≤ x) :
    ρ ≤ upperNewtonStep a x ∧ upperNewtonStep a x-ρ ≤ (x-ρ)/2 := by
  have hxp : 0 < x := hρ.trans_le hx
  have hquot : x*(a/x) = a := by field_simp
  have hdiv : a/x ≤ ρ := (div_le_iff₀ hxp).mpr (by nlinarith)
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    change ρ*2 ≤ x+a/x
    apply (mul_le_mul_iff_left₀ hxp).mp
    nlinarith [sq_nonneg (x-ρ)]
  · unfold upperNewtonStep
    linarith

theorem upperNewtonScalar_bounds (a : ℝ) (ha : 0 < a) (ha' : a ≤ 4) (n : ℕ) :
    Real.sqrt a ≤ upperNewtonScalar a n ∧
      upperNewtonScalar a n-Real.sqrt a ≤ 2*(1/2:ℝ)^n ∧ upperNewtonScalar a n ≤ 2 := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq := Real.sq_sqrt ha.le
  have hs2 : Real.sqrt a ≤ 2 := by nlinarith [Real.sqrt_nonneg a]
  induction n with
  | zero => simp only [upperNewtonScalar, pow_zero, mul_one]; exact ⟨hs2, by linarith, le_refl _⟩
  | succ n ih =>
    have hstep := upperNewtonStep_bounds a (Real.sqrt a) (upperNewtonScalar a n) hs hsq ih.1
    refine ⟨hstep.1, ?_, ?_⟩
    · rw [upperNewtonScalar, pow_succ]
      nlinarith [ih.2.1, hstep.2]
    · change upperNewtonStep a (upperNewtonScalar a n) ≤ 2
      linarith [hstep.2, ih.2.2]

theorem upperNewtonScalar_pos (a : ℝ) (ha : 0 < a) (ha' : a ≤ 4) (n : ℕ) :
    0 < upperNewtonScalar a n :=
  (Real.sqrt_pos.mpr ha).trans_le (upperNewtonScalar_bounds a ha ha' n).1

def baseNewtonSteps (h : ℝ) (hh : 0 < h) : ℕ := neumannCount (4*h) (by positivity)

theorem baseNewtonSteps_accuracy (h : ℝ) (hh : 0 < h) :
    2*(1/2:ℝ)^(baseNewtonSteps h hh) ≤ 8*h := by
  have hs := dyadicStoppingLevel_stops (1/2) (4*h) (by norm_num) (by norm_num)
    (show 0 < 4*h by positivity)
  change (1/2:ℝ)^(baseNewtonSteps h hh) ≤ 4*h at hs
  linarith

theorem baseNewtonSteps_bound (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64) :
    (baseNewtonSteps h hh : ℝ) ≤ 1+4*Real.log (1/(4*h)) :=
  neumannCount_bound (4*h) (by positivity) (by linarith)

def baseNewtonScalar (h x : ℝ) (n : ℕ) : ℝ := upperNewtonScalar (x^2+(8*h)^2) n+8*h

theorem baseNewtonScalar_bounds (h x : ℝ) (n : ℕ) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hx : -1 ≤ x) (hx' : x ≤ 1) (hn : 2*(1/2:ℝ)^n ≤ 8*h) :
    8*h ≤ baseNewtonScalar h x n ∧ baseNewtonScalar h x n ≤ 2 ∧
      8*h ≤ baseNewtonScalar h x n-x ∧ 8*h ≤ baseNewtonScalar h x n+x ∧
      0 ≤ baseNewtonScalar h x n-x^2/baseNewtonScalar h x n ∧
      baseNewtonScalar h x n-x^2/baseNewtonScalar h x n ≤ 32*h := by
  have ha : 0 < x^2+(8*h)^2 := by positivity
  have ha' : x^2+(8*h)^2 ≤ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-x by linarith) (show 0 ≤ 1+x by linarith)]
  have hi := upperNewtonScalar_bounds _ ha ha' n
  have hs := Real.sqrt_nonneg (x^2+(8*h)^2)
  have hsq := Real.sq_sqrt ha.le
  have hsx : |x| ≤ Real.sqrt (x^2+(8*h)^2) := by
    nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (8*h)]
  have hsh : 8*h ≤ Real.sqrt (x^2+(8*h)^2) := by nlinarith [sq_nonneg x]
  have hsu : Real.sqrt (x^2+(8*h)^2) ≤ 1+8*h := by
    nlinarith [mul_nonneg (show 0 ≤ 1-x by linarith) (show 0 ≤ 1+x by linarith)]
  have hfb : baseNewtonScalar h x n ≤ Real.sqrt (x^2+(8*h)^2)+16*h := by
    unfold baseNewtonScalar
    linarith
  have hfl : Real.sqrt (x^2+(8*h)^2)+8*h ≤ baseNewtonScalar h x n := by
    unfold baseNewtonScalar
    linarith
  have hfp : 0 < baseNewtonScalar h x n := by linarith
  have hm : 0 ≤ baseNewtonScalar h x n-16*h := by linarith
  have hdiff : 0 ≤ Real.sqrt (x^2+(8*h)^2)-(baseNewtonScalar h x n-16*h) := by linarith
  have hsum : 0 ≤ Real.sqrt (x^2+(8*h)^2)+(baseNewtonScalar h x n-16*h) := by linarith
  have hprod := mul_nonneg hdiff hsum
  have hmul : baseNewtonScalar h x n*(x^2/baseNewtonScalar h x n) = x^2 := by field_simp
  refine ⟨by linarith, by linarith, by linarith [le_abs_self x], by linarith [neg_le_abs x], ?_, ?_⟩
  · apply (mul_nonneg_iff_of_pos_left hfp).mp
    nlinarith [mul_nonneg (show 0 ≤ baseNewtonScalar h x n-|x| by linarith)
      (show 0 ≤ baseNewtonScalar h x n+|x| by positivity), sq_abs x]
  · apply (mul_le_mul_iff_left₀ hfp).mp
    nlinarith

open ArithmeticProgram hiding pure

def upperNewtonScalarProgram (a : ℝ) : ℕ → ArithmeticProgram ℝ
  | 0 => .pure 2
  | n+1 => do
      let x ← upperNewtonScalarProgram a n
      let q ← div a x
      let s ← add x q
      div s 2

@[simp] theorem upperNewtonScalarProgram_eval (a : ℝ) (n : ℕ) :
    (upperNewtonScalarProgram a n).eval = upperNewtonScalar a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [upperNewtonScalarProgram, eval_bind, eval_div, eval_add,
      ih, upperNewtonScalar, upperNewtonStep]

@[simp] theorem upperNewtonScalarProgram_work (a : ℝ) (n : ℕ) :
    (upperNewtonScalarProgram a n).work = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [upperNewtonScalarProgram, work_bind, work_div, work_add, ih]; omega

theorem upperNewtonScalarProgram_admissible (a : ℝ) (ha : 0 < a) (ha' : a ≤ 4) (n : ℕ) :
    (upperNewtonScalarProgram a n).admissible := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [upperNewtonScalarProgram, admissible_bind, ih, admissible_div,
      admissible_add, true_and, upperNewtonScalarProgram_eval]
    exact ⟨(upperNewtonScalar_pos a ha ha' n).ne', by norm_num⟩

end
end HierarchicalAbsoluteSpectral
