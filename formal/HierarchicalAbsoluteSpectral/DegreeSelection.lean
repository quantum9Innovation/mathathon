import HierarchicalAbsoluteSpectral.ArithmeticProgram
import HierarchicalAbsoluteSpectral.DyadicDegree

/-! Repeated-squaring degree selection as an operational program. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

def dyadicStoppingLevel (r δ : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (hδ : 0 < δ) : ℕ :=
  Nat.find (dyadic_stopping_exists r δ hr hr' hδ)

theorem dyadicStoppingLevel_stops (r δ : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (hδ : 0 < δ) :
    r^(2^(dyadicStoppingLevel r δ hr hr' hδ)) ≤ δ := by
  exact Nat.find_spec (p := fun s : ℕ => r^(2^s) ≤ δ) _

theorem dyadicStoppingLevel_zero (r δ : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (hδ : 0 < δ)
    (h : r ≤ δ) : dyadicStoppingLevel r δ hr hr' hδ = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' _ (by simpa using h)

theorem square_lt_one (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) : r*r < 1 := by
  nlinarith [mul_pos (sub_pos.mpr hr') (show 0 < 1+r by linarith)]

theorem squared_dyadic_power (r : ℝ) (s : ℕ) : (r*r)^(2^s) = r^(2^(s+1)) := by
  rw [pow_succ' (2:ℕ) s, pow_mul, pow_two]

theorem dyadicStoppingLevel_square_decreases (r δ : ℝ) (hr : 0 ≤ r) (hr' : r < 1)
    (hδ : 0 < δ) (h : ¬r ≤ δ) :
    dyadicStoppingLevel (r*r) δ (mul_nonneg hr hr) (square_lt_one r hr hr') hδ <
      dyadicStoppingLevel r δ hr hr' hδ := by
  have hstop := dyadicStoppingLevel_stops r δ hr hr' hδ
  cases heq : dyadicStoppingLevel r δ hr hr' hδ with
  | zero =>
    rw [heq] at hstop
    exact False.elim (h (by simpa using hstop))
  | succ s =>
    have hstop' : (r*r)^(2^s) ≤ δ := by
      rw [heq] at hstop
      simpa only [squared_dyadic_power] using hstop
    have hm : dyadicStoppingLevel (r*r) δ (mul_nonneg hr hr) (square_lt_one r hr hr') hδ ≤ s :=
      Nat.find_min' _ hstop'
    omega

theorem dyadicStoppingLevel_square (r δ : ℝ) (hr : 0 ≤ r) (hr' : r < 1)
    (hδ : 0 < δ) (h : ¬r ≤ δ) :
    dyadicStoppingLevel (r*r) δ (mul_nonneg hr hr) (square_lt_one r hr hr') hδ + 1 =
      dyadicStoppingLevel r δ hr hr' hδ := by
  have hdec := dyadicStoppingLevel_square_decreases r δ hr hr' hδ h
  have hstop := dyadicStoppingLevel_stops (r*r) δ (mul_nonneg hr hr) (square_lt_one r hr hr') hδ
  have hstop' : r^(2^(dyadicStoppingLevel (r*r) δ (mul_nonneg hr hr)
      (square_lt_one r hr hr') hδ+1)) ≤ δ := by
    simpa only [squared_dyadic_power] using hstop
  have hm : dyadicStoppingLevel r δ hr hr' hδ ≤
      dyadicStoppingLevel (r*r) δ (mul_nonneg hr hr) (square_lt_one r hr hr') hδ+1 :=
    Nat.find_min' _ hstop'
  omega

def dyadicSearchProgram (r δ : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (hδ : 0 < δ) :
    ArithmeticProgram ℕ :=
  .branch r δ
    (fun _ => .pure 0)
    (fun _ => .certifiedStep (.mul r r) (fun q => do
      let s ← dyadicSearchProgram q.val δ
        (by rw [q.property]; exact mul_nonneg hr hr)
        (by rw [q.property]; exact square_lt_one r hr hr') hδ
      ArithmeticProgram.pure (s+1)))
termination_by dyadicStoppingLevel r δ hr hr' hδ
decreasing_by
  simpa only [q.property, ArithmeticOp.eval] using
    dyadicStoppingLevel_square_decreases r δ hr hr' hδ ‹¬r ≤ δ›

theorem dyadicSearchProgram_specification (r δ : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (hδ : 0 < δ) :
    (dyadicSearchProgram r δ hr hr' hδ).eval = dyadicStoppingLevel r δ hr hr' hδ ∧
      (dyadicSearchProgram r δ hr hr' hδ).work = 2*dyadicStoppingLevel r δ hr hr' hδ+1 ∧
      (dyadicSearchProgram r δ hr hr' hδ).admissible := by
  generalize hn : dyadicStoppingLevel r δ hr hr' hδ = n
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    rw [dyadicSearchProgram.eq_def]
    by_cases h : r ≤ δ
    · have hz := dyadicStoppingLevel_zero r δ hr hr' hδ h
      have hn0 : n = 0 := by omega
      simp [ArithmeticProgram.eval, ArithmeticProgram.work, ArithmeticProgram.admissible, h, hn0]
    · have hdec := dyadicStoppingLevel_square_decreases r δ hr hr' hδ h
      have heq := dyadicStoppingLevel_square r δ hr hr' hδ h
      have hi := ih (dyadicStoppingLevel (r*r) δ (mul_nonneg hr hr) (square_lt_one r hr hr') hδ)
        (by omega) (r*r) (mul_nonneg hr hr) (square_lt_one r hr hr') rfl
      simp only [ArithmeticProgram.eval, ArithmeticProgram.work, ArithmeticProgram.admissible,
        dif_neg h, ArithmeticOp.eval, eval_bind, work_bind, admissible_bind,
        add_zero, and_true, ArithmeticOp.admissible, true_and]
      rw [hi.1, hi.2.1]
      constructor
      · omega
      · exact ⟨by omega, hi.2.2⟩

def degreeParameterProgram (η τ : ℝ) : ArithmeticProgram (ℝ × ℝ) := do
  let a ← div η 4
  let ρ ← add 1 a
  let r ← div 1 ρ
  let e ← sqrt η
  let b ← mul τ η
  let c ← mul b e
  let δ ← div c 1000
  ArithmeticProgram.pure (r,δ)

@[simp] theorem degreeParameterProgram_eval (η τ : ℝ) :
    (degreeParameterProgram η τ).eval = ((1+η/4)⁻¹, τ*η*Real.sqrt η/1000) := by
  simp [degreeParameterProgram]

@[simp] theorem degreeParameterProgram_work (η τ : ℝ) :
    (degreeParameterProgram η τ).work = 7 := by simp [degreeParameterProgram]

theorem degreeParameterProgram_admissible (η τ : ℝ) (hη : 0 < η) :
    (degreeParameterProgram η τ).admissible := by
  simp [degreeParameterProgram, ne_of_gt (show 0 < 1+η/4 by positivity), hη.le]

def degreeSelectionProgram (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) : ArithmeticProgram ℕ := do
  let a ← certify (degreeParameterProgram η τ)
  dyadicSearchProgram a.val.1 a.val.2
    (by rw [a.property, degreeParameterProgram_eval]; positivity)
    (by
      rw [a.property, degreeParameterProgram_eval]
      exact (inv_lt_one₀ (by positivity)).mpr (by linarith))
    (by rw [a.property, degreeParameterProgram_eval]; positivity)

theorem degreeSelectionProgram_specification (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    (degreeSelectionProgram η τ hη hτ).eval = inverseRootLevel η τ hη hτ ∧
      (degreeSelectionProgram η τ hη hτ).work = 2*inverseRootLevel η τ hη hτ+8 ∧
      (degreeSelectionProgram η τ hη hτ).admissible := by
  have hsearch := dyadicSearchProgram_specification (1+η/4)⁻¹ (τ*η*Real.sqrt η/1000)
    (by positivity) ((inv_lt_one₀ (by positivity)).mpr (by linarith)) (by positivity)
  have hlevel : dyadicStoppingLevel (1+η/4)⁻¹ (τ*η*Real.sqrt η/1000)
      (by positivity) ((inv_lt_one₀ (by positivity)).mpr (by linarith)) (by positivity) =
      inverseRootLevel η τ hη hτ := rfl
  rw [hlevel] at hsearch
  simp only [degreeSelectionProgram, eval_bind, work_bind, admissible_bind, certify_eval,
    certify_work, degreeParameterProgram_eval, degreeParameterProgram_work, certify_admissible]
  rw [hsearch.1, hsearch.2.1]
  exact ⟨rfl, by omega, degreeParameterProgram_admissible η τ hη, hsearch.2.2⟩

end
end HierarchicalAbsoluteSpectral
