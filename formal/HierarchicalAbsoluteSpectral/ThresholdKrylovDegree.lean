import HierarchicalAbsoluteSpectral.ThresholdRepeatedSafe
import HierarchicalAbsoluteSpectral.StrongFilterSearch

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

def gaussianCaptureRadiusProgram (k : ℕ) (U β : ℝ) : ArithmeticProgram ℝ := do
  let a ← mul 100 k
  let b ← mul a U
  let c ← div b β
  let d ← mul c c
  mul d c

@[simp] theorem gaussianCaptureRadiusProgram_eval (k : ℕ) (U β : ℝ) :
    (gaussianCaptureRadiusProgram k U β).eval = gaussianCaptureRadius k U β := by
  simp only [gaussianCaptureRadiusProgram, eval_bind, eval_mul, eval_div, gaussianCaptureRadius]
  ring

@[simp] theorem gaussianCaptureRadiusProgram_work (k : ℕ) (U β : ℝ) :
    (gaussianCaptureRadiusProgram k U β).work = 5 := by
  simp [gaussianCaptureRadiusProgram]

theorem gaussianCaptureRadiusProgram_admissible (k : ℕ) (U β : ℝ) (hβ : β ≠ 0) :
    (gaussianCaptureRadiusProgram k U β).admissible := by
  simp [gaussianCaptureRadiusProgram, hβ]

theorem krylovDegree_target_ge_one (k : ℕ) (U β ε : ℝ) (hk : 1 ≤ k)
    (hU : 1 ≤ U) (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) :
    1 ≤ 10*gaussianCaptureRadius k U β/ε := by
  have hR := gaussianCaptureRadius_ge_one k U β hk hU hβ hβ'
  apply (le_div_iff₀ hε).mpr
  nlinarith

def krylovDegree (k : ℕ) (U β ε : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) : ℕ :=
  strongFilterDegree (ε/100) (10*gaussianCaptureRadius k U β/ε) (by positivity) (by linarith)
    (krylovDegree_target_ge_one k U β ε hk hU hβ hβ' hε hε')

theorem krylovDegree_stops (k : ℕ) (U β ε : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) :
    10*gaussianCaptureRadius k U β/ε ≤ strongFilterDenominator (ε/100)
      (krylovDegree k U β ε hk hU hβ hβ' hε hε') := strongFilterDegree_stops _ _ _ _ _

theorem krylovDegree_bound (k : ℕ) (U β ε : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) :
    (krylovDegree k U β ε hk hU hβ hβ' hε hε' : ℝ) ≤
      2*Real.log (20*gaussianCaptureRadius k U β/ε)/Real.sqrt (ε/100)+1 := by
  have hh := strongFilterDegree_bound (ε/100) (10*gaussianCaptureRadius k U β/ε)
    (by positivity) (by linarith) (krylovDegree_target_ge_one k U β ε hk hU hβ hβ' hε hε')
  simpa only [krylovDegree, show 2*(10*gaussianCaptureRadius k U β/ε) =
    20*gaussianCaptureRadius k U β/ε by ring] using hh

def krylovDegreeProgram (k : ℕ) (U β ε : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) : ArithmeticProgram ℕ := do
  let R ← (gaussianCaptureRadiusProgram k U β).certify
  let small ← (div ε 100).certify
  let D ← certify (show ArithmeticProgram ℝ from do
    let a ← mul 10 R.val
    div a ε)
  have hR : R.val = gaussianCaptureRadius k U β := R.property.trans (gaussianCaptureRadiusProgram_eval _ _ _)
  have hsmall : small.val = ε/100 := small.property
  have hD : D.val = 10*gaussianCaptureRadius k U β/ε := by
    simpa only [eval_bind, eval_mul, eval_div, hR] using D.property
  strongDegreeProgram small.val D.val (by rw [hsmall]; positivity) (by rw [hsmall]; linarith)
    (by rw [hD]; exact krylovDegree_target_ge_one k U β ε hk hU hβ hβ' hε hε')

theorem krylovDegreeProgram_specification (k : ℕ) (U β ε : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) :
    (krylovDegreeProgram k U β ε hk hU hβ hβ' hε hε').eval = krylovDegree k U β ε hk hU hβ hβ' hε hε' ∧
    (krylovDegreeProgram k U β ε hk hU hβ hβ' hε hε').work =
      4*krylovDegree k U β ε hk hU hβ hβ' hε hε'+15 ∧
    (krylovDegreeProgram k U β ε hk hU hβ hβ' hε hε').admissible := by
  simp only [krylovDegreeProgram, eval_bind, work_bind, admissible_bind,
    certify_work, certify_admissible]
  simp only [certify_eval]
  simp only [eval_bind, gaussianCaptureRadiusProgram_eval,
    gaussianCaptureRadiusProgram_work, gaussianCaptureRadiusProgram_admissible _ _ _ hβ.ne',
    eval_div, eval_mul, admissible_div, admissible_mul, work_div, work_mul,
    true_and, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, hε.ne']
  have hh := strongDegreeProgram_specification (ε/100) (10*gaussianCaptureRadius k U β/ε)
    (by positivity) (by linarith) (krylovDegree_target_ge_one k U β ε hk hU hβ hβ' hε hε')
  exact ⟨hh.1, by rw [hh.2.1]; simp only [krylovDegree]; omega, hh.2.2⟩

end
end HierarchicalAbsoluteSpectral
