import HierarchicalAbsoluteSpectral.ThresholdHalving

/-! The complete scalar search wrapper computes its own finite iteration cap
by counted halving before running the counted bisection program. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

theorem leastHalvings_mono (x y ε : ℝ) (hε : 0 < ε) (hxy : x ≤ y) :
    leastHalvings x ε hε ≤ leastHalvings y ε hε := by
  apply leastHalvings_le
  exact (div_le_div_of_nonneg_right hxy (pow_nonneg (by norm_num) _)).trans
    (leastHalvings_spec y ε hε)

def thresholdSearchAuto (query : ℝ → ArithmeticProgram ThresholdDecision)
    (ε : ℝ) (hε : 0 < ε) (l u : ℝ) : ArithmeticProgram ThresholdSearchResult := do
  let width ← sub u l
  let relative ← div width l
  let n ← scalarHalving relative ε hε
  thresholdSearch query ε n l u

theorem thresholdSearchAuto_eval (query : ℝ → ArithmeticProgram ThresholdDecision)
    (ε : ℝ) (hε : 0 < ε) (l u : ℝ) :
    (thresholdSearchAuto query ε hε l u).eval =
      (thresholdSearch query ε (leastHalvings ((u-l)/l) ε hε) l u).eval := by
  simp only [thresholdSearchAuto, eval_bind, eval_sub, eval_div,
    (scalarHalving_checked ((u-l)/l) ε hε).1]

theorem thresholdSearchAuto_correct (query : ℝ → ArithmeticProgram ThresholdDecision)
    (target ε : ℝ) (hε : 0 < ε) (near : ℝ → Prop)
    (hsound : ThresholdSearchSound (fun t => (query t).eval) target near)
    (l u : ℝ) (hl : 0 < l) (hlo : l ≤ target) (hhi : target ≤ u) :
    ThresholdSearchConclusion target ε near (thresholdSearchAuto query ε hε l u).eval := by
  rw [thresholdSearchAuto_eval]
  apply thresholdSearch_correct query target ε near hsound hε.le _ l u hl hlo hhi
  have hs := leastHalvings_spec ((u-l)/l) ε hε
  apply (div_le_iff₀ hl).mp
  have hp : 0 < (2:ℝ)^(leastHalvings ((u-l)/l) ε hε) := pow_pos (by norm_num) _
  have hh := (div_le_iff₀ hp).mp hs
  convert hh using 1 <;> ring

theorem thresholdSearchAuto_admissible (query : ℝ → ArithmeticProgram ThresholdDecision)
    (hquery : ∀ t, 0 < t → (query t).admissible)
    (ε : ℝ) (hε : 0 < ε) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    (thresholdSearchAuto query ε hε l u).admissible := by
  simp only [thresholdSearchAuto, admissible_bind, admissible_sub, admissible_div,
    eval_sub, eval_div, true_and]
  refine ⟨ne_of_gt hl, (scalarHalving_checked _ ε hε).2.2, ?_⟩
  exact thresholdSearch_admissible query hquery ε _ l u hl hlu

theorem thresholdSearchAuto_work_le (query : ℝ → ArithmeticProgram ThresholdDecision)
    (cost : ℕ) (hquery : ∀ t, 0 < t → (query t).work ≤ cost)
    (ε : ℝ) (hε : 0 < ε) (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    (thresholdSearchAuto query ε hε l u).work ≤
      3+leastHalvings ((u-l)/l) ε hε*(7+cost) := by
  simp only [thresholdSearchAuto, work_bind, work_sub, work_div, eval_sub, eval_div,
    (scalarHalving_checked ((u-l)/l) ε hε).1,
    (scalarHalving_checked ((u-l)/l) ε hε).2.1]
  have hh := thresholdSearch_work_le query cost hquery ε
    (leastHalvings ((u-l)/l) ε hε) l u hl hlu
  nlinarith only [hh]

end
end HierarchicalAbsoluteSpectral
