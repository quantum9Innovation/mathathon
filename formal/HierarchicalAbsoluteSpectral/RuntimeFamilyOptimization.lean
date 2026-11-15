import HierarchicalAbsoluteSpectral.RuntimeFamilyCorollaries

/-! The endpoint optimizes the minimum of the two stated comparison gaps.
These are comparisons of available arithmetic upper bounds. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

def krylovComparisonGap (d : ℝ) : ℝ := d/(4*(1+d))
def gramComparisonGap (d : ℝ) : ℝ := 1/(4*(1+d)^2)-d/(1+d)

theorem krylovComparisonGap_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    krylovComparisonGap a ≤ krylovComparisonGap b := by
  have hb : 0 ≤ b := ha.trans hab
  unfold krylovComparisonGap
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem gramComparisonGap_antitone (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    gramComparisonGap b ≤ gramComparisonGap a := by
  have hp : 0 < 1+a := by linarith
  have hq : 0 < 1+b := by linarith
  have hfirst : 1/(4*(1+b)^2) ≤ 1/(4*(1+a)^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hsecond : a/(1+a) ≤ b/(1+b) := by
    apply (div_le_div_iff₀ hp hq).mpr
    nlinarith
  exact sub_le_sub hfirst hsecond

theorem optimized_comparison_gap_value :
    krylovComparisonGap dStar = savingStar ∧ gramComparisonGap dStar = savingStar := by
  exact ⟨optimized_parameters.2.2.2.1,optimized_parameters.2.2.2.2⟩

theorem optimized_comparison_saving_maximal (d : ℝ) (hd : 0 ≤ d) :
    min (krylovComparisonGap d) (gramComparisonGap d) ≤ savingStar := by
  have hs := optimized_comparison_gap_value
  have hdstar : 0 ≤ dStar := by linarith [optimized_parameter_in_family.1]
  by_cases hle : d ≤ dStar
  · exact (min_le_left _ _).trans ((krylovComparisonGap_mono d dStar hd hle).trans_eq hs.1)
  · exact (min_le_right _ _).trans
      ((gramComparisonGap_antitone dStar d hdstar (le_of_lt (lt_of_not_ge hle))).trans_eq hs.2)

theorem optimized_parameter_numerical_bounds :
    (3647/100000 : ℝ) < savingStar ∧ savingStar < 3648/100000 ∧
      (427/1000 : ℝ) < alphaStar/2 ∧ alphaStar/2 < 428/1000 ∧
        (170/1000 : ℝ) < dStar ∧ dStar < 171/1000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  have hlo : (223606/100000 : ℝ) < Real.sqrt 5 := by nlinarith
  have hhi : Real.sqrt 5 < (223607/100000 : ℝ) := by nlinarith
  unfold savingStar alphaStar dStar
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end
end HierarchicalAbsoluteSpectral
