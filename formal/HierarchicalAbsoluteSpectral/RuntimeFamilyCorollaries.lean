import HierarchicalAbsoluteSpectral.RuntimeFamilyAsymptotics
import HierarchicalAbsoluteSpectral.Scalars

/-! Exact exponent comparisons in the growing-depth and optimized examples. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

theorem family_parameter_margins (d : ℝ)
    (hd : (1/8 : ℝ) < d) (hd' : d < (Real.sqrt 2-1)/2) :
    0 < d ∧ d < 1/3 ∧ d < 1/2 ∧ 0 < 2+2*d-9/4 ∧
      1/2+5*d/4 < 1 ∧ 1/2+d < 1 ∧ d*(1+d) < 1/4 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hroot : Real.sqrt 2 < 3/2 := by nlinarith
  have hd0 : 0 < d := by linarith
  have hds : 2*d+1 < Real.sqrt 2 := by linarith
  have hprod : (2*d+1)^2 < 2 := by nlinarith
  refine ⟨hd0,by linarith,by linarith,by linarith,by linarith,by linarith,?_⟩
  nlinarith

theorem family_core_slack_exists (d : ℝ) (hd : (1/8 : ℝ) < d) :
    ∃ ζ : ℝ, 0 < ζ ∧ 9/4+ζ < 2+2*d := by
  refine ⟨(2+2*d-9/4)/2,by linarith,by linarith⟩

theorem family_baseline_exponents (d : ℝ)
    (hd : (1/8 : ℝ) < d) (hd' : d < (Real.sqrt 2-1)/2) :
    2+2*d < 2+9*d/4 ∧ 2+2*d < 2+d+1/(4*(1+d)) ∧
      13/8+41*d/16 < 2+9*d/4 ∧
      3*(1/2+5*d/4) < 2+9*d/4 ∧
      (2+9*d/4)/(1+d)-2 = d/(4*(1+d)) ∧
      (2+d+1/(4*(1+d)))/(1+d)-2 = 1/(4*(1+d)^2)-d/(1+d) := by
  have hm := family_parameter_margins d hd hd'
  have hp : 0 < 1+d := by linarith [hm.1]
  refine ⟨by linarith [hm.1],?_,by linarith [hm.2.1],by linarith [hm.2.1],?_,?_⟩
  · have hh : d < 1/(4*(1+d)) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith [hm.2.2.2.2.2.2])
    linarith
  · field_simp
    <;> ring
  · field_simp
    <;> ring

theorem optimized_total_comparison :
    (2+9*dStar/4)/(1+dStar) = 2+savingStar ∧
    (2+dStar+1/(4*(1+dStar)))/(1+dStar) = 2+savingStar ∧
      (5/2)*dStar/(1+dStar) = 10*savingStar ∧
      0 < savingStar ∧ 0 < alphaStar ∧ alphaStar/2 < 1/2 := by
  have hd := optimized_parameter_in_family
  have hm := family_baseline_exponents dStar hd.1 hd.2
  have hi := optimized_parameters
  have hs : 0 < savingStar := by
    have hp : 0 < 1+dStar := by linarith [hd.1]
    rw [← hi.2.2.2.1]
    exact div_pos (by linarith [hd.1]) (by positivity)
  have ha : 0 < alphaStar := by
    have hp := Real.sqrt_nonneg (5 : ℝ)
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    dsimp [alphaStar]
    nlinarith
  refine ⟨?_,?_,?_,hs,ha,?_⟩
  · linarith [hm.2.2.2.2.1,hi.2.2.2.1]
  · linarith [hm.2.2.2.2.2,hi.2.2.2.2]
  · rw [← hi.2.2.2.1]
    field_simp
    <;> ring
  · linarith [hi.2.2.1]

theorem two_level_example_exact_margins :
    (3362/1425 : ℝ)/(59/50) = 6724/3363 ∧
    (29227553/12390000 : ℝ) < 3362/1425 ∧
    (2831/1200 : ℝ) < 3362/1425 ∧
    (9/4 : ℝ) < 3362/1425 ∧
    (3362/1425 : ℝ) < 59/25 ∧
    (3362/1425 : ℝ)-(2831/1200) = 1/7600 ∧
    (443/600 : ℝ) < 1 ∧ (7/6 : ℝ) < 59/50 ∧ (28/59 : ℝ) < 1/2 := by
  norm_num

end
end HierarchicalAbsoluteSpectral
