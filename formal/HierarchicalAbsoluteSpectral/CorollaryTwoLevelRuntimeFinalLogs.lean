import HierarchicalAbsoluteSpectral.CorollaryTwoLevelDegrees
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelBudgets
import HierarchicalAbsoluteSpectral.BaseFixedLeafCost
import HierarchicalAbsoluteSpectral.BaseCost

/-! Uniform logarithmic budgets for the actual two-level factor actions and
the final Gaussian degree. All bounds hold for every computed support. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
variable {N m r : ℕ}

theorem twoLevelRuntime_rounded_log_inverse (x : ℝ) (a b : ℕ)
    (hx : 2 ≤ x) (hb : 1 ≤ b) :
    Real.log (1/twoLevelRoundedPower x a b) ≤ ((a:ℝ)/(b:ℝ)+2)*Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hpos := twoLevelRoundedPower_positive x a b
  have hlo := (twoLevelRoundedPower_bounds x a b hx1 hb).1
  have hi : 1/twoLevelRoundedPower x a b ≤ 4*x^((a:ℝ)/(b:ℝ)) := by
    calc
      _ ≤ 1/(x^(-(a:ℝ)/(b:ℝ))/4) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hlo
      _ = _ := by rw [neg_div,Real.rpow_neg hx0.le]; field_simp
  have hl := Real.log_le_log (one_div_pos.mpr hpos) hi
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne',Real.log_rpow hx0] at hl
  have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hx
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  rw [h4] at hl
  nlinarith only [hl,h2]

theorem TwoLevelProblem.runtime_alpha_log (I : TwoLevelProblem N m r) (hm : (2:ℝ) ≤ m) :
    Real.log (1/I.fixed.alpha) ≤ 36*Real.log m := by
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hm0 : (0:ℝ) < m := by linarith
  have hp : (m:ℝ)^(107/300:ℝ) ≤ m := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1
      (show (107/300:ℝ) ≤ 1 by norm_num)
  have hi : 1/I.fixed.alpha ≤ 20000000000*(m:ℝ) := by
    have h := I.inverse_alpha_bound
    have hmul := mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ 14804000000 by norm_num)
    nlinarith
  have hl := Real.log_le_log (one_div_pos.mpr I.fixed.alpha_positive) hi
  rw [Real.log_mul (by norm_num) hm0.ne'] at hl
  have hC : Real.log (20000000000:ℝ) ≤ 35*Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 20000000000)
      (by norm_num : (20000000000:ℝ) ≤ 2^35)
    rwa [Real.log_pow] at h
  have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hm
  nlinarith only [hl,hC,h2]

theorem TwoLevelProblem.runtime_mass_log (I : TwoLevelProblem N m r) (hm : (2:ℝ) ≤ m) :
    Real.log (1/I.fixed.massAccuracy) ≤ 39*Real.log m := by
  have hα := I.runtime_alpha_log hm
  have hh := twoLevelRuntime_rounded_log_inverse (m:ℝ) 1 12 hm (by norm_num)
  change Real.log (1/twoLevelH1 m) ≤ _ at hh
  have hmass : I.fixed.massAccuracy = I.fixed.alpha*twoLevelH1 m := by
    unfold FixedProblem.massAccuracy FixedProblem.alpha literalFinalMass literalFinalAlpha
    rw [TwoLevelProblem.fixed_accuracy]
    simp only [twoLevelAccuracy,one_ne_zero,ite_false]
    field_simp [(twoLevelParameters_positive m).2.1.ne']
  rw [hmass,one_div,Real.log_inv,Real.log_mul I.fixed.alpha_positive.ne'
    (twoLevelParameters_positive m).2.1.ne']
  rw [one_div,Real.log_inv] at hα hh
  have hlog : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by linarith)
  norm_num only [Nat.cast_ofNat] at hh
  nlinarith only [hα,hh,hlog]

theorem TwoLevelProblem.runtime_true_neumann_log (I : TwoLevelProblem N m r)
    (hm : (2:ℝ) ≤ m) : 1+4*Real.log (1/I.fixed.massAccuracy) ≤ 158*Real.log m := by
  have h := I.runtime_mass_log hm
  have hlog : (1/2:ℝ) ≤ Real.log (m:ℝ) :=
    family_log_two_lower.trans (Real.log_le_log (by norm_num : (0:ℝ) < 2) hm)
  nlinarith only [h,hlog]

theorem TwoLevelProblem.runtime_fine_neumann_log (I : TwoLevelProblem N m r)
    (hm : (2:ℝ) ≤ m) : mainFineNeumannLog I.fixed 0 ≤ 42*Real.log m := by
  have h := twoLevelRuntime_rounded_log_inverse (m:ℝ) 1 12 hm (by norm_num)
  have hh := (twoLevelParameters_positive m).2.1
  have h100 : Real.log (100:ℝ) ≤ 7*Real.log 2 := by
    have hl := Real.log_le_log (by norm_num : (0:ℝ) < 100)
      (by norm_num : (100:ℝ) ≤ 2^7)
    rwa [Real.log_pow] at hl
  have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hm
  have hlog : (1/2:ℝ) ≤ Real.log (m:ℝ) := family_log_two_lower.trans h2
  have he : Real.log (1/(twoLevelH1 m/100)) = Real.log 100+Real.log (1/twoLevelH1 m) := by
    rw [one_div,Real.log_inv,Real.log_div hh.ne' (by norm_num),one_div,Real.log_inv]
    ring
  simp only [mainFineNeumannLog,safeAccuracy,Nat.zero_add,Nat.min_self,
    TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,one_ne_zero,ite_false]
  rw [he]
  change Real.log (1/twoLevelH1 m) ≤ _ at h
  norm_num only [Nat.cast_ofNat] at h
  nlinarith only [h,h100,h2,hlog]

theorem TwoLevelProblem.runtime_inverse_accuracy_ratio (I : TwoLevelProblem N m r) :
    I.fixed.accuracy 0/I.fixed.accuracy 1 ≤ 4*(m:ℝ)^(1/75:ℝ) := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast I.core_positive
  have h := twoLevelRoundedPower_ratio_le (m:ℝ) 7 100 1 12 hm (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at h
  simpa only [TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,ite_true,one_ne_zero,ite_false,
    twoLevelH0,twoLevelH1,show (1/12:ℝ)-7/100 = 1/75 by norm_num] using h

theorem TwoLevelProblem.runtime_refinement_log (I : TwoLevelProblem N m r)
    (hm : (2:ℝ) ≤ m) : fixedRefinementLog I.fixed ≤ 32*Real.log m := by
  have h0 := (twoLevelParameters_positive m).1
  have h1 := (twoLevelParameters_positive m).2.1
  have hh1 := twoLevelRuntime_rounded_log_inverse (m:ℝ) 1 12 hm (by norm_num)
  have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hm
  have hlog : (1/2:ℝ) ≤ Real.log (m:ℝ) := family_log_two_lower.trans h2
  have hscale : Real.log (1/twoLevelH1 m) ≤ 3*Real.log m := by
    change Real.log (1/twoLevelH1 m) ≤ _ at hh1
    norm_num only [Nat.cast_ofNat] at hh1
    nlinarith only [hh1,hlog]
  have hH : twoLevelH0 m ≤ 1 := by
    have hb := (twoLevelMinimumCore_spec m I.core_large).2.1
    linarith
  have hbudget := family_interpolation_log_budget (twoLevelH1 m) (twoLevelH1 m)
    (twoLevelH0 m) (m:ℝ) 3 0 1 h1 h1 h0 le_rfl hH (by omega) h2 hscale
      (by norm_num only [Nat.cast_one]; nlinarith only [h2,hlog])
  have heps : 0 < twoLevelH1 m/twoLevelH0 m := div_pos h1 h0
  have hless : refinementLogBudget (twoLevelH1 m/twoLevelH0 m) (twoLevelH1 m) (hierarchyUpper 0) ≤
      Real.log (1/((twoLevelH1 m/(1000000*(1+(2:ℝ)^0)))*(twoLevelH1 m/twoLevelH0 m))) := by
    apply Real.log_le_log (by unfold refinementTolerance hierarchyUpper; positivity)
    apply one_div_le_one_div_of_le (by positivity)
    simp only [refinementTolerance,hierarchyUpper,pow_zero]
    nlinarith [div_pos h1 (show (0:ℝ) < 1000000*(1+1) by norm_num)]
  have hsmall : refinementLogBudget (twoLevelH1 m/twoLevelH0 m) (twoLevelH1 m) (hierarchyUpper 0) ≤
      30*Real.log m := hless.trans (by norm_num at hbudget ⊢; exact hbudget)
  simp only [fixedRefinementLog,Fin.sum_univ_one,Fin.val_zero,Nat.zero_add,
    TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,ite_true,one_ne_zero,ite_false]
  nlinarith only [hsmall,hlog]

theorem TwoLevelProblem.runtime_refinement_multiplier (I : TwoLevelProblem N m r)
    (hm : (2:ℝ) ≤ m) :
    fixedRefinementCostMultiplier I.fixed ≤ 204800000000000*(Real.log m)^2 := by
  have h := I.runtime_refinement_log hm
  have h0 := fixedRefinementLog_ge_one I.fixed
  unfold fixedRefinementCostMultiplier
  nlinarith [sq_nonneg (32*Real.log (m:ℝ)-fixedRefinementLog I.fixed)]

def twoLevelRuntimeStrongDegree (I : TwoLevelProblem N m r) (k : ℕ) (hk : 1 ≤ k) : ℕ :=
  strongGaussianDegree k (mainConditionBound I.fixed) I.fixed.singleFailure I.fixed.alpha hk
    (mainConditionBound_ge_one _) (div_pos I.delta_positive (by norm_num))
    (by change I.delta/20 ≤ 1; linarith [I.delta_lt_one]) I.fixed.alpha_positive
    (by have h := I.fixed.final_budget.alpha_small; change I.fixed.alpha ≤ _ at h; linarith)

theorem twoLevelRuntimeStrongDegree_eq_main (I : TwoLevelProblem N m r)
    (S : StoredSketches N m N 1) (C : MainSupportData S) (hk : 1 ≤ C.pair.dimension) :
    twoLevelRuntimeStrongDegree I C.pair.dimension hk = mainStrongDegree I.fixed S C hk := rfl

theorem TwoLevelProblem.runtime_strong_log (I : TwoLevelProblem N m r)
    (c : ℝ) (hm : (2:ℝ) ≤ m) (hδ : (m:ℝ)^(-c) ≤ I.delta)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    Real.log (4*gaussianCaptureRadius k (mainConditionBound I.fixed) I.fixed.singleFailure/I.fixed.alpha) ≤
      (3*c+122)*Real.log m := by
  have hβ : 0 < I.fixed.singleFailure := div_pos I.delta_positive (by norm_num)
  have hα := I.fixed.alpha_positive
  have hU := mainConditionBound_ge_one I.fixed
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hQ := I.query_log_bound k hk hkm hm
  have hB := I.singleFailure_log_bound c (Real.log_le_log (by norm_num) hm) hδ
  have he : 4*gaussianCaptureRadius k (mainConditionBound I.fixed) I.fixed.singleFailure/I.fixed.alpha =
      (20*gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2)/(I.fixed.alpha/100))*
        (1/I.fixed.singleFailure)^3/4000 := by
    unfold gaussianCaptureRadius
    field_simp
    ring
  rw [he,Real.log_div (by unfold gaussianCaptureRadius; positivity) (by norm_num),
    Real.log_mul (by unfold gaussianCaptureRadius; positivity) (by positivity),Real.log_pow]
  have h4000 : 0 ≤ Real.log (4000:ℝ) := Real.log_nonneg (by norm_num)
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hQ,hB,h4000]

theorem twoLevelRuntimeStrongDegree_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hc : 0 ≤ c) (hm : (2:ℝ) ≤ m) (hδ : (m:ℝ)^(-c) ≤ I.delta)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    (twoLevelRuntimeStrongDegree I k hk:ℝ) ≤
      400000*(3*c+122)*(m:ℝ)^(107/600:ℝ)*Real.log m+1 := by
  have hβ : 0 < I.fixed.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.fixed.singleFailure ≤ 1 := by change I.delta/20 ≤ 1; linarith [I.delta_lt_one]
  have hα := I.fixed.alpha_positive
  have hα1 : I.fixed.alpha ≤ 1 := by
    have h := I.fixed.final_budget.alpha_small
    change I.fixed.alpha ≤ _ at h
    linarith
  have hq := strongGaussianDegree_bound k (mainConditionBound I.fixed) I.fixed.singleFailure
    I.fixed.alpha hk (mainConditionBound_ge_one _) hβ hβ1 hα hα1
  change (twoLevelRuntimeStrongDegree I k hk:ℝ) ≤ _ at hq
  have hlog := I.runtime_strong_log c hm hδ k hk hkm
  have hlog0 : 0 ≤ Real.log (4*gaussianCaptureRadius k (mainConditionBound I.fixed)
      I.fixed.singleFailure/I.fixed.alpha) := by
    apply Real.log_nonneg
    have hR := gaussianCaptureRadius_ge_one k (mainConditionBound I.fixed) I.fixed.singleFailure
      hk (mainConditionBound_ge_one _) hβ hβ1
    apply (le_div_iff₀ hα).mpr
    linarith
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hlog (show (0:ℝ) ≤ 2 by norm_num))
    I.inverse_alpha_sqrt_bound (by positivity : 0 ≤ 1/Real.sqrt I.fixed.alpha)
      (by positivity : 0 ≤ 2*((3*c+122)*Real.log (m:ℝ)))
  apply hq.trans
  have he : 2*Real.log (4*gaussianCaptureRadius k (mainConditionBound I.fixed)
      I.fixed.singleFailure/I.fixed.alpha)/Real.sqrt I.fixed.alpha =
      (2*Real.log (4*gaussianCaptureRadius k (mainConditionBound I.fixed)
        I.fixed.singleFailure/I.fixed.alpha))*(1/Real.sqrt I.fixed.alpha) := by ring
  rw [he]
  nlinarith only [hmul]

theorem twoLevelRuntimeStrongDegree_eventually (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → ∀ (k : ℕ) (hk : 1 ≤ k), k ≤ m →
        (twoLevelRuntimeStrongDegree I k hk:ℝ) ≤ (m:ℝ)^((107/600:ℝ)+ε) := by
  let K : ℝ := 400000*(3*c+122)+1
  have hcost := family_core_polylog_absorbed K 1 ((107/600:ℝ)+ε) (107/600)
    (by dsimp [K]; positivity) (by linarith)
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually hcost,eventually_ge_atTop (2:ℕ),
    hcast.eventually (eventually_ge_atTop (Real.exp 1))] with m hbound hm hmexp N r I hδ k hk hkm
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 1 ≤ Real.log (m:ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1) hmexp
    rwa [Real.log_exp] at h
  have hpow : 1 ≤ (m:ℝ)^(107/600:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hprod : 1 ≤ (m:ℝ)^(107/600:ℝ)*Real.log m := by nlinarith
  have hq := twoLevelRuntimeStrongDegree_bound I c hc hmR hδ k hk hkm
  have hh : (twoLevelRuntimeStrongDegree I k hk:ℝ) ≤ K*(m:ℝ)^(107/600:ℝ)*Real.log m := by
    dsimp [K]
    nlinarith only [hq,hprod]
  exact hh.trans (by simpa only [Real.rpow_one] using hbound)

end
end HierarchicalAbsoluteSpectral
