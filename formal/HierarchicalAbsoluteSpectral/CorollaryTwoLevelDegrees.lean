import HierarchicalAbsoluteSpectral.CorollaryTwoLevelProgram
import HierarchicalAbsoluteSpectral.MainStatementsQueryViews

/-! Uniform bounds for the degree selected by the actual scalar Krylov
search, including the covariance logarithm and every support dimension. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter
variable {N m r : ℕ}

theorem twoLevel_inverse_accuracies (x : ℝ) (hx : 1 ≤ x) :
    1/twoLevelH0 x ≤ 4*x^(7/100:ℝ) ∧ 1/twoLevelH1 x ≤ 4*x^(1/12:ℝ) := by
  have hx0 : 0 < x := by linarith
  have hb := twoLevelParameters_bounds x hx
  constructor
  · calc
      _ ≤ 1/(x^(-(7/100:ℝ))/4) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hb.1
      _ = _ := by rw [Real.rpow_neg hx0.le]; field_simp <;> ring
  · calc
      _ ≤ 1/(x^(-(1/12:ℝ))/4) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hb.2.2.1
      _ = _ := by rw [Real.rpow_neg hx0.le]; field_simp <;> ring

theorem TwoLevelProblem.inverse_alpha_bound (I : TwoLevelProblem N m r) :
    1/I.fixed.alpha ≤ 14804000000*(m:ℝ)^(107/300:ℝ) := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast I.core_positive
  have hratio := (twoLevelParameters_ratios m hm).2.2
  have ht := (twoLevelParameters_positive m).2.2
  have hh := (twoLevelParameters_positive m).2.1
  have he : 1/I.fixed.alpha = 3701000000*(twoLevelH1 m/twoLevelTheta m) := by
    simp only [FixedProblem.alpha,literalFinalAlpha,TwoLevelProblem.fixed_theta,
      TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,one_ne_zero,ite_false,hierarchyConstant]
    norm_num
    field_simp
    <;> ring
  rw [he]
  nlinarith

theorem TwoLevelProblem.inverse_alpha_sqrt_bound (I : TwoLevelProblem N m r) :
    1/Real.sqrt I.fixed.alpha ≤ 200000*(m:ℝ)^(107/600:ℝ) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast I.core_positive
  have hp := I.fixed.alpha_positive
  have he : ((m:ℝ)^(107/600:ℝ))^2 = (m:ℝ)^(107/300:ℝ) := by
    rw [← Real.rpow_two,← Real.rpow_mul hm0.le]
    norm_num
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow,one_pow,Real.sq_sqrt hp.le,mul_pow,he]
  have h := I.inverse_alpha_bound
  have hmPow : 0 ≤ (m:ℝ)^(107/300:ℝ) := Real.rpow_nonneg hm0.le _
  exact h.trans (mul_le_mul_of_nonneg_right (by norm_num : (14804000000:ℝ) ≤ 200000^2) hmPow)

theorem TwoLevelProblem.condition_bound (I : TwoLevelProblem N m r) :
    mainConditionBound I.fixed ≤ 6*(m:ℝ) := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast I.core_positive
  have hm0 : (0:ℝ) < m := by linarith
  have hh0 := (twoLevelParameters_positive (m:ℝ)).1
  have hh1 := (twoLevelParameters_positive (m:ℝ)).2.1
  have h := twoLevel_inverse_accuracies m hm
  have hP : 1 ≤ (m:ℝ)^(1/12:ℝ) := Real.one_le_rpow hm (by norm_num)
  have hQ : 1 ≤ (m:ℝ)^(7/100:ℝ) := Real.one_le_rpow hm (by norm_num)
  have hleft : 1+2/(8*twoLevelH1 m) ≤ 2*(m:ℝ)^(1/12:ℝ) := by
    have he : 2/(8*twoLevelH1 m) = (1/twoLevelH1 m)/4 := by ring
    rw [he]
    linarith [h.2]
  have hright : 1+4/(8*twoLevelH0 m) ≤ 3*(m:ℝ)^(7/100:ℝ) := by
    have he : 4/(8*twoLevelH0 m) = (1/twoLevelH0 m)/2 := by ring
    rw [he]
    linarith [h.1]
  have hprod := mul_le_mul hleft hright (by positivity : 0 ≤ 1+4/(8*twoLevelH0 m)) (by positivity)
  have he : (2*(m:ℝ)^(1/12:ℝ))*(3*(m:ℝ)^(7/100:ℝ)) =
      6*(m:ℝ)^(23/150:ℝ) := by
    rw [show (2*(m:ℝ)^(1/12:ℝ))*(3*(m:ℝ)^(7/100:ℝ)) =
      6*((m:ℝ)^(1/12:ℝ)*(m:ℝ)^(7/100:ℝ)) by ring,← Real.rpow_add hm0]
    norm_num
  rw [he] at hprod
  have hpow : (m:ℝ)^(23/150:ℝ) ≤ m := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm (show (23/150:ℝ) ≤ 1 by norm_num)
  have hu : mainConditionBound I.fixed =
      (1+2/(8*twoLevelH1 m))*(1+4/(8*twoLevelH0 m)) := by
    simp only [mainConditionBound,TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,hierarchyUpper]
    norm_num
  rw [hu]
  exact hprod.trans (by linarith)

def twoLevelQueryDegree (I : TwoLevelProblem N m r) (k : ℕ) (hk : 1 ≤ k) : ℕ :=
  krylovDegree k (mainConditionBound I.fixed) (1/2) (I.fixed.alpha/100)
    hk (mainConditionBound_ge_one I.fixed) (by norm_num) (by norm_num)
    (by positivity [I.fixed.alpha_positive])
    (by have hh := I.fixed.final_budget.alpha_small; change I.fixed.alpha ≤ _ at hh; linarith)

theorem twoLevelQueryDegree_eq_main (I : TwoLevelProblem N m r)
    (S : StoredSketches N m N 1) (C : MainSupportData S) (hr : r < C.pair.dimension) :
    twoLevelQueryDegree I C.pair.dimension (by omega) = mainKrylovDegree I.fixed S C hr := rfl

theorem TwoLevelProblem.query_log_bound (I : TwoLevelProblem N m r)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (hm2 : (2:ℝ) ≤ m) :
    Real.log (20*gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2)/(I.fixed.alpha/100)) ≤
      107*Real.log m := by
  have hm : (1:ℝ) ≤ m := by linarith
  have hm0 : (0:ℝ) < m := by linarith
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hkmR : (k:ℝ) ≤ m := by exact_mod_cast hkm
  have hU := mainConditionBound_ge_one I.fixed
  have ha := I.fixed.alpha_positive
  have hi : 1/I.fixed.alpha ≤ 20000000000*(m:ℝ) := by
    apply I.inverse_alpha_bound.trans
    have hp : (m:ℝ)^(107/300:ℝ) ≤ m := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm (show (107/300:ℝ) ≤ 1 by norm_num)
    nlinarith
  have hR : gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2) ≤ (1200*(m:ℝ)^2)^3 := by
    unfold gaussianCaptureRadius
    apply pow_le_pow_left₀ (by positivity)
    have hprod := mul_le_mul hkmR I.condition_bound (by linarith : 0 ≤ mainConditionBound I.fixed) hm0.le
    nlinarith
  have hpoly : 20*gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2)/(I.fixed.alpha/100) ≤
      (2:ℝ)^100*(m:ℝ)^7 := by
    calc
      _ = 2000*gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2)*(1/I.fixed.alpha) := by ring
      _ ≤ 2000*(1200*(m:ℝ)^2)^3*(20000000000*(m:ℝ)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hR (by norm_num)
        · exact hi
        · positivity
        · positivity
      _ ≤ _ := by
        ring_nf
        nlinarith [pow_nonneg hm0.le 7]
  have hlog := Real.log_le_log (show 0 <
    20*gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2)/(I.fixed.alpha/100) by
      unfold gaussianCaptureRadius
      positivity) hpoly
  rw [Real.log_mul (by positivity) (pow_pos hm0 _).ne',Real.log_pow,Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hl2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hm2
  nlinarith only [hlog,hl2]

theorem twoLevelQueryDegree_bound (I : TwoLevelProblem N m r)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (hm2 : (2:ℝ) ≤ m) :
    (twoLevelQueryDegree I k hk:ℝ) ≤ 4280000000*(m:ℝ)^(107/600:ℝ)*Real.log m+1 := by
  have hm0 : (0:ℝ) < m := by linarith
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have ha := I.fixed.alpha_positive
  have hε0 : 0 < I.fixed.alpha/100 := by positivity
  have hε1 : I.fixed.alpha/100 ≤ 1 := by
    have hh := I.fixed.final_budget.alpha_small
    change I.fixed.alpha ≤ _ at hh
    linarith
  have hq := krylovDegree_bound k (mainConditionBound I.fixed) (1/2) (I.fixed.alpha/100) hk
    (mainConditionBound_ge_one I.fixed) (by norm_num) (by norm_num) hε0 hε1
  change (twoLevelQueryDegree I k hk:ℝ) ≤ _ at hq
  have hs : Real.sqrt ((I.fixed.alpha/100)/100) = Real.sqrt I.fixed.alpha/100 := by
    rw [div_div,Real.sqrt_div ha.le]
    norm_num
  have hroot : 1/Real.sqrt ((I.fixed.alpha/100)/100) ≤ 20000000*(m:ℝ)^(107/600:ℝ) := by
    rw [hs]
    have he : 1/(Real.sqrt I.fixed.alpha/100) = 100*(1/Real.sqrt I.fixed.alpha) := by ring
    rw [he]
    nlinarith [I.inverse_alpha_sqrt_bound]
  have hb := I.query_log_bound k hk hkm hm2
  have hB0 : 0 ≤ Real.log (20*gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2)/(I.fixed.alpha/100)) := by
    apply Real.log_nonneg
    have hR := gaussianCaptureRadius_ge_one k (mainConditionBound I.fixed) (1/2) hk
      (mainConditionBound_ge_one I.fixed) (by norm_num) (by norm_num)
    apply (le_div_iff₀ hε0).mpr
    nlinarith only [hR,hε1]
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2)) hroot
    (by positivity : 0 ≤ 1/Real.sqrt ((I.fixed.alpha/100)/100)) (by positivity)
  calc
    _ ≤ 2*Real.log (20*gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2)/(I.fixed.alpha/100))/
        Real.sqrt ((I.fixed.alpha/100)/100)+1 := hq
    _ = (2*Real.log (20*gaussianCaptureRadius k (mainConditionBound I.fixed) (1/2)/(I.fixed.alpha/100)))*
        (1/Real.sqrt ((I.fixed.alpha/100)/100))+1 := by ring
    _ ≤ (2*(107*Real.log m))*(20000000*(m:ℝ)^(107/600:ℝ))+1 := add_le_add hprod le_rfl
    _ = _ := by ring

theorem twoLevelQueryDegree_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r)
      (k : ℕ) (hk : 1 ≤ k), k ≤ m →
        (twoLevelQueryDegree I k hk:ℝ) ≤ (m:ℝ)^((107/600:ℝ)+ε) := by
  have hcost := family_core_polylog_absorbed 4280000001 1 ((107/600:ℝ)+ε)
    (107/600) (by norm_num) (by linarith)
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually hcost,hcast.eventually (eventually_ge_atTop (2:ℝ)),
    hcast.eventually (eventually_ge_atTop (Real.exp 1))]
    with m hc hm2 hmexp N r I k hk hkm
  have hm0 : (0:ℝ) < m := by linarith
  have hlog : 1 ≤ Real.log (m:ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1) hmexp
    rwa [Real.log_exp] at h
  have hpow : 1 ≤ (m:ℝ)^(107/600:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hprod : 1 ≤ (m:ℝ)^(107/600:ℝ)*Real.log m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) (sub_nonneg.mpr hlog)]
  have hq := twoLevelQueryDegree_bound I k hk hkm hm2
  have hq' : (twoLevelQueryDegree I k hk:ℝ) ≤
      4280000001*(m:ℝ)^(107/600:ℝ)*Real.log m := by nlinarith
  exact hq'.trans (by simpa only [Real.rpow_one] using hc)

/-- Uniform raw-width safety for every computed support, hence every
random outcome; no good sketch or covariance event is assumed. -/
theorem twoLevel_raw_width_eventually :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r)
      (k : ℕ) (hk : 1 ≤ k), k ≤ m →
        (2*twoLevelQueryDegree I k hk+1)*(r+1) < m := by
  let ε : ℝ := 157/1200
  have hε : 0 < ε := by norm_num [ε]
  have hcap := family_const_mul_rpow_lt_linear 9 ((443/600:ℝ)+ε) (by norm_num [ε])
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [twoLevelQueryDegree_eventually ε hε,hcast.eventually hcap,
    hcast.eventually (eventually_ge_atTop (1:ℝ))] with m hq hc hm N r I k hk hkm
  have hm0 : (0:ℝ) < m := by linarith
  have hqi := hq N r I k hk hkm
  have hpow : 1 ≤ (m:ℝ)^((107/600:ℝ)+ε) := Real.one_le_rpow hm (by norm_num [ε])
  have hfirst : 2*(twoLevelQueryDegree I k hk:ℝ)+1 ≤ 3*(m:ℝ)^((107/600:ℝ)+ε) := by linarith
  have hsecond := twoLevel_rounded_rank_width m r I.core_positive I.rank_le_power
  have hprod := mul_le_mul hfirst hsecond (by positivity : 0 ≤ (r:ℝ)+1) (by positivity)
  have he : (3*(m:ℝ)^((107/600:ℝ)+ε))*(3*(m:ℝ)^(14/25:ℝ)) =
      9*(m:ℝ)^((443/600:ℝ)+ε) := by
    rw [show (3*(m:ℝ)^((107/600:ℝ)+ε))*(3*(m:ℝ)^(14/25:ℝ)) =
      9*((m:ℝ)^((107/600:ℝ)+ε)*(m:ℝ)^(14/25:ℝ)) by ring,← Real.rpow_add hm0]
    congr 2
    ring
  rw [he] at hprod
  have hfinal : (2*(twoLevelQueryDegree I k hk:ℝ)+1)*((r:ℝ)+1) < m := hprod.trans_lt hc
  exact_mod_cast hfinal

theorem twoLevel_main_raw_width_eventually :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r)
      (S : StoredSketches N m N 1) (C : MainSupportData S) (hr : r < C.pair.dimension),
        (2*mainKrylovDegree I.fixed S C hr+1)*(r+1) < m := by
  filter_upwards [twoLevel_raw_width_eventually] with m hm N r I S C hr
  have hk : 1 ≤ C.pair.dimension := by omega
  have h := hm N r I C.pair.dimension hk C.pair.dimension_le_fin
  rwa [twoLevelQueryDegree_eq_main I S C hr] at h

end
end HierarchicalAbsoluteSpectral
