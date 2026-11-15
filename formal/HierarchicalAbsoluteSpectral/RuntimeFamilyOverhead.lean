import HierarchicalAbsoluteSpectral.RuntimeFamilyStrongDegree

/-! All depth dependence is displayed explicitly. B and C are polylogarithmic,
the outer degree has a fifth logarithmic power, and only the common action
overhead contributes exp(O((log log m)^2)). -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

theorem familySchedule_power_le_logscale {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (hscale : Real.log (1/s) ≤ D*Real.log m) :
    (2 : ℝ)^out.depth ≤ D*Real.log m := by
  have hp := (out.depth_power_bounds hs hL).2
  have heps : 1 ≤ Real.log 1024 := by
    have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1023)
    norm_num at hh
    linarith
  have hx := (le_div_iff₀ (by linarith : 0 < Real.log 1024)).mp hp
  have hpow : 0 ≤ (2 : ℝ)^out.depth := by positivity
  nlinarith

theorem family_depth_constants_polylog {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (hscale : Real.log (1/s) ≤ D*Real.log m) :
    (2 : ℝ)^(out.depth+1) ≤ 2*D*Real.log m ∧
      (10 : ℝ)^out.depth ≤ (D*Real.log m)^4 ∧
      defectConstant out.depth ≤ 38*(D*Real.log m)^7 ∧
      Real.sqrt (accuracyScale out.depth) ≤ 7000*(D*Real.log m)^4 := by
  have hp := familySchedule_power_le_logscale hs out hL hscale
  have hp0 : 0 ≤ D*Real.log m := (by positivity : (0 : ℝ) ≤ 2^out.depth).trans hp
  have h10 : (10 : ℝ)^out.depth ≤ ((2 : ℝ)^out.depth)^4 := by
    calc
      _ ≤ (16 : ℝ)^out.depth := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = _ := by
        rw [← pow_mul,show out.depth*4 = 4*out.depth by omega,pow_mul]
        norm_num
  have h100 : (100 : ℝ)^out.depth ≤ ((2 : ℝ)^out.depth)^7 := by
    calc
      _ ≤ (128 : ℝ)^out.depth := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = _ := by
        rw [← pow_mul,show out.depth*7 = 7*out.depth by omega,pow_mul]
        norm_num
  have h10bound := h10.trans (pow_le_pow_left₀ (by positivity) hp 4)
  have h100bound := h100.trans (pow_le_pow_left₀ (by positivity) hp 7)
  have hC : defectConstant out.depth ≤ 38*(100 : ℝ)^out.depth := by
    rw [defectConstant_closed]
    have hx : 1 ≤ (100 : ℝ)^out.depth := one_le_pow₀ (by norm_num)
    nlinarith
  refine ⟨?_,h10bound,?_,?_⟩
  · rw [pow_succ]
    nlinarith
  · exact hC.trans (mul_le_mul_of_nonneg_left h100bound (by norm_num))
  · exact (family_accuracyScale_sqrt_bound out.depth).trans
      (mul_le_mul_of_nonneg_left h10bound (by norm_num))

theorem family_actual_overhead_bound {s m D C : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024))
    (hD : 1 ≤ D) (hC : 1 ≤ C) (hm : 1 ≤ Real.log m)
    (hm0 : 0 < m) (hscale : Real.log (1/s) ≤ D*Real.log m) :
    (C*(Real.log (2*m))^2)^out.depth ≤
      Real.exp ((3+2*Real.log D)*(Real.log C+2)*(1+Real.log (Real.log (2*m)))^2) := by
  have hD0 : 0 < D := by linarith
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hm2 : Real.log m ≤ Real.log (2*m) := Real.log_le_log hm0 (by linarith)
  have hell : 1 ≤ Real.log (2*m) := hm.trans hm2
  have hl : 0 ≤ Real.log (Real.log (2*m)) := Real.log_nonneg hell
  have hLbound : (out.depth : ℝ) ≤ (3+2*Real.log D)*(1+Real.log (Real.log (2*m))) := by
    by_cases hL : out.depth = 0
    · rw [hL,Nat.cast_zero]
      positivity
    · have hp := familySchedule_power_le_logscale hs out (by omega) hscale
      have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2^out.depth) hp
      rw [Real.log_pow,Real.log_mul hD0.ne' (by linarith : Real.log m ≠ 0)] at hlog
      have hle := Real.log_le_log (by linarith : 0 < Real.log m) hm2
      have hhalf := (show (1/2 : ℝ) ≤ Real.log 2 by
        have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        norm_num at hh
        linarith)
      have hprod := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg out.depth)
      nlinarith [mul_nonneg hlogD hl]
  exact family_overhead_exp_bound C (Real.log (2*m)) (3+2*Real.log D) out.depth
    hC hell (by positivity) hLbound

theorem family_strong_degree_polylog_bound {s m D Dβ β : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (k : ℕ) (hk : 1 ≤ k) (hkm : (k : ℝ) ≤ m)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hD : 0 ≤ D)
    (hm : Real.log 2 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m)
    (hconfidence : Real.log (1/β) ≤ Dβ*Real.log m) :
    ∃ (hU : 1 ≤ familyCovarianceEnvelope out) (hα : 0 < familyOuterAccuracy out)
      (hα1 : familyOuterAccuracy out ≤ 1),
      (strongGaussianDegree k (familyCovarianceEnvelope out) β (familyOuterAccuracy out)
        hk hU hβ hβ1 hα hα1 : ℝ) ≤
        (448000*(17*D+3*Dβ+60)*D^4)*(1/s^2)*(Real.log m)^5+1 := by
  obtain ⟨hU,hα,hα1,hu⟩ := family_strong_degree_uniform_bound hs out hL k hk hkm hβ hβ1 hD hm hscale hconfidence
  have h10 := (family_depth_constants_polylog hs out hL hscale).2.1
  have hR := gaussianCaptureRadius_ge_one k (familyCovarianceEnvelope out) β hk hU hβ hβ1
  have hlog := family_gaussian_log_budget hs out hL k hk hkm hβ hβ1 hD hm hscale hconfidence
  have hB : 0 ≤ Real.log (4*gaussianCaptureRadius k (familyCovarianceEnvelope out) β/familyOuterAccuracy out) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hα).mpr
    linarith
  have hbudget : 0 ≤ (17*D+3*Dβ+60)*Real.log m := hB.trans hlog
  refine ⟨hU,hα,hα1,hu.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left h10
    (by positivity : 0 ≤ 448000*((17*D+3*Dβ+60)*Real.log m)/s^2)
  convert add_le_add hh (le_refl (1 : ℝ)) using 1 <;> ring

end
end HierarchicalAbsoluteSpectral
