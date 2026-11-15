import HierarchicalAbsoluteSpectral.Schedule

/-! The fully unfolded exp(O((log log m)^2)) overhead is subpolynomial,
with the quantifier over every positive exponent made explicit. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter Asymptotics

theorem family_shifted_loglog_sq_isLittleO_log :
    (fun m : ℝ => (1+Real.log (Real.log m))^2) =o[atTop] Real.log := by
  have hconst : (fun _ : ℝ => (1 : ℝ)) =o[atTop] Real.log := by
    simpa only [Function.comp_def,id_eq] using
      (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto Real.tendsto_log_atTop
  have hlog : (fun m : ℝ => Real.log (Real.log m)) =o[atTop] Real.log := by
    simpa only [Function.comp_def,id_eq] using
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hh := (hconst.add (hlog.const_mul_left 2)).add loglog_sq_isLittleO_log
  apply hh.congr_left
  intro m
  ring

theorem family_exp_loglog_eventually_le_rpow (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop,
      Real.exp (K*(1+Real.log (Real.log m))^2) ≤ m^ε := by
  have ho := family_shifted_loglog_sq_isLittleO_log.const_mul_left K
  have hb := ho.bound hε
  filter_upwards [hb,eventually_ge_atTop (Real.exp 1)] with m hm hm1
  have hp : 0 < m := (Real.exp_pos 1).trans_le hm1
  have hl : 0 ≤ Real.log m := by
    apply Real.log_nonneg
    exact (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans hm1
  have hh : K*(1+Real.log (Real.log m))^2 ≤ ε*Real.log m := by
    calc
      _ ≤ |K*(1+Real.log (Real.log m))^2| := le_abs_self _
      _ ≤ ε*Real.log m := by simpa only [Real.norm_eq_abs,abs_of_nonneg hl] using hm
  rw [Real.rpow_def_of_pos hp]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem family_exp_loglog_two_mul_eventually_le_rpow (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop,
      Real.exp (K*(1+Real.log (Real.log (2*m)))^2) ≤ m^ε := by
  have ht : Tendsto (fun m : ℝ => 2*m) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hb := ht.eventually (family_exp_loglog_eventually_le_rpow K (ε/2) (by positivity))
  filter_upwards [hb,eventually_ge_atTop (2 : ℝ)] with m hm hm2
  have hp : 0 < m := by linarith
  have hl : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2
  have hlog : Real.log (2*m) ≤ 2*Real.log m := by
    rw [Real.log_mul (by norm_num) hp.ne']
    linarith
  apply hm.trans
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2*m),Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  nlinarith

end
end HierarchicalAbsoluteSpectral
