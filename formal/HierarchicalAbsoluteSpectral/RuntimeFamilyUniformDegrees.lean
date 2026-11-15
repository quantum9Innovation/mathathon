import HierarchicalAbsoluteSpectral.RuntimeFamilyBounds
import HierarchicalAbsoluteSpectral.DyadicDegree

/-! A single logarithmic budget controls every actual interpolation level,
including the depth-dependent B constants in the manuscript's tolerances. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section

theorem familySchedule_depth_log_linear {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (hscale : Real.log (1/s) ≤ D*Real.log m) :
    (out.depth : ℝ)*Real.log 2 ≤ D*Real.log m := by
  have hp := (out.depth_power_bounds hs hL).2
  have heps : 1 ≤ Real.log 1024 := by
    have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1023)
    norm_num at hh
    linarith
  have hpow : 0 < (2 : ℝ)^out.depth := by positivity
  have hg0 : 0 < Real.log (1/s) := by
    have hh := (le_div_iff₀ (by linarith : 0 < Real.log 1024)).mp hp
    nlinarith
  have hpow' : (2 : ℝ)^out.depth ≤ Real.log (1/s) := by
    have hh := (le_div_iff₀ (by linarith : 0 < Real.log 1024)).mp hp
    nlinarith
  have hl := Real.log_le_log hpow hpow'
  rw [Real.log_pow] at hl
  have hlog := Real.log_le_sub_one_of_pos hg0
  linarith

theorem family_interpolation_log_budget (s h H m D : ℝ) (J L : ℕ)
    (hs : 0 < s) (hh : 0 < h) (hH : 0 < H) (hhlo : s ≤ h) (hHhi : H ≤ 1)
    (hJ : J ≤ L) (hm : Real.log 2 ≤ Real.log m)
    (hscale : Real.log (1/s) ≤ D*Real.log m)
    (hdepth : (L : ℝ)*Real.log 2 ≤ D*Real.log m) :
    Real.log (1/((h/(1000000*(1+(2 : ℝ)^J)))*(h/H))) ≤ (3*D+21)*Real.log m := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Real.log (1000000 : ℝ) ≤ 20*Real.log 2 := by
    have hn : (1000000 : ℝ) ≤ (2 : ℝ)^20 := by norm_num
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1000000) hn
    rw [Real.log_pow] at hl
    norm_num at hl ⊢
    exact hl
  have hp : 1 ≤ (2 : ℝ)^J := one_le_pow₀ (by norm_num)
  have hsum : 1+(2 : ℝ)^J ≤ (2 : ℝ)^(J+1) := by rw [pow_succ]; linarith
  have hb := Real.log_le_log (by positivity : (0 : ℝ) < 1+(2 : ℝ)^J) hsum
  rw [Real.log_pow] at hb
  have hj : (J : ℝ)*Real.log 2 ≤ (L : ℝ)*Real.log 2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) h2.le
  have hlogh := Real.log_le_log hs hhlo
  have hlogH : Real.log H ≤ 0 := Real.log_nonpos hH.le hHhi
  have hslog : Real.log (1/s) = -Real.log s := by rw [one_div,Real.log_inv]
  rw [hslog] at hscale
  have he : Real.log (1/((h/(1000000*(1+(2 : ℝ)^J)))*(h/H))) =
      Real.log (1000000 : ℝ)+Real.log (1+(2 : ℝ)^J)+Real.log H-2*Real.log h := by
    rw [one_div,Real.log_inv,Real.log_mul (by positivity) (by positivity),
      Real.log_div hh.ne' (by positivity),Real.log_div hh.ne' hH.ne',
      Real.log_mul (by norm_num) (by positivity)]
    ring
  rw [he]
  push_cast at hb
  nlinarith

theorem family_uniform_interpolation_degree {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024)) (hL : 0 < out.depth)
    (hm : Real.log 2 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m)
    (j : ℕ) (hj : j < out.depth) :
    let H := familyScheduleValue (1/1024) (s/1024) j
    let h := familyScheduleValue (1/1024) (s/1024) (j+1)
    let η := 8*(h/H)
    let τ := h/(1000000*(1+(2 : ℝ)^(j+1)))
    ∃ (hη : 0 < η) (hη1 : η ≤ 1/8) (hτ : 0 < τ) (hτ1 : τ < 1/4),
      (2^inverseRootLevel η τ hη hτ : ℝ) ≤
        17000*(3*D+21)*(H/h)*Real.log m := by
  let H := familyScheduleValue (1/1024) (s/1024) j
  let h := familyScheduleValue (1/1024) (s/1024) (j+1)
  let η := 8*(h/H)
  let τ := h/(1000000*(1+(2 : ℝ)^(j+1)))
  have hH : 0 < H := familyScheduleValue_pos _ _ (by norm_num) (by positivity) j
  have hh : 0 < h := familyScheduleValue_pos _ _ (by norm_num) (by positivity) (j+1)
  have hbH := out.level_bounds hs hL j (by omega)
  have hbh := out.level_bounds hs hL (j+1) (by omega)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/8 := by
    change 8*(h/H) ≤ (1/8 : ℝ)
    have ha' : h/H ≤ (1/1024 : ℝ) := by
      apply (div_le_iff₀ hH).mpr
      have hx := out.ratios j hj
      change h ≤ H/1024 at hx
      nlinarith
    linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ < 1/4 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 1000000*(1+(2 : ℝ)^(j+1)))).mpr
    have hp : 1 ≤ (2 : ℝ)^(j+1) := one_le_pow₀ (by norm_num)
    change h < _
    linarith [hbh.2]
  refine ⟨hη,hη1,hτ,hτ1,?_⟩
  have hu := inverseRootLevel_degree_bound_simple η τ hη hη1 hτ hτ1
  have hl := family_interpolation_log_budget s h H m D (j+1) out.depth hs hh hH
    hbh.1 (by linarith [hbH.2]) (by omega) hm hscale
    (familySchedule_depth_log_linear hs out hL hscale)
  have hl' : Real.log (1/(τ*η)) ≤ (3*D+21)*Real.log m := by
    apply le_trans (Real.log_le_log (by positivity) ?_) hl
    apply one_div_le_one_div_of_le (by positivity : 0 < τ*(h/H))
    dsimp only [η]
    nlinarith [div_pos hh hH]
  calc
    _ ≤ (17000/η)*Real.log (1/(τ*η)) := hu
    _ ≤ (17000/η)*((3*D+21)*Real.log m) :=
      mul_le_mul_of_nonneg_left hl' (by positivity)
    _ ≤ (17000*(H/h))*((3*D+21)*Real.log m) := by
      have hdepth := familySchedule_depth_log_linear hs out hL hscale
      have hDlm : 0 ≤ D*Real.log m :=
        (by positivity : (0 : ℝ) ≤ (out.depth : ℝ)*Real.log 2).trans hdepth
      have hlm : 0 < Real.log m := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hm
      have hpos : 0 ≤ (3*D+21)*Real.log m := by nlinarith
      apply mul_le_mul_of_nonneg_right _ hpos
      change 17000/(8*(h/H)) ≤ 17000*(H/h)
      apply (div_le_iff₀ hη).mpr
      have he : (17000*(H/h))*(8*(h/H)) = 136000 := by
        field_simp [hh.ne',hH.ne']
        <;> ring
      rw [he]
      norm_num
    _ = _ := by ring

end
end HierarchicalAbsoluteSpectral
