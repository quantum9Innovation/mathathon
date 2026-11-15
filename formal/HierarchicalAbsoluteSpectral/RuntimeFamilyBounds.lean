import HierarchicalAbsoluteSpectral.RuntimeFamilyScheduleProgram
import HierarchicalAbsoluteSpectral.ProbabilityEmbeddingSize

/-! Explicit uniform depth and multiplicative-overhead estimates. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter Asymptotics

theorem leastHalvings_log_bound (x ε : ℝ) (hε : 0 < ε) :
    (leastHalvings x ε hε : ℝ) ≤
      1+Real.log (max 1 (x/ε))/Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (max 1 (x/ε)) := Real.log_nonneg (le_max_left _ _)
  cases he : leastHalvings x ε hε with
  | zero =>
    simp only [Nat.cast_zero]
    have hh := div_nonneg hlog hlog2.le
    linarith
  | succ j =>
    have hm : ¬x/(2 : ℝ)^j ≤ ε := Nat.find_min (exists_halving_bound x ε hε) (by
      change j < leastHalvings x ε hε
      omega)
    have hp : (2 : ℝ)^j < x/ε := by
      apply (lt_div_iff₀ hε).mpr
      have hh := (lt_div_iff₀ (by positivity)).mp (lt_of_not_ge hm)
      nlinarith
    have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 2^j)
      (hp.trans_le (le_max_right (1 : ℝ) (x/ε)))
    rw [Real.log_pow] at hl
    have hj := (lt_div_iff₀ hlog2).mpr hl
    push_cast
    linarith

theorem familySchedule_depth_log_bound (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar) :
    ((familyScheduleProgram h hstar hh hs).eval.depth : ℝ) ≤
      1+Real.log (max 1 (Real.log (h/hstar)/Real.log 1024))/Real.log 2 := by
  calc
    _ ≤ (familyScheduleMeasure h hstar : ℝ) := by
      exact_mod_cast (familyScheduleProgram_checked h hstar hh hs).2.2
    _ ≤ _ := leastHalvings_log_bound _ _ _

theorem familySchedule_depth_loglog_bound (h hstar m D : ℝ)
    (hh : 0 < h) (hs : 0 < hstar) (hD : 1 ≤ D)
    (hm : 1 ≤ Real.log m) (hscale : Real.log (h/hstar) ≤ D*Real.log m) :
    ((familyScheduleProgram h hstar hh hs).eval.depth : ℝ) ≤
      1+(Real.log D+Real.log (Real.log m))/Real.log 2 := by
  have heps : 1 ≤ Real.log 1024 := by
    have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1023)
    norm_num at hh
    linarith
  have hDm : 1 ≤ D*Real.log m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hm)]
  have hratio : Real.log (h/hstar)/Real.log 1024 ≤ D*Real.log m := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 1024)).mpr
    nlinarith
  have hb := familySchedule_depth_log_bound h hstar hh hs
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < max 1
      (Real.log (h/hstar)/Real.log 1024)) (max_le hDm hratio)
  have hstep := div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hD0 : D ≠ 0 := by linarith
  have hm0 : Real.log m ≠ 0 := by linarith
  rw [Real.log_mul hD0 hm0] at hstep
  linarith

theorem family_overhead_exp_bound (C ell a : ℝ) (L : ℕ)
    (hC : 1 ≤ C) (hell : 1 ≤ ell) (ha : 0 ≤ a)
    (hL : (L : ℝ) ≤ a*(1+Real.log ell)) :
    (C*ell^2)^L ≤ Real.exp (a*(Real.log C+2)*(1+Real.log ell)^2) := by
  have hC0 : 0 < C := by linarith
  have he0 : 0 < ell := by linarith
  have hl : 0 ≤ Real.log ell := Real.log_nonneg hell
  have hc : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog : Real.log (C*ell^2) = Real.log C+2*Real.log ell := by
    rw [Real.log_mul hC0.ne' (pow_pos he0 _).ne',Real.log_pow]
    norm_num
  have hfactor : Real.log C+2*Real.log ell ≤ (Real.log C+2)*(1+Real.log ell) := by
    nlinarith
  have hh : (L : ℝ)*(Real.log C+2*Real.log ell) ≤
      a*(Real.log C+2)*(1+Real.log ell)^2 := by
    calc
      _ ≤ (a*(1+Real.log ell))*(Real.log C+2*Real.log ell) :=
        mul_le_mul_of_nonneg_right hL (by positivity)
      _ ≤ (a*(1+Real.log ell))*((Real.log C+2)*(1+Real.log ell)) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = _ := by ring
  calc
    _ = Real.exp (Real.log ((C*ell^2)^L)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := by rw [Real.log_pow,hlog]; exact Real.exp_le_exp.mpr hh

theorem family_accuracyScale_bound (L : ℕ) : accuracyScale L ≤ 39000000*(100 : ℝ)^L := by
  rw [accuracyScale,defectConstant_closed]
  have hp : 1 ≤ (100 : ℝ)^L := one_le_pow₀ (by norm_num)
  nlinarith

theorem family_accuracyScale_sqrt_bound (L : ℕ) : Real.sqrt (accuracyScale L) ≤ 7000*(10 : ℝ)^L := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  have he : ((10 : ℝ)^L)^2 = (100 : ℝ)^L := by
    rw [← pow_mul,Nat.mul_comm L 2,pow_mul]
    norm_num
  nlinarith [family_accuracyScale_bound L]

end
end HierarchicalAbsoluteSpectral
