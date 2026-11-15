import HierarchicalAbsoluteSpectral.Schedule
import HierarchicalAbsoluteSpectral.ThresholdHalving

/-! Scalar facts for the manuscript's executable square-root schedule. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

def familyScheduleValue (h hstar : ℝ) : ℕ → ℝ
  | 0 => h
  | j+1 => Real.sqrt (familyScheduleValue h hstar j*hstar)

theorem familyScheduleValue_pos (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar) :
    ∀ j, 0 < familyScheduleValue h hstar j := by
  intro j
  induction j with
  | zero => exact hh
  | succ j ih => exact Real.sqrt_pos.mpr (mul_pos ih hs)

theorem familyScheduleValue_shift (h hstar : ℝ) (j : ℕ) :
    familyScheduleValue h hstar (j+1) = familyScheduleValue (Real.sqrt (h*hstar)) hstar j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change Real.sqrt (familyScheduleValue h hstar (j+1)*hstar) =
      Real.sqrt (familyScheduleValue (Real.sqrt (h*hstar)) hstar j*hstar)
    rw [ih]

theorem familySchedule_log_step (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar) :
    Real.log (Real.sqrt (h*hstar)/hstar) = Real.log (h/hstar)/2 := by
  rw [Real.log_div (Real.sqrt_pos.mpr (mul_pos hh hs)).ne' hs.ne',
    Real.log_sqrt (mul_pos hh hs).le,Real.log_mul hh.ne' hs.ne',Real.log_div hh.ne' hs.ne']
  ring

theorem familySchedule_log_value (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar) (j : ℕ) :
    Real.log (familyScheduleValue h hstar j/hstar) = Real.log (h/hstar)/(2 : ℝ)^j := by
  induction j with
  | zero => simp [familyScheduleValue]
  | succ j ih =>
    rw [familyScheduleValue,familySchedule_log_step _ _ (familyScheduleValue_pos h hstar hh hs j) hs,
      ih,pow_succ]
    ring

theorem familySchedule_accept_iff (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar) :
    Real.sqrt (h*hstar) ≤ h/1024 ↔ (1024 : ℝ)^2*hstar ≤ h := by
  constructor
  · intro ha
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ h/1024)).mpr ha
    rw [Real.sq_sqrt (mul_pos hh hs).le] at hsq
    have hp : 0 ≤ h*(h-(1024 : ℝ)^2*hstar) := by nlinarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hh).mp hp)
  · intro ha
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hp := mul_le_mul_of_nonneg_left ha hh.le
    nlinarith

theorem familySchedule_accept_log_iff (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar) :
    Real.sqrt (h*hstar) ≤ h/1024 ↔ 2*Real.log 1024 ≤ Real.log (h/hstar) := by
  rw [familySchedule_accept_iff h hstar hh hs]
  have hl : Real.log ((1024 : ℝ)^2) = 2*Real.log 1024 := by rw [Real.log_pow]; norm_num
  rw [← hl,Real.log_le_log_iff (by positivity) (div_pos hh hs),le_div_iff₀ hs]

def familyScheduleMeasure (h hstar : ℝ) : ℕ :=
  leastHalvings (Real.log (h/hstar)) (Real.log 1024) (Real.log_pos (by norm_num))

theorem familyScheduleMeasure_decreases (h hstar : ℝ) (hh : 0 < h) (hs : 0 < hstar)
    (ha : Real.sqrt (h*hstar) ≤ h/1024) :
    familyScheduleMeasure (Real.sqrt (h*hstar)) hstar < familyScheduleMeasure h hstar := by
  unfold familyScheduleMeasure
  rw [familySchedule_log_step h hstar hh hs]
  apply leastHalvings_half_lt
  have hl := (familySchedule_accept_log_iff h hstar hh hs).mp ha
  have hp : 0 < Real.log 1024 := Real.log_pos (by norm_num)
  linarith

theorem familySchedule_terminal_bounds (s h : ℝ) (hs : 0 < s) (hh : 0 < h)
    (hprev : ∃ H, 0 < H ∧ h = Real.sqrt (H*(s/1024)) ∧ h ≤ H/1024)
    (hstop : ¬Real.sqrt (h*(s/1024)) ≤ h/1024) :
    s ≤ h ∧ h < 1024*s := by
  obtain ⟨H,hH,he,ha⟩ := hprev
  have hs0 : 0 < s/1024 := by positivity
  have hacc := (familySchedule_accept_iff H (s/1024) hH hs0).mp (he ▸ ha)
  have hsq : h^2 = H*(s/1024) := by rw [he,Real.sq_sqrt (by positivity)]
  have hlo : s^2 ≤ h^2 := by nlinarith
  have hup := mt (familySchedule_accept_iff h (s/1024) hh hs0).mpr hstop
  constructor
  · nlinarith
  · have hu := lt_of_not_ge hup
    nlinarith

end
end HierarchicalAbsoluteSpectral
