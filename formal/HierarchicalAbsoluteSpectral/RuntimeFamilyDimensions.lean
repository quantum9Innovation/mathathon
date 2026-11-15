import HierarchicalAbsoluteSpectral.RuntimeFamilyLogBudgets
import HierarchicalAbsoluteSpectral.RuntimeFamilyRecurrence

/-! Quantified dimensional consequences of the family assumptions: the
square-root schedule scale, rounded rank widths, raw-width safety and
absorption of the coarse algebra term. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter Asymptotics

theorem family_ratio_log (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    Real.log (1/Real.sqrt (m/N)) = (Real.log N-Real.log m)/2 := by
  rw [one_div,Real.log_inv,Real.log_sqrt (div_pos hm hN).le,
    Real.log_div hm.ne' hN.ne']
  ring

theorem family_ratio_log_bounds (m N d D : ℝ) (hm : 1 < m) (hN : 0 < N)
    (hlo : m^(1+d) ≤ N) (hhi : N ≤ m^(1+D)) :
    (d/2)*Real.log m ≤ Real.log (1/Real.sqrt (m/N)) ∧
      Real.log (1/Real.sqrt (m/N)) ≤ (D/2)*Real.log m := by
  have hm0 : 0 < m := by linarith
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hm0 _) hlo
  have hh := Real.log_le_log hN hhi
  rw [Real.log_rpow hm0] at hl hh
  rw [family_ratio_log m N hm0 hN]
  constructor <;> nlinarith

theorem family_theta_square_root (m N : ℝ) (hm : 0 ≤ m) (hN : 0 < N) :
    (Real.sqrt (m/N))^5 = (m/N)^2*Real.sqrt (m/N) := by
  have hs := Real.sq_sqrt (div_nonneg hm hN.le)
  calc
    _ = ((Real.sqrt (m/N))^2)^2*Real.sqrt (m/N) := by ring
    _ = _ := by rw [hs]

theorem family_rounded_rank_width (m r : ℕ) (hm : 1 ≤ m) (hr : r ≤ ⌊Real.sqrt (m : ℝ)⌋₊) :
    (r+1 : ℝ) ≤ 2*Real.sqrt (m : ℝ) ∧
      r+1 ≤ 2*⌈Real.sqrt (m : ℝ)⌉₊ := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 ≤ Real.sqrt (m : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hrR : (r : ℝ) ≤ Real.sqrt (m : ℝ) := by
    exact (by exact_mod_cast hr : (r : ℝ) ≤ ⌊Real.sqrt (m : ℝ)⌋₊).trans
      (Nat.floor_le (Real.sqrt_nonneg _))
  have hfirst : (r+1 : ℝ) ≤ 2*Real.sqrt (m : ℝ) := by nlinarith
  refine ⟨hfirst,?_⟩
  have hceil := Nat.le_ceil (Real.sqrt (m : ℝ))
  exact_mod_cast (hfirst.trans (mul_le_mul_of_nonneg_left hceil (by norm_num)))

theorem family_const_mul_rpow_lt_linear (C a : ℝ) (ha : a < 1) :
    ∀ᶠ m : ℝ in atTop, C*m^a < m := by
  have ht := tendsto_rpow_atTop (sub_pos.mpr ha)
  filter_upwards [ht.eventually (eventually_gt_atTop C),eventually_gt_atTop (0 : ℝ)] with m hm hm0
  calc
    _ < m^(1-a)*m^a := mul_lt_mul_of_pos_right hm (Real.rpow_pos_of_pos hm0 _)
    _ = _ := by rw [← Real.rpow_add hm0]; norm_num

theorem family_raw_width_eventually (q r : ℝ → ℕ) (d : ℝ) (hd : 0 < d) (hd1 : d < 1/2)
    (hq : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, (q m : ℝ) ≤ m^(d+ε))
    (hr : ∀ᶠ m in atTop, (r m : ℝ) ≤ Real.sqrt m) :
    ∀ᶠ m : ℝ in atTop, ((2*q m+1)*(r m+1) : ℝ) < m := by
  let ε : ℝ := (1/2-d)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ha : 1/2+d+ε < 1 := by dsimp [ε]; linarith
  filter_upwards [hq ε hε,hr,family_const_mul_rpow_lt_linear 6 (1/2+d+ε) ha,
    eventually_ge_atTop (1 : ℝ)] with m hqm hrm hcap hm
  have hm0 : 0 < m := by linarith
  have hX : 1 ≤ m^(d+ε) := Real.one_le_rpow hm (by linarith)
  have hY : 1 ≤ Real.sqrt m := (Real.le_sqrt (by norm_num) hm0.le).mpr (by linarith)
  have hfirst : (2*(q m : ℝ)+1) ≤ 3*m^(d+ε) := by linarith
  have hsecond : (r m : ℝ)+1 ≤ 2*Real.sqrt m := by linarith
  have hprod := mul_le_mul hfirst hsecond (by positivity : 0 ≤ (r m : ℝ)+1) (by positivity)
  have he : (3*m^(d+ε))*(2*Real.sqrt m) = 6*m^(1/2+d+ε) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = 6*(m^(d+ε)*m^(1/2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hm0]; congr 2 <;> ring
  rw [he] at hprod
  exact hprod.trans_lt hcap

theorem family_polylog_eventually_le_rpow (γ ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, (Real.log m)^γ ≤ m^ε := by
  have hb := (isLittleO_log_rpow_rpow_atTop γ hε).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb,eventually_ge_atTop (1 : ℝ)] with m hm hm1
  have hm0 : 0 ≤ m := by linarith
  simpa only [Real.norm_eq_abs,one_mul,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hm1) γ),
    abs_of_nonneg (Real.rpow_nonneg hm0 ε)] using hm

theorem family_core_polylog_absorbed (C γ a b : ℝ) (hC : 0 ≤ C) (hab : b < a) :
    ∀ᶠ m : ℝ in atTop, C*m^b*(Real.log m)^γ ≤ m^a := by
  let ε : ℝ := (a-b)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ht := tendsto_rpow_atTop hε
  filter_upwards [family_polylog_eventually_le_rpow γ ε hε,
    ht.eventually (eventually_ge_atTop C),eventually_ge_atTop (1 : ℝ)] with m hp hc hm1
  have hm0 : 0 < m := by linarith
  calc
    _ ≤ (m^ε*m^b)*m^ε :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hm0.le _)) hp
        (Real.rpow_nonneg (Real.log_nonneg hm1) γ) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hm0,← Real.rpow_add hm0]
      congr 1
      dsimp [ε]
      ring

end
end HierarchicalAbsoluteSpectral
