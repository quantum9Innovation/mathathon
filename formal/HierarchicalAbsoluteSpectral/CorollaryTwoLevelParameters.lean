import HierarchicalAbsoluteSpectral.CorollaryTwoLevelScalar
import HierarchicalAbsoluteSpectral.RuntimeFamilyDimensions

/-! The rounded two-level schedule satisfies all finite fixed-depth input
conditions for sufficiently large integer dimensions. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter
open ArithmeticProgram hiding pure

def twoLevelH0 (m : ℝ) : ℝ := twoLevelRoundedPower m 7 100
def twoLevelH1 (m : ℝ) : ℝ := twoLevelRoundedPower m 1 12
def twoLevelTheta (m : ℝ) : ℝ := twoLevelRoundedPower m 11 25
def twoLevelAccuracy (m : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then twoLevelH0 m else twoLevelH1 m

structure TwoLevelScalarParameters (m : ℝ) where
  h0 : ℝ
  h1 : ℝ
  theta : ℝ
  h0_eq : h0 = twoLevelH0 m
  h1_eq : h1 = twoLevelH1 m
  theta_eq : theta = twoLevelTheta m

def twoLevelCanonicalParameters (m : ℝ) : TwoLevelScalarParameters m :=
  ⟨twoLevelH0 m,twoLevelH1 m,twoLevelTheta m,rfl,rfl,rfl⟩

theorem TwoLevelScalarParameters.eq_canonical {m : ℝ} (out : TwoLevelScalarParameters m) :
    out = twoLevelCanonicalParameters m := by
  rcases out with ⟨h0,h1,theta,h0eq,h1eq,hteq⟩
  subst h0
  subst h1
  subst theta
  rfl

def twoLevelParametersProgram (m : ℝ) : ArithmeticProgram (TwoLevelScalarParameters m) := do
  let h0 ← (twoLevelRoundedPowerProgram m 7 100).certify
  let h1 ← (twoLevelRoundedPowerProgram m 1 12).certify
  let theta ← (twoLevelRoundedPowerProgram m 11 25).certify
  .pure
    { h0 := h0.val, h1 := h1.val, theta := theta.val
      h0_eq := h0.property.trans (twoLevelRoundedPowerProgram_eval m 7 100)
      h1_eq := h1.property.trans (twoLevelRoundedPowerProgram_eval m 1 12)
      theta_eq := theta.property.trans (twoLevelRoundedPowerProgram_eval m 11 25) }

theorem twoLevelParametersProgram_admissible (m : ℝ) :
    (twoLevelParametersProgram m).admissible := by simp [twoLevelParametersProgram]

theorem twoLevelParametersProgram_work (m : ℝ) :
    (twoLevelParametersProgram m).work =
      (twoLevelRoundedPowerProgram m 7 100).work+
        (twoLevelRoundedPowerProgram m 1 12).work+
        (twoLevelRoundedPowerProgram m 11 25).work := by
  simp [twoLevelParametersProgram,Nat.add_assoc]

theorem twoLevelParametersProgram_work_log (m : ℝ) (hm : 1 ≤ m) :
    ((twoLevelParametersProgram m).work : ℝ) ≤ 34+57*Real.log m/Real.log 2 := by
  rw [twoLevelParametersProgram_work]
  push_cast
  have h0 := twoLevelRoundedPowerProgram_work_log m 7 100 hm
  have h1 := twoLevelRoundedPowerProgram_work_log m 1 12 hm
  have ht := twoLevelRoundedPowerProgram_work_log m 11 25 hm
  norm_num only [Nat.cast_ofNat] at h0 h1 ht
  calc
    _ ≤ (12+21*Real.log m/Real.log 2)+(6+3*Real.log m/Real.log 2)+
        (16+33*Real.log m/Real.log 2) := add_le_add (add_le_add h0 h1) ht
    _ = _ := by ring

theorem twoLevelParameters_positive (m : ℝ) :
    0 < twoLevelH0 m ∧ 0 < twoLevelH1 m ∧ 0 < twoLevelTheta m :=
  ⟨twoLevelRoundedPower_positive m 7 100,twoLevelRoundedPower_positive m 1 12,
    twoLevelRoundedPower_positive m 11 25⟩

theorem twoLevelParameters_bounds (m : ℝ) (hm : 1 ≤ m) :
    m^(-(7/100 : ℝ))/4 ≤ twoLevelH0 m ∧ twoLevelH0 m ≤ m^(-(7/100 : ℝ)) ∧
      m^(-(1/12 : ℝ))/4 ≤ twoLevelH1 m ∧ twoLevelH1 m ≤ m^(-(1/12 : ℝ)) ∧
      m^(-(11/25 : ℝ))/4 ≤ twoLevelTheta m ∧ twoLevelTheta m ≤ m^(-(11/25 : ℝ)) := by
  have h0 := twoLevelRoundedPower_bounds m 7 100 hm (by norm_num)
  have h1 := twoLevelRoundedPower_bounds m 1 12 hm (by norm_num)
  have ht := twoLevelRoundedPower_bounds m 11 25 hm (by norm_num)
  norm_num only [Nat.cast_ofNat,neg_div] at h0 h1 ht
  exact ⟨h0.1,h0.2,h1.1,h1.2,ht.1,ht.2⟩

theorem twoLevelParameters_ratios (m : ℝ) (hm : 1 ≤ m) :
    twoLevelH1 m/twoLevelH0 m ≤ 4*m^(-(1/75 : ℝ)) ∧
      twoLevelTheta m/twoLevelH1 m ≤ 4*m^(-(107/300 : ℝ)) ∧
      twoLevelH1 m/twoLevelTheta m ≤ 4*m^(107/300 : ℝ) := by
  have h0 := twoLevelRoundedPower_ratio_le m 1 12 7 100 hm (by norm_num) (by norm_num)
  have h1 := twoLevelRoundedPower_ratio_le m 11 25 1 12 hm (by norm_num) (by norm_num)
  have h2 := twoLevelRoundedPower_ratio_le m 1 12 11 25 hm (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at h0 h1 h2
  exact ⟨h0,h1,h2⟩

theorem twoLevel_rounded_rank_width (m r : ℕ) (hm : 1 ≤ m)
    (hr : r ≤ ⌈(m : ℝ)^(14/25 : ℝ)⌉₊) :
    (r+1 : ℝ) ≤ 3*(m : ℝ)^(14/25 : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 1 ≤ (m : ℝ)^(14/25 : ℝ) := Real.one_le_rpow hmR (by norm_num)
  have hceil : (⌈(m:ℝ)^(14/25:ℝ)⌉₊:ℝ) ≤ 2*(m:ℝ)^(14/25:ℝ) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (m:ℝ)^(14/25:ℝ) by positivity)
    linarith
  have hrR : (r:ℝ) ≤ (⌈(m:ℝ)^(14/25:ℝ)⌉₊:ℝ) := by exact_mod_cast hr
  linarith

theorem twoLevel_schedule_eventually :
    ∀ᶠ m : ℝ in atTop,
      1 ≤ m ∧ twoLevelH0 m ≤ 1/64 ∧
        twoLevelTheta m ≤ twoLevelH1 m ∧ twoLevelH1 m/twoLevelH0 m ≤ 1/1024 := by
  have h0 := (tendsto_rpow_neg_atTop (show (0:ℝ) < 7/100 by norm_num)).eventually
    (eventually_le_nhds (show (0:ℝ) < 1/64 by norm_num))
  have h1 := (tendsto_rpow_neg_atTop (show (0:ℝ) < 1/75 by norm_num)).eventually
    (eventually_le_nhds (show (0:ℝ) < 1/4096 by norm_num))
  have ht := (tendsto_rpow_neg_atTop (show (0:ℝ) < 107/300 by norm_num)).eventually
    (eventually_le_nhds (show (0:ℝ) < 1/4 by norm_num))
  filter_upwards [eventually_ge_atTop (1:ℝ),h0,h1,ht] with m hm h0 h1 ht
  have hb := twoLevelParameters_bounds m hm
  have hr := twoLevelParameters_ratios m hm
  exact ⟨hm,hb.2.1.trans h0,
    (div_le_one (twoLevelParameters_positive m).2.1).mp (hr.2.1.trans (by linarith)),
    hr.1.trans (by linarith)⟩

theorem twoLevel_rank_cap_eventually :
    ∀ᶠ m : ℝ in atTop, 2*m^(14/25:ℝ) < m :=
  family_const_mul_rpow_lt_linear 2 (14/25) (by norm_num)

theorem twoLevel_schedule_nat_eventually :
    ∀ᶠ m : ℕ in atTop,
      1 ≤ m ∧ twoLevelH0 m ≤ 1/64 ∧ twoLevelTheta m ≤ twoLevelH1 m ∧
        twoLevelH1 m/twoLevelH0 m ≤ 1/1024 ∧ ⌈(m:ℝ)^(14/25:ℝ)⌉₊ ≤ m := by
  have hs := tendsto_natCast_atTop_atTop.eventually twoLevel_schedule_eventually
  have hr := tendsto_natCast_atTop_atTop.eventually twoLevel_rank_cap_eventually
  filter_upwards [hs,hr] with m hs hr
  have hm : 1 ≤ m := by exact_mod_cast hs.1
  have hmR : (1:ℝ) ≤ m := hs.1
  have hp : 1 ≤ (m:ℝ)^(14/25:ℝ) := Real.one_le_rpow hmR (by norm_num)
  have hc : (⌈(m:ℝ)^(14/25:ℝ)⌉₊:ℝ) ≤ 2*(m:ℝ)^(14/25:ℝ) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (m:ℝ)^(14/25:ℝ) by positivity)
    linarith
  refine ⟨hm,hs.2.1,hs.2.2.1,hs.2.2.2,?_⟩
  exact_mod_cast hc.trans hr.le

/-- A fixed finite cutoff from the proved eventual schedule conditions.
It is used only in the mathematical domain of the asymptotic corollary. -/
def twoLevelMinimumCore : ℕ :=
  (eventually_atTop.mp twoLevel_schedule_nat_eventually).choose

theorem twoLevelMinimumCore_spec (m : ℕ) (hm : twoLevelMinimumCore ≤ m) :
    1 ≤ m ∧ twoLevelH0 m ≤ 1/64 ∧ twoLevelTheta m ≤ twoLevelH1 m ∧
      twoLevelH1 m/twoLevelH0 m ≤ 1/1024 ∧ ⌈(m:ℝ)^(14/25:ℝ)⌉₊ ≤ m :=
  (eventually_atTop.mp twoLevel_schedule_nat_eventually).choose_spec m hm

end
end HierarchicalAbsoluteSpectral
