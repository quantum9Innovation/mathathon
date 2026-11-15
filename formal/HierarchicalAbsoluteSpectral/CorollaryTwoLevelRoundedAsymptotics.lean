import HierarchicalAbsoluteSpectral.CorollaryTwoLevelParameters
import HierarchicalAbsoluteSpectral.RuntimeFamilyAsymptotics

/-! The executed dyadics have the manuscript's exact logarithmic power
exponents. A fixed positive confidence also meets the polynomial budget. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

theorem twoLevelRoundedPower_log_exponent (a b : ℕ) (hb : 1 ≤ b) :
    Tendsto (fun m:ℝ => Real.log (twoLevelRoundedPower m a b)/Real.log m) atTop
      (𝓝 (-(a:ℝ)/(b:ℝ))) := by
  let e : ℝ := -(a:ℝ)/(b:ℝ)
  have hz : Tendsto (fun m:ℝ => Real.log 4/Real.log m) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop (Real.log 4)
  have hbound : ∀ᶠ m:ℝ in atTop,
      0 ≤ e-Real.log (twoLevelRoundedPower m a b)/Real.log m ∧
      e-Real.log (twoLevelRoundedPower m a b)/Real.log m ≤ Real.log 4/Real.log m := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with m hm
    have hm0 : 0 < m := by linarith
    have hlog : 0 < Real.log m := Real.log_pos hm
    have hp := twoLevelRoundedPower_positive m a b
    have hi : 0 < m^(-(a:ℝ)/(b:ℝ)) := Real.rpow_pos_of_pos hm0 _
    have h := twoLevelRoundedPower_bounds m a b hm.le hb
    have hlo := Real.log_le_log (by positivity : 0 < m^(-(a:ℝ)/(b:ℝ))/4) h.1
    have hhi := Real.log_le_log hp h.2
    rw [Real.log_div hi.ne' (by norm_num),Real.log_rpow hm0] at hlo
    rw [Real.log_rpow hm0] at hhi
    change e*Real.log m-Real.log 4 ≤ Real.log (twoLevelRoundedPower m a b) at hlo
    change Real.log (twoLevelRoundedPower m a b) ≤ e*Real.log m at hhi
    have hdiv := (div_le_iff₀ hlog).mpr hhi
    constructor
    · linarith
    · apply (le_div_iff₀ hlog).mpr
      nlinarith only [hlo,div_mul_cancel₀ (Real.log (twoLevelRoundedPower m a b)) hlog.ne']
  have hf := squeeze_zero' (hbound.mono (fun _ h => h.1)) (hbound.mono (fun _ h => h.2)) hz
  have ht : Tendsto (fun m:ℝ => e-(e-Real.log (twoLevelRoundedPower m a b)/Real.log m))
      atTop (𝓝 (e-0)) :=
    (tendsto_const_nhds : Tendsto (fun _:ℝ => e) atTop (𝓝 e)).sub hf
  convert ht using 1
  · funext m
    dsimp [e]
    ring
  · simp only [sub_zero,e]

theorem twoLevel_parameter_log_exponents :
    Tendsto (fun m:ℝ => Real.log (twoLevelH0 m)/Real.log m) atTop (𝓝 (-(7/100:ℝ))) ∧
      Tendsto (fun m:ℝ => Real.log (twoLevelH1 m)/Real.log m) atTop (𝓝 (-(1/12:ℝ))) ∧
      Tendsto (fun m:ℝ => Real.log (twoLevelTheta m)/Real.log m) atTop (𝓝 (-(11/25:ℝ))) := by
  have h0 := twoLevelRoundedPower_log_exponent 7 100 (by norm_num)
  have h1 := twoLevelRoundedPower_log_exponent 1 12 (by norm_num)
  have ht := twoLevelRoundedPower_log_exponent 11 25 (by norm_num)
  norm_num only [Nat.cast_ofNat,neg_div] at h0 h1 ht
  exact ⟨h0,h1,ht⟩

theorem twoLevel_constant_confidence_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m:ℕ in atTop, (m:ℝ)^(-(1:ℝ)) ≤ δ := by
  have hm : Tendsto (fun m:ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact ((tendsto_rpow_neg_atTop (show (0:ℝ) < 1 by norm_num)).comp hm).eventually
    (eventually_le_nhds hδ)

theorem twoLevel_constant_confidence_family {ι : Type*} (l : Filter ι)
    (m : ι → ℕ) (hm : Tendsto m l atTop) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ i in l, (m i:ℝ)^(-(1:ℝ)) ≤ δ :=
  hm.eventually (twoLevel_constant_confidence_eventually δ hδ)

end
end HierarchicalAbsoluteSpectral
