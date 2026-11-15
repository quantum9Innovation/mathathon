import HierarchicalAbsoluteSpectral.CoarseAlgebraInputOptimalKernels
import HierarchicalAbsoluteSpectral.RuntimeFamilyDimensions

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.RectangularPrograms Matmul.RectangularOptimization Filter

theorem rectangular_width_le_self (κ : ℝ) (hκ : κ ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    width κ m ≤ m := by
  apply Nat.ceil_le.mpr
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hm : (1:ℝ) ≤ m) hκ

/-- A fixed amount of exponent slack accommodates every block width up
to m^κ for some κ strictly larger than one half. Both physical directions
have a gate count linear in the ambient dimension. -/
theorem exists_growing_input_optimal_arithmetic_kernels (η : ℝ) (hη : 0 < η) :
    ∃ (κ : ℝ) (K : ∀ m : ℕ, ArithmeticKernel m m (width κ m)) (C : ℝ),
      1/2 < κ ∧ κ ≤ 1 ∧ 0 < C ∧
      ∀ (N m b : ℕ) (hm : 0 < m) (hNm : m ≤ N) (hb : b ≤ width κ m),
        ((blockedForwardKernel K N m b hm hb).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η) ∧
        ((blockedAdjointKernel K N m b hm hb).cost:ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η) := by
  let δ := min (η/4) (1/4)
  let κ := 1/2+δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1/4 := min_le_right _ _
  have hδη : δ ≤ η/4 := min_le_left _ _
  have hκ0 : 0 ≤ κ := by dsimp [κ]; linarith
  have hκhalf : 1/2 < κ := by dsimp [κ]; linarith
  have hκ1 : κ ≤ 1 := by dsimp [κ]; linarith
  have he : rectangularBound κ+η/4-1 ≤ 1+η := by
    have hb := rectangularBound_le_add_delta (k := 1/2) (l := κ) (by norm_num) hκ0 hκhalf.le
    rw [rectangularBound_half] at hb
    dsimp [κ] at hb
    linarith
  obtain ⟨K,C,hC,hK⟩ := exists_input_optimal_arithmetic_kernels κ (η/4) hκ0 (by positivity)
  refine ⟨κ,K,2*(C+1),hκhalf,hκ1,by positivity,?_⟩
  intro N m b hm hNm hb
  have hs := hK N m b hm hNm hb
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm : (1:ℝ) ≤ m) he
  have hbs : (b:ℝ) ≤ (m:ℝ) := by
    exact_mod_cast hb.trans (rectangular_width_le_self κ hκ1 m hm)
  have hbm : (b:ℝ) ≤ (m:ℝ)^(1+η) := hbs.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hm : (1:ℝ) ≤ m) (show (1:ℝ) ≤ 1+η by linarith))
  have hfront : 2*C*(N:ℝ)*(m:ℝ)^(rectangularBound κ+η/4-1) ≤
      2*C*(N:ℝ)*(m:ℝ)^(1+η) := mul_le_mul_of_nonneg_left hpow (by positivity)
  have htail := mul_le_mul_of_nonneg_left hbm (show 0 ≤ 2*(N:ℝ) by positivity)
  have hnon : 0 ≤ (N:ℝ)*(m:ℝ)^(1+η) := by positivity
  constructor
  · exact hs.1.trans (hfront.trans (by nlinarith))
  · exact hs.2.trans (by nlinarith)

theorem polylog_width_eventually_fits (κ C γ : ℝ) (hκ : 1/2 < κ) (hC : 0 ≤ C)
    (b : ℕ → ℕ)
    (hb : ∀ᶠ m : ℕ in atTop, (b m:ℝ) ≤ C*Real.sqrt (m:ℝ)*(Real.log (m:ℝ))^γ) :
    ∀ᶠ m : ℕ in atTop, b m ≤ width κ m := by
  have hreal := family_core_polylog_absorbed C γ κ (1/2) hC hκ
  have hnat : ∀ᶠ m : ℕ in atTop,
      C*(m:ℝ)^(1/2:ℝ)*(Real.log (m:ℝ))^γ ≤ (m:ℝ)^κ :=
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop).eventually hreal
  filter_upwards [hb,hnat] with m hm hn
  have hc : (b m:ℝ) ≤ (m:ℝ)^κ := by
    rw [← Real.sqrt_eq_rpow] at hn
    exact hm.trans hn
  have hceil := Nat.le_ceil ((m:ℝ)^κ)
  exact_mod_cast hc.trans hceil

end
end HierarchicalAbsoluteSpectral
