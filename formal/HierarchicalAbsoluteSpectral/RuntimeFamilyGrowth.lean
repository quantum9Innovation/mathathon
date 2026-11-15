import HierarchicalAbsoluteSpectral.RuntimeFamilyTopBound

/-! Give N=m^(1+d+o(1)) its explicit logarithmic meaning and discharge
the small exponent slack needed by the coarse/output cost comparison. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter Asymptotics Set
open scoped Topology

def FamilyDimensionGrowth (N : ℝ → ℝ) (d : ℝ) : Prop :=
  (∀ᶠ m in atTop, 0 < N m) ∧
    Tendsto (fun m : ℝ => Real.log (N m)/Real.log m) atTop (𝓝 (1+d))

theorem family_dimension_growth_powers (N : ℝ → ℝ) (d ε : ℝ)
    (hgrowth : FamilyDimensionGrowth N d) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, m^(1+d-ε) ≤ N m ∧ N m ≤ m^(1+d+ε) := by
  have hb := hgrowth.2.eventually
    (Ioo_mem_nhds (show 1+d-ε < 1+d by linarith) (show 1+d < 1+d+ε by linarith))
  filter_upwards [hb,hgrowth.1,eventually_gt_atTop (1 : ℝ)] with m hm hN hm1
  have hm0 : 0 < m := by linarith
  have hlog : 0 < Real.log m := Real.log_pos hm1
  constructor
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hm0 _) hN).mp
    rw [Real.log_rpow hm0]
    have hh := (lt_div_iff₀ hlog).mp hm.1
    linarith
  · apply (Real.log_le_log_iff hN (Real.rpow_pos_of_pos hm0 _)).mp
    rw [Real.log_rpow hm0]
    have hh := (div_lt_iff₀ hlog).mp hm.2
    linarith

theorem family_dimension_growth_scale (N : ℝ → ℝ) (d : ℝ)
    (hd : 0 < d) (hgrowth : FamilyDimensionGrowth N d) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ m : ℝ in atTop,
      (d/4)*Real.log m ≤ Real.log (1/Real.sqrt (m/N m)) ∧
      Real.log (1/Real.sqrt (m/N m)) ≤ D*Real.log m := by
  let D : ℝ := max 1 (d+1)
  refine ⟨D,le_max_left _ _,?_⟩
  filter_upwards [family_dimension_growth_powers N d (d/2) hgrowth (by positivity),
    family_dimension_growth_powers N d 1 hgrowth (by norm_num),hgrowth.1,
    eventually_gt_atTop (1 : ℝ)] with m hlo hhi hN hm1
  have hl := (family_ratio_log_bounds m (N m) (d/2) (d+1) hm1 hN
    (by convert hlo.1 using 1 <;> congr 1 <;> ring)
    (by convert hhi.2 using 1 <;> congr 1 <;> ring))
  have hm0 : 0 ≤ Real.log m := (Real.log_pos hm1).le
  refine ⟨by nlinarith [hl.1],?_⟩
  apply hl.2.trans
  have hD : d+1 ≤ D := le_max_right _ _
  have hD1 : 1 ≤ D := le_max_left _ _
  nlinarith [mul_nonneg (show 0 ≤ D-(d+1)/2 by linarith) hm0]

theorem family_top_cost_of_dimension_growth (N χ cost : ℝ → ℝ) (d ζ K γ Ccore : ℝ)
    (hd : (1/8 : ℝ) < d) (hζ : ζ < 2+2*d-9/4) (hcore : 0 ≤ Ccore)
    (hgrowth : FamilyDimensionGrowth N d)
    (hχ0 : ∀ᶠ m in atTop, 0 ≤ χ m)
    (hχ : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, χ m ≤ m^ε)
    (hcost : ∀ᶠ m in atTop, cost m ≤
      (N m)^2*χ m*Real.exp (K*(1+Real.log (Real.log (2*m)))^2)+
        Ccore*m^(9/4+ζ)*(Real.log m)^γ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, cost m ≤ (N m)^(2+ε) := by
  let η : ℝ := min ((d-1/8)/2) ((2+2*d-9/4-ζ)/4)
  have hη : 0 < η := by apply lt_min <;> linarith
  have hη1 : η ≤ (d-1/8)/2 := min_le_left _ _
  have hη2 : η ≤ (2+2*d-9/4-ζ)/4 := min_le_right _ _
  have hd0 : 1/8 < d-η := by linarith
  have hζ0 : ζ < 2+2*(d-η)-9/4 := by linarith
  have hN : ∀ᶠ m : ℝ in atTop, m^(1+(d-η)) ≤ N m := by
    filter_upwards [family_dimension_growth_powers N d η hgrowth hη] with m hm
    convert hm.1 using 1 <;> congr 1 <;> ring
  exact family_top_cost_in_output N χ cost (d-η) ζ K γ Ccore hd0 hζ0 hcore hN
    (hgrowth.1.mono (fun _ hm => hm.le)) hχ0 hχ hcost

end
end HierarchicalAbsoluteSpectral
