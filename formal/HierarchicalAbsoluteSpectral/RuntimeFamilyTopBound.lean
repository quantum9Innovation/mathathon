import HierarchicalAbsoluteSpectral.RuntimeFamilyDimensions
import HierarchicalAbsoluteSpectral.RuntimeFamilyOverhead
import HierarchicalAbsoluteSpectral.RuntimeFamilyCorollaries

/-! Quantified asymptotic assembly of the manuscript's unfolded family
bound, including the fixed positive coarse/output margin. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter Asymptotics

theorem family_top_cost_in_m (N χ cost : ℝ → ℝ) (d ζ K γ Ccore : ℝ)
    (hd : (1/8 : ℝ) < d) (hζ : ζ < 2+2*d-9/4) (hcore : 0 ≤ Ccore)
    (hN : ∀ᶠ m in atTop, m^(1+d) ≤ N m)
    (hN0 : ∀ᶠ m in atTop, 0 ≤ N m)
    (hχ0 : ∀ᶠ m in atTop, 0 ≤ χ m)
    (hχ : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, χ m ≤ m^ε)
    (hcost : ∀ᶠ m in atTop, cost m ≤
      (N m)^2*χ m*Real.exp (K*(1+Real.log (Real.log (2*m)))^2)+
        Ccore*m^(9/4+ζ)*(Real.log m)^γ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, cost m ≤ (N m)^2*m^ε := by
  intro ε hε
  have hmain := family_unfolded_cost_eventually χ N
    (fun m => (N m)^2*χ m*Real.exp (K*(1+Real.log (Real.log (2*m)))^2)) K hχ
      (Filter.Eventually.of_forall (fun _ => le_rfl)) hχ0
  have hpow := tendsto_rpow_atTop (show 0 < ε/2 by positivity)
  filter_upwards [hcost,hmain (ε/2) (by positivity),hN,hN0,
    family_core_polylog_absorbed Ccore γ (2+2*d) (9/4+ζ) hcore (by linarith),
    hpow.eventually (eventually_ge_atTop (2 : ℝ)),eventually_gt_atTop (0 : ℝ)]
    with m hc hmainm hNm hNpos hcorem hsmall hm0
  have hcoreN : Ccore*m^(9/4+ζ)*(Real.log m)^γ ≤ (N m)^2 := by
    apply hcorem.trans
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hm0.le (1+d)) hNm 2
    have he : m^(2+2*d) = (m^(1+d))^2 := by
      rw [← Real.rpow_two,← Real.rpow_mul hm0.le]
      congr 1
      ring
    rwa [← he] at hp
  have hsquare : m^(ε/2)+1 ≤ m^ε := by
    have he : m^ε = (m^(ε/2))^2 := by
      rw [← Real.rpow_two,← Real.rpow_mul hm0.le]
      congr 1
      ring
    rw [he]
    nlinarith
  calc
    _ ≤ (N m)^2*χ m*Real.exp (K*(1+Real.log (Real.log (2*m)))^2)+
      Ccore*m^(9/4+ζ)*(Real.log m)^γ := hc
    _ ≤ (N m)^2*m^(ε/2)+(N m)^2 := add_le_add hmainm hcoreN
    _ = (N m)^2*(m^(ε/2)+1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)

theorem family_top_cost_in_output (N χ cost : ℝ → ℝ) (d ζ K γ Ccore : ℝ)
    (hd : (1/8 : ℝ) < d) (hζ : ζ < 2+2*d-9/4) (hcore : 0 ≤ Ccore)
    (hN : ∀ᶠ m in atTop, m^(1+d) ≤ N m)
    (hN0 : ∀ᶠ m in atTop, 0 ≤ N m)
    (hχ0 : ∀ᶠ m in atTop, 0 ≤ χ m)
    (hχ : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, χ m ≤ m^ε)
    (hcost : ∀ᶠ m in atTop, cost m ≤
      (N m)^2*χ m*Real.exp (K*(1+Real.log (Real.log (2*m)))^2)+
        Ccore*m^(9/4+ζ)*(Real.log m)^γ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, cost m ≤ (N m)^(2+ε) := by
  intro ε hε
  have hb := family_top_cost_in_m N χ cost d ζ K γ Ccore hd hζ hcore hN hN0 hχ0 hχ hcost ε hε
  filter_upwards [hb,hN,hN0,eventually_ge_atTop (1 : ℝ)] with m hbound hNm hNpos hm1
  have hm0 : 0 < m := by linarith
  have hmN : m ≤ N m := by
    apply le_trans _ hNm
    calc
      m = m^(1 : ℝ) := (Real.rpow_one m).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hNpositive : 0 < N m := hm0.trans_le hmN
  calc
    _ ≤ (N m)^2*m^ε := hbound
    _ ≤ (N m)^2*(N m)^ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm0.le hmN hε.le) (sq_nonneg _)
    _ = _ := by rw [← Real.rpow_two,← Real.rpow_add hNpositive]

end
end HierarchicalAbsoluteSpectral
