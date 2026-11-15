import HierarchicalAbsoluteSpectral.CorollaryTwoLevelExponents

/-! Uniform exponent transfer keeps the same size threshold for all
random outcomes, matrices, and supports at each dimension. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

theorem twoLevel_exponent_transfer_uniform {ι : Type*} {α : ι → Type*} (l : Filter ι)
    (m N : ι → ℝ) (cost : ∀ i, α i → ℝ) (E b : ℝ)
    (hb : 0 ≤ b) (hE : E=(59/50:ℝ)*b)
    (hm : Tendsto m l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (59/50:ℝ)))
    (hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, ∀ x : α i, cost i x ≤ (m i)^(E+η)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x : α i, cost i x ≤ (N i)^(b+ε) := by
  intro ε hε
  let η : ℝ := (59/50:ℝ)*(ε/2)
  let δ : ℝ := η/(b+ε)
  have hs : 0 < b+ε := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := div_pos hη hs
  have hg : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (1+(9/50:ℝ))) := by
    convert hgrowth using 1 <;> norm_num
  have hdim := family_sequence_dimension_powers l m N (9/50) δ hδ hm hN hg
  filter_upwards [hcost η hη,hdim,hN,hm.eventually (eventually_gt_atTop (0:ℝ))]
    with i hc hd hNi hmi x
  have hlow : (m i)^((59/50:ℝ)-δ) ≤ N i := by convert hd.1 using 1 <;> norm_num
  have he : ((59/50:ℝ)-δ)*(b+ε)=E+η := by
    rw [hE]
    dsimp [δ,η]
    field_simp [hs.ne']
    <;> ring
  calc
    _ ≤ (m i)^(E+η) := hc x
    _ = ((m i)^((59/50:ℝ)-δ))^(b+ε) := by rw [← Real.rpow_mul hmi.le,he]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hmi.le _) hlow hs.le

theorem twoLevel_input_dimensions_eventually {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (hm : Tendsto m l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ))) :
    ∀ᶠ i in l, twoLevelMinimumCore ≤ m i ∧ m i ≤ N i := by
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hm
  have hNR : ∀ᶠ i in l, (0:ℝ) < N i := hN.mono (fun i hi => by exact_mod_cast hi)
  have hg : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+(9/50:ℝ))) := by
    convert hgrowth using 1 <;> norm_num
  have hd := family_sequence_dimension_powers l (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    (9/50) (9/100) (by norm_num) hmR hNR hg
  filter_upwards [hd,hm.eventually (eventually_ge_atTop twoLevelMinimumCore),
    hmR.eventually (eventually_ge_atTop (1:ℝ))] with i hd hlarge hmi
  refine ⟨hlarge,?_⟩
  have hpow : (m i:ℝ) ≤ (m i:ℝ)^(1+(9/50:ℝ)-9/100) := by
    calc
      _ = (m i:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hmi (by norm_num)
  exact_mod_cast hpow.trans hd.1

end
end HierarchicalAbsoluteSpectral
