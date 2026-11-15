import HierarchicalAbsoluteSpectral.CorollaryTwoLevelParameters
import HierarchicalAbsoluteSpectral.RuntimeFamilySequences

/-! Exact exponent arithmetic and quantified passage from powers of the
integer core dimension to powers of the ambient/output dimension. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

/-- The curved branch of the full three-dimension rectangular formula.
This is scalar arithmetic; actual circuit witnesses are supplied separately. -/
def twoLevelRectangularExponent (a b c : ℝ) : ℝ :=
  (a*b+b*c+c*a)^2/(4*a*b*c)

theorem twoLevel_rectangular_exponents :
    twoLevelRectangularExponent (57/50) 1 1 = 3362/1425 ∧
      twoLevelRectangularExponent (59/50) 1 (14/25) = 9006001/4130000 ∧
      twoLevelRectangularExponent (7/6) 1 (14/25) = 867/400 ∧
      (1:ℝ)*(57/50+1) > 57/50 ∧
      (14/25:ℝ)*(59/50+1) > (59/50)*1 ∧
      (14/25:ℝ)*(7/6+1) > (7/6)*1 := by
  norm_num [twoLevelRectangularExponent]

theorem twoLevel_action_exponents :
    ((11/25:ℝ)-(1/12))/2 = 107/600 ∧
      (1/12:ℝ)-(7/100) = 1/75 ∧
      (107/600:ℝ)+(14/25) = 443/600 ∧
      (9006001/4130000:ℝ)+(107/600) = 29227553/12390000 ∧
      (867/400:ℝ)+(107/600)+(1/75) = 2831/1200 ∧
      1+2*(7/100:ℝ) = 57/50 ∧ 1+2*(1/12:ℝ) = 7/6 := by norm_num

theorem twoLevel_all_exponent_margins :
    (29227553/12390000:ℝ) < 3362/1425 ∧
      (2831/1200:ℝ) < 3362/1425 ∧ (9/4:ℝ) < 3362/1425 ∧
      (1+59/50:ℝ) < 3362/1425 ∧ (3362/1425:ℝ) < 59/25 ∧
      (3362/1425:ℝ)-(2831/1200) = 1/7600 ∧
      (3362/1425:ℝ)-(29227553/12390000) = 78893/235410000 ∧
      (59/25:ℝ)-(3362/1425) = 1/1425 ∧
      (443/600:ℝ) < 1 ∧ (7/6:ℝ) < 59/50 ∧ (28/59:ℝ) < 1/2 := by norm_num

theorem twoLevel_output_exponent_identities :
    (3362/1425:ℝ)/(59/50) = 6724/3363 ∧
      (14/25:ℝ)/(59/50) = 28/59 ∧
      (59/25:ℝ)/(59/50) = 2 ∧
      (6724/3363:ℝ) = 2-2/3363 := by norm_num

/-- A generic analytic transfer lemma, with arbitrary diverging dimension
families. It does not assume any algorithm or success certificate. -/
theorem twoLevel_exponent_transfer {ι : Type*} (l : Filter ι)
    (m N cost : ι → ℝ) (E b : ℝ) (hb : 0 ≤ b) (hE : E = (59/50:ℝ)*b)
    (hm : Tendsto m l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (59/50:ℝ)))
    (hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, cost i ≤ (m i)^(E+η)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, cost i ≤ (N i)^(b+ε) := by
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
    with i hc hd hNi hmi
  have hlow : (m i)^((59/50:ℝ)-δ) ≤ N i := by convert hd.1 using 1 <;> norm_num
  have he : ((59/50:ℝ)-δ)*(b+ε) = E+η := by
    rw [hE]
    dsimp [δ,η]
    field_simp [hs.ne']
    <;> ring
  calc
    _ ≤ (m i)^(E+η) := hc
    _ = ((m i)^((59/50:ℝ)-δ))^(b+ε) := by rw [← Real.rpow_mul hmi.le,he]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hmi.le _) hlow hs.le

theorem twoLevel_construction_exponent_transfer {ι : Type*} (l : Filter ι)
    (m N cost : ι → ℝ) (hm : Tendsto m l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (59/50:ℝ)))
    (hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, cost i ≤ (m i)^((3362/1425:ℝ)+η)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, cost i ≤ (N i)^((6724/3363:ℝ)+ε) :=
  twoLevel_exponent_transfer l m N cost (3362/1425) (6724/3363) (by norm_num)
    (by norm_num) hm hN hgrowth hcost

theorem twoLevel_full_output_exponent_transfer {ι : Type*} (l : Filter ι)
    (m N cost : ι → ℝ) (hm : Tendsto m l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (59/50:ℝ)))
    (hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, cost i ≤ (m i)^((59/25:ℝ)+η)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, cost i ≤ (N i)^((2:ℝ)+ε) :=
  twoLevel_exponent_transfer l m N cost (59/25) 2 (by norm_num) (by norm_num)
    hm hN hgrowth hcost

theorem twoLevel_output_rank_eventually {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (hm : Tendsto m l atTop)
    (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ))) :
    ∀ᶠ i in l, ⌈(m i:ℝ)^(14/25:ℝ)⌉₊ ≤ ⌊Real.sqrt (N i:ℝ)⌋₊ := by
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hm
  have hNR : ∀ᶠ i in l, (0:ℝ) < N i := hN.mono (fun i hi => by exact_mod_cast hi)
  have hg : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+(9/50:ℝ))) := by
    convert hgrowth using 1 <;> norm_num
  have hd := family_sequence_dimension_powers l (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    (9/50) (1/100) (by norm_num) hmR hNR hg
  have hr := hmR.eventually (family_core_polylog_absorbed 2 0 (117/200) (14/25)
    (by norm_num) (by norm_num))
  filter_upwards [hd,hr,hNR,hmR.eventually (eventually_ge_atTop (1:ℝ))]
    with i hd hr hNi hmi
  have hm0 : (0:ℝ) < m i := by linarith
  have hpow : 1 ≤ (m i:ℝ)^(14/25:ℝ) := Real.one_le_rpow hmi (by norm_num)
  have hc : (⌈(m i:ℝ)^(14/25:ℝ)⌉₊:ℝ) ≤ 2*(m i:ℝ)^(14/25:ℝ) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (m i:ℝ)^(14/25:ℝ) by positivity)
    linarith
  have hbound : 2*(m i:ℝ)^(14/25:ℝ) ≤ (m i:ℝ)^(117/200:ℝ) := by
    simpa only [Real.rpow_zero,mul_one] using hr
  have hs : (m i:ℝ)^(117/200:ℝ) ≤ Real.sqrt (N i:ℝ) := by
    apply (Real.le_sqrt (by positivity) hNi.le).mpr
    rw [← Real.rpow_two,← Real.rpow_mul hm0.le]
    convert hd.1 using 1 <;> norm_num
  exact Nat.le_floor (hc.trans (hbound.trans hs))

end
end HierarchicalAbsoluteSpectral
