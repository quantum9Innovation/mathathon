import HierarchicalAbsoluteSpectral.RuntimeFamilyGrowth

/-! The final asymptotic quantification works over any diverging sequence of
dimensions, including natural dimensions. N=m^(1+d+o(1)) means convergence
of the displayed logarithmic ratio; no real-dimension extension is assumed. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter Asymptotics Set
open scoped Topology

theorem family_sequence_dimension_powers {ι : Type*} (l : Filter ι)
    (m N : ι → ℝ) (d ε : ℝ) (hε : 0 < ε) (hm : Tendsto m l atTop)
    (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (1+d))) :
    ∀ᶠ i in l, (m i)^(1+d-ε) ≤ N i ∧ N i ≤ (m i)^(1+d+ε) := by
  have hb := hgrowth.eventually
    (Ioo_mem_nhds (show 1+d-ε < 1+d by linarith) (show 1+d < 1+d+ε by linarith))
  filter_upwards [hb,hN,hm.eventually (eventually_gt_atTop (1 : ℝ))] with i hi hNi hmi
  have hm0 : 0 < m i := by linarith
  have hlog : 0 < Real.log (m i) := Real.log_pos hmi
  constructor
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hm0 _) hNi).mp
    rw [Real.log_rpow hm0]
    have hh := (lt_div_iff₀ hlog).mp hi.1
    linarith
  · apply (Real.log_le_log_iff hNi (Real.rpow_pos_of_pos hm0 _)).mp
    rw [Real.log_rpow hm0]
    have hh := (div_lt_iff₀ hlog).mp hi.2
    linarith

theorem family_sequence_top_cost {ι : Type*} (l : Filter ι)
    (m N χ cost : ι → ℝ) (d ζ K γ Ccore : ℝ)
    (hm : Tendsto m l atTop) (hd : (1/8 : ℝ) < d)
    (hζ : ζ < 2+2*d-9/4) (hcore : 0 ≤ Ccore)
    (hN0 : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (1+d)))
    (hχ0 : ∀ᶠ i in l, 0 ≤ χ i)
    (hχ : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, χ i ≤ (m i)^ε)
    (hcost : ∀ᶠ i in l, cost i ≤
      (N i)^2*χ i*Real.exp (K*(1+Real.log (Real.log (2*m i)))^2)+
        Ccore*(m i)^(9/4+ζ)*(Real.log (m i))^γ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, cost i ≤ (N i)^(2+ε) := by
  let η : ℝ := min ((d-1/8)/2) ((2+2*d-9/4-ζ)/4)
  have hη : 0 < η := by apply lt_min <;> linarith
  have hη1 : η ≤ (d-1/8)/2 := min_le_left _ _
  have hη2 : η ≤ (2+2*d-9/4-ζ)/4 := min_le_right _ _
  have hd0 : 1/8 < d-η := by linarith
  have hζ0 : 9/4+ζ < 2+2*(d-η) := by linarith
  have hN := family_sequence_dimension_powers l m N d η hη hm hN0 hgrowth
  intro ε hε
  have ht := tendsto_rpow_atTop (show 0 < ε/4 by positivity)
  filter_upwards [hcost,hχ (ε/4) (by positivity),hχ0,hN,hN0,
    hm.eventually (family_exp_loglog_two_mul_eventually_le_rpow K (ε/4) (by positivity)),
    hm.eventually (family_core_polylog_absorbed Ccore γ (2+2*(d-η)) (9/4+ζ) hcore hζ0),
    (ht.comp hm).eventually (eventually_ge_atTop (2 : ℝ)),
    hm.eventually (eventually_ge_atTop (1 : ℝ))]
    with i hc hkernel hk0 hNi hNpos hover hcorei hlarge hmi
  change 2 ≤ (m i)^(ε/4) at hlarge
  have hm0 : 0 < m i := by linarith
  have hlow : (m i)^(1+(d-η)) ≤ N i := by convert hNi.1 using 1 <;> congr 1 <;> ring
  have hmN : m i ≤ N i := by
    apply le_trans _ hlow
    calc
      m i = (m i)^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hmi (by linarith)
  have hcoreN : Ccore*(m i)^(9/4+ζ)*(Real.log (m i))^γ ≤ (N i)^2 := by
    apply hcorei.trans
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg hm0.le (1+(d-η))) hlow 2
    have he : (m i)^(2+2*(d-η)) = ((m i)^(1+(d-η)))^2 := by
      rw [← Real.rpow_two,← Real.rpow_mul hm0.le]
      congr 1
      ring
    rwa [← he] at hp
  have hmain : (N i)^2*χ i*Real.exp (K*(1+Real.log (Real.log (2*m i)))^2) ≤
      (N i)^2*(m i)^(ε/2) := by
    calc
      _ ≤ ((N i)^2*(m i)^(ε/4))*(m i)^(ε/4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hkernel (sq_nonneg _)) hover
          (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [mul_assoc,← Real.rpow_add hm0]; congr 2 <;> ring
  have hlarge2 : 2 ≤ (m i)^(ε/2) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlarge 2
    have he : (m i)^(ε/2) = ((m i)^(ε/4))^2 := by
      rw [← Real.rpow_two,← Real.rpow_mul hm0.le]
      congr 1
      ring
    rw [he]
    nlinarith
  have hsquare : (m i)^(ε/2)+1 ≤ (m i)^ε := by
    have he : (m i)^ε = ((m i)^(ε/2))^2 := by
      rw [← Real.rpow_two,← Real.rpow_mul hm0.le]
      congr 1
      ring
    rw [he]
    nlinarith
  calc
    _ ≤ (N i)^2*χ i*Real.exp (K*(1+Real.log (Real.log (2*m i)))^2)+
      Ccore*(m i)^(9/4+ζ)*(Real.log (m i))^γ := hc
    _ ≤ (N i)^2*(m i)^(ε/2)+(N i)^2 := add_le_add hmain hcoreN
    _ = (N i)^2*((m i)^(ε/2)+1) := by ring
    _ ≤ (N i)^2*(m i)^ε := mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
    _ ≤ (N i)^2*(N i)^ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm0.le hmN hε.le) (sq_nonneg _)
    _ = _ := by rw [← Real.rpow_two,← Real.rpow_add hNpos]

end
end HierarchicalAbsoluteSpectral
