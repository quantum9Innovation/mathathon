import HierarchicalAbsoluteSpectral.RuntimeFamilySequences

/-! Subpolynomial overheads at the two literal circuit sizes, and absorption
of the remaining polynomial logarithms into the unfolded depth factor. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Filter
open scoped Topology

theorem family_final_kernel_overhead_sequence {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (χ χOut : ℕ → ℝ) (d : ℝ) (hd : 0 < d)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hmN : ∀ i, m i ≤ N i) (hN : ∀ i, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d)))
    (hχ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, χ n ≤ (n:ℝ)^ε)
    (hχOut : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, χOut n ≤ (n:ℝ)^ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, max (χ (m i)) (χOut (N i)) ≤ (m i:ℝ)^ε := by
  have hmNat : Tendsto m l atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hm.eventually (eventually_ge_atTop (b:ℝ))] with i hi
    exact_mod_cast hi
  have hNNat : Tendsto N l atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hmNat.eventually (eventually_ge_atTop b)] with i hi
    exact hi.trans (hmN i)
  have hpow := family_sequence_dimension_powers l (fun i => (m i:ℝ)) (fun i => (N i:ℝ)) d 1
    (by norm_num) hm (Eventually.of_forall (fun i => by exact_mod_cast hN i)) hgrowth
  intro ε hε
  have hden : 0 < 2+d := by linarith
  have hε' : 0 < ε/(2+d) := div_pos hε hden
  filter_upwards [hmNat.eventually (hχ ε hε),hNNat.eventually (hχOut (ε/(2+d)) hε'),hpow]
    with i hi ho hp
  apply max_le hi
  apply ho.trans
  calc
    _ ≤ ((m i:ℝ)^(2+d))^(ε/(2+d)) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hε'.le
      convert hp.2 using 1 <;> congr 1 <;> ring
    _ = _ := by
      rw [← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      field_simp

theorem family_final_polylog_depth_absorb (m C R K : ℝ)
    (hm : 0 < m) (hmLog : 1 ≤ Real.log m) (hC : 1 ≤ C) (hR : 0 ≤ R) :
    C*(Real.log m)^R*Real.exp (K*(1+Real.log (Real.log (2*m)))^2) ≤
      Real.exp ((K+Real.log C+R)*(1+Real.log (Real.log (2*m)))^2) := by
  have hCp : 0 < C := by linarith
  have hlogp : 0 < Real.log m := by linarith
  have hlog : Real.log m ≤ Real.log (2*m) := Real.log_le_log hm (by linarith)
  have ht : 0 ≤ Real.log (Real.log (2*m)) := Real.log_nonneg (hmLog.trans hlog)
  have hCLog : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogs : Real.log (Real.log m) ≤ Real.log (Real.log (2*m)) :=
    Real.log_le_log hlogp hlog
  have hw : 1 ≤ (1+Real.log (Real.log (2*m)))^2 := by nlinarith
  have hv : Real.log (Real.log m) ≤ (1+Real.log (Real.log (2*m)))^2 := by
    nlinarith
  have h1 := mul_nonneg hCLog (sub_nonneg.mpr hw)
  have h2 := mul_nonneg hR (sub_nonneg.mpr hv)
  calc
    _ = Real.exp (Real.log C+Real.log (Real.log m)*R+
      K*(1+Real.log (Real.log (2*m)))^2) := by
      rw [Real.rpow_def_of_pos hlogp,Real.exp_add,Real.exp_add,Real.exp_log hCp]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end
end HierarchicalAbsoluteSpectral
