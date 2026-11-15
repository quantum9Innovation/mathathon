import HierarchicalAbsoluteSpectral.CorollaryOptimizedKernelFamily
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalAsymptotics

/-! Absorb the comparator's actual polynomial logarithms and fixed core
slack.  The verified Gram circuit and ordinary-action exponents then both
convert to the exact output exponent 2+s*. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter
open scoped Topology

theorem optimized_output_ratio_power (m N η : ℝ) (hm : 0 < m) (hN : 0 < N)
    (hside : N ≤ m^(1+dStar+η)) :
    N^2*(N/m)^(1/4:ℝ) ≤ m^(2+9*dStar/4+9*η/4) := by
  have hh := Real.log_le_log hN hside
  rw [Real.log_rpow hm] at hh
  apply (Real.log_le_log_iff (by positivity : 0 < N^2*(N/m)^(1/4:ℝ))
    (Real.rpow_pos_of_pos hm _)).mp
  rw [Real.log_mul (pow_pos hN _).ne' (Real.rpow_pos_of_pos (div_pos hN hm) _).ne',
    Real.log_pow,Real.log_rpow (div_pos hN hm),Real.log_div hN.ne' hm.ne',Real.log_rpow hm]
  norm_num
  nlinarith

def optimizedComparatorAnalyticEnvelope (m N X CMain CCore ζ : ℝ) : ℝ :=
  CMain*X*N^2*(N/m)^(1/4:ℝ)*(Real.log m)^12+CCore*m^(9/4+ζ)*(Real.log m)^2

theorem optimized_comparator_analytic_exponent (m N : ℕ → ℕ) (X : ℕ → ℝ)
    (hm : Tendsto m atTop atTop) (hNm : ∀ i, m i ≤ N i)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ))
      atTop (𝓝 (1+dStar)))
    (hX : ∀ i, 1 ≤ X i)
    (hXsub : ∀ η : ℝ, 0 < η → ∀ᶠ i : ℕ in atTop, X i ≤ (m i:ℝ)^η)
    (CMain CCore ζ : ℝ) (hMain : 0 ≤ CMain) (hCore : 0 ≤ CCore)
    (hζ : 9/4+ζ < 2+9*dStar/4) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop,
      optimizedComparatorAnalyticEnvelope (m i) (N i) (X i) CMain CCore ζ ≤
        (N i:ℝ)^(2+savingStar+ε) := by
  let E : ℝ := 2+9*dStar/4
  have hκ : 0 < 1+dStar := by linarith [optimized_parameter_in_family.1]
  have hE : 0 ≤ E := by dsimp [E]; linarith [optimized_parameter_in_family.1]
  have hmR : Tendsto (fun i => (m i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hN0 : ∀ᶠ i : ℕ in atTop, (0:ℝ) < N i := by
    filter_upwards [hm.eventually (eventually_ge_atTop (1:ℕ))] with i hi
    exact_mod_cast hi.trans (hNm i)
  have hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i : ℕ in atTop,
      optimizedComparatorAnalyticEnvelope (m i) (N i) (X i) CMain CCore ζ ≤ (m i:ℝ)^(E+η) := by
    intro η hη
    let δ : ℝ := η/20
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hdim := family_sequence_dimension_powers atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
      dStar δ hδ hmR hN0 hgrowth
    have hlogs := hmR.eventually (family_core_polylog_absorbed CMain 12 δ 0 hMain hδ)
    have hcore := hmR.eventually (family_core_polylog_absorbed CCore 2 E (9/4+ζ) hCore hζ)
    have hlarge := ((tendsto_rpow_atTop (show 0 < η/2 by positivity)).comp hmR).eventually
      (eventually_ge_atTop (2:ℝ))
    filter_upwards [hdim,hXsub δ hδ,hlogs,hcore,hlarge,hN0,
      hm.eventually (eventually_ge_atTop (1:ℕ))] with i hNi hXi hLi hCi hlargei hNpos hmi
    have hm0 : (0:ℝ) < m i := by exact_mod_cast hmi
    have hm1 : (1:ℝ) ≤ m i := by exact_mod_cast hmi
    have hgeom := optimized_output_ratio_power (m i) (N i) δ hm0 hNpos hNi.2
    have hLi' : CMain*(Real.log (m i:ℝ))^12 ≤ (m i:ℝ)^δ := by
      simpa only [Real.rpow_zero,mul_one,Real.rpow_ofNat] using hLi
    have hCi' : CCore*(m i:ℝ)^(9/4+ζ)*(Real.log (m i:ℝ))^2 ≤ (m i:ℝ)^E := by
      simpa only [Real.rpow_ofNat] using hCi
    have hX0 : 0 ≤ X i := by linarith [hX i]
    have hgeom0 : 0 ≤ (N i:ℝ)^2*(N i/m i:ℝ)^(1/4:ℝ) := by positivity
    have hinput := mul_le_mul hXi hgeom hgeom0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hprod := mul_le_mul hLi' hinput (mul_nonneg hX0 hgeom0)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hlead : CMain*X i*(N i:ℝ)^2*(N i/m i:ℝ)^(1/4:ℝ)*(Real.log (m i:ℝ))^12 ≤
        (m i:ℝ)^(E+η/2) := by
      calc
        _ = (CMain*(Real.log (m i:ℝ))^12)*(X i*((N i:ℝ)^2*(N i/m i:ℝ)^(1/4:ℝ))) := by ring
        _ ≤ (m i:ℝ)^δ*((m i:ℝ)^δ*(m i:ℝ)^(2+9*dStar/4+9*δ/4)) := hprod
        _ = (m i:ℝ)^(E+17*δ/4) := by
          rw [← mul_assoc,← Real.rpow_add hm0,← Real.rpow_add hm0]
          congr 1
          dsimp [E]
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm1 (by dsimp [δ]; linarith)
    have hcore' := hCi'.trans (Real.rpow_le_rpow_of_exponent_le hm1 (show E ≤ E+η/2 by linarith))
    unfold optimizedComparatorAnalyticEnvelope
    calc
      _ ≤ (m i:ℝ)^(E+η/2)+(m i:ℝ)^(E+η/2) := add_le_add hlead hcore'
      _ = 2*(m i:ℝ)^(E+η/2) := by ring
      _ ≤ (m i:ℝ)^(η/2)*(m i:ℝ)^(E+η/2) :=
        mul_le_mul_of_nonneg_right hlargei (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by rw [← Real.rpow_add hm0]; congr 1; ring
  have hh := sequence_cost_exponent_in_output atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    (fun i => optimizedComparatorAnalyticEnvelope (m i) (N i) (X i) CMain CCore ζ)
    (1+dStar) E hκ hE hmR hN0 hgrowth hcost
  simpa only [E,optimized_total_comparison.1] using hh

theorem optimized_comparator_full_envelope_exponent (m N : ℕ → ℕ) (X G : ℕ → ℝ)
    (hm : Tendsto m atTop atTop) (hNm : ∀ i, m i ≤ N i)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ))
      atTop (𝓝 (1+dStar)))
    (hX : ∀ i, 1 ≤ X i)
    (hXsub : ∀ η : ℝ, 0 < η → ∀ᶠ i : ℕ in atTop, X i ≤ (m i:ℝ)^η)
    (hG : ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop, G i ≤ (N i:ℝ)^(2+savingStar+ε))
    (CMain CCore ζ : ℝ) (hMain : 0 ≤ CMain) (hCore : 0 ≤ CCore)
    (hζ : 9/4+ζ < 2+9*dStar/4) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop,
      2*G i+optimizedComparatorAnalyticEnvelope (m i) (N i) (X i) CMain CCore ζ ≤
        (N i:ℝ)^(2+savingStar+ε) := by
  have hNNat : Tendsto N atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hm.eventually (eventually_ge_atTop b)] with i hi
    exact hi.trans (hNm i)
  have hNR : Tendsto (fun i => (N i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hNNat
  intro ε hε
  have hlarge := ((tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp hNR).eventually
    (eventually_ge_atTop (3:ℝ))
  filter_upwards [optimized_comparator_analytic_exponent m N X hm hNm hgrowth hX hXsub
    CMain CCore ζ hMain hCore hζ (ε/2) (by positivity),hG (ε/2) (by positivity),hlarge,
    hNNat.eventually (eventually_ge_atTop (1:ℕ))] with i hi hGi hlargei hNi
  have hN0 : (0:ℝ) < N i := by exact_mod_cast hNi
  calc
    _ ≤ 2*(N i:ℝ)^(2+savingStar+ε/2)+(N i:ℝ)^(2+savingStar+ε/2) := by nlinarith
    _ = 3*(N i:ℝ)^(2+savingStar+ε/2) := by ring
    _ ≤ (N i:ℝ)^(ε/2)*(N i:ℝ)^(2+savingStar+ε/2) :=
      mul_le_mul_of_nonneg_right hlargei (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring

end
end HierarchicalAbsoluteSpectral
