import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeNumeric

/-! Uniform magnitude, outer-degree and raw-width consequences of the
original optimized dimension and polynomial-confidence assumptions. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology
variable {N m r : ℕ}

def comparatorFamilyMagnitudeCoefficient (c : ℝ) : ℝ :=
  comparatorMagnitudeCoefficient (5+2*|Real.log 1048576|) c

theorem comparator_family_magnitude_coefficient_ge_one (c : ℝ) (hc : 0 ≤ c) :
    1 ≤ comparatorFamilyMagnitudeCoefficient c :=
  comparator_magnitude_coefficient_ge_one _ c (by positivity) hc

theorem comparator_family_magnitude (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy)
    (htheta : I.theta=min (comparatorDimensionTheta m N) (1/1048576))
    (c : ℝ) (hm : 2 ≤ m) (hN : (N:ℝ) ≤ (m:ℝ)^3)
    (hdelta : (m:ℝ)^(-c) ≤ I.delta) :
    comparatorScalarMagnitude I ≤ comparatorFamilyMagnitudeCoefficient c*Real.log (m:ℝ) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N from (show 0 < m by omega).trans_le I.core_le_rows)
  have hlogm : (1/2:ℝ) ≤ Real.log (m:ℝ) := family_log_two_lower.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hm))
  have hlogN : Real.log (N:ℝ) ≤ 3*Real.log (m:ℝ) := by
    have hh := Real.log_le_log hN0 hN
    rw [Real.log_pow] at hh
    norm_num at hh
    exact hh
  have hlogTheta : Real.log (1/comparatorDimensionTheta m N) ≤ 5*Real.log (m:ℝ) := by
    rw [one_div,Real.log_inv]
    have hh := optimized_theta_log (m:ℝ) (N:ℝ) hm0 hN0
    change Real.log (comparatorDimensionTheta m N)=(5/2:ℝ)*(Real.log (m:ℝ)-Real.log (N:ℝ)) at hh
    rw [hh]
    linarith
  have hc : |Real.log (1048576:ℝ)| ≤ 2 * |Real.log (1048576:ℝ)| * Real.log (m:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlogm (abs_nonneg (Real.log (1048576:ℝ)))]
  have ht : Real.log (1/I.theta) ≤ (5+2*|Real.log (1048576:ℝ)|)*Real.log (m:ℝ) := by
    have hh := comparator_dimension_internal_accuracy_log I htheta
    linarith [le_abs_self (Real.log (1048576:ℝ))]
  have hd : Real.log (1/I.delta) ≤ c*Real.log (m:ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hm0 _) hdelta
    rw [Real.log_rpow hm0] at hh
    rw [one_div,Real.log_inv]
    linarith
  exact comparator_magnitude_log_bound I haccuracy _ c hm ht hd

theorem comparator_degree_exponent_uniform (m N : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (hNm : ∀ i, m i ≤ N i)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ))
      atTop (𝓝 (1+dStar))) (c : ℝ) (hc : 0 ≤ c) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop,
      ∀ (r : ℕ) (I : FixedProblem (N i) (m i) (N i) r 1),
        I.accuracy=comparatorAccuracy →
        I.theta=min (comparatorDimensionTheta (m i) (N i)) (1/1048576) →
        (m i:ℝ)^(-c) ≤ I.delta →
        (comparatorOuterDegreeCap I:ℝ)+1 ≤ (m i:ℝ)^(5*dStar/4+ε) := by
  intro ε hε
  let η : ℝ := ε/10
  let D : ℝ := comparatorFamilyMagnitudeCoefficient c
  let CQ : ℝ := comparatorQueryCoefficient D
  let b : ℝ := (dStar+η)*(5/4)
  have hD : 1 ≤ D := comparator_family_magnitude_coefficient_ge_one c hc
  have hCα := comparatorAlphaRootConstant_ge_one
  have hCQ : 0 ≤ CQ := by dsimp [CQ,comparatorQueryCoefficient]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hb : b < 5*dStar/4+ε := by dsimp [b,η]; linarith
  have hmR : Tendsto (fun i => (m i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hN0 : ∀ᶠ i : ℕ in atTop, (0:ℝ) < N i := by
    filter_upwards [hm.eventually (eventually_ge_atTop (1:ℕ))] with i hi
    exact_mod_cast hi.trans (hNm i)
  have hdim := family_sequence_dimension_powers atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    dStar η hη hmR hN0 hgrowth
  have hdim1 := family_sequence_dimension_powers atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    dStar 1 (by norm_num) hmR hN0 hgrowth
  have habs := hmR.eventually (family_core_polylog_absorbed CQ 5 (5*dStar/4+ε) b hCQ hb)
  filter_upwards [hdim,hdim1,habs,hm.eventually (eventually_ge_atTop (2:ℕ)),
    hmR.eventually (eventually_ge_atTop (Real.exp 1))] with i hNi hNi1 hAbs hmi hlarge
  have hm0 : (0:ℝ) < m i := by exact_mod_cast (show 0 < m i by omega)
  have hm1 : (1:ℝ) ≤ m i := by exact_mod_cast (show 1 ≤ m i by omega)
  have hlog : 1 ≤ Real.log (m i:ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hlarge
  have hN3 : (N i:ℝ) ≤ (m i:ℝ)^3 := by
    apply hNi1.2.trans
    have hd1 : dStar < 1 := by
      have hh := family_parameter_margins dStar optimized_parameter_in_family.1 optimized_parameter_in_family.2
      linarith [hh.2.1]
    have hh := Real.rpow_le_rpow_of_exponent_le hm1 (show 1+dStar+1 ≤ (3:ℝ) by linarith)
    simpa only [Real.rpow_ofNat] using hh
  have hratio : (N i/m i:ℝ) ≤ (m i:ℝ)^(dStar+η) := by
    calc
      _ ≤ (m i:ℝ)^(1+dStar+η)/(m i:ℝ) := div_le_div_of_nonneg_right hNi.2 hm0.le
      _ = _ := by
        rw [show 1+dStar+η=1+(dStar+η) by ring,Real.rpow_add hm0,Real.rpow_one]
        field_simp
  have hpower : (N i/m i:ℝ)^(5/4:ℝ) ≤ (m i:ℝ)^b := by
    apply (Real.rpow_le_rpow (by positivity) hratio (by norm_num : (0:ℝ) ≤ 5/4)).trans_eq
    rw [← Real.rpow_mul hm0.le]
  intro r I haccuracy htheta hdelta
  have hmag := comparator_family_magnitude I haccuracy htheta c hmi hN3 hdelta
  have hq := comparator_query_dimension_bound I haccuracy htheta D (Real.log (m i:ℝ))
    hD hlog rfl hmag
  have hRp : (0:ℝ) < (N i/m i:ℝ) := by
    exact div_pos (by exact_mod_cast (show 0 < N i from (show 0 < m i by omega).trans_le (hNm i))) hm0
  have he : (N i/m i:ℝ)^(1/4:ℝ)*(N i/m i:ℝ)=(N i/m i:ℝ)^(5/4:ℝ) := by
    rw [show (5/4:ℝ)=1/4+1 by norm_num,Real.rpow_add hRp,Real.rpow_one]
  have hq' : (comparatorOuterDegreeCap I:ℝ)+1 ≤ CQ*(N i/m i:ℝ)^(5/4:ℝ)*(Real.log (m i:ℝ))^5 := by
    apply hq.trans_eq
    dsimp [CQ]
    calc
      _ = comparatorQueryCoefficient D*((N i/m i:ℝ)^(1/4:ℝ)*(N i/m i:ℝ))*(Real.log (m i:ℝ))^5 := by ring
      _ = _ := by rw [he]
  have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hCQ)
    (show 0 ≤ (Real.log (m i:ℝ))^5 by positivity)
  have hAbs' : CQ*(m i:ℝ)^b*(Real.log (m i:ℝ))^5 ≤ (m i:ℝ)^(5*dStar/4+ε) := by
    convert hAbs using 1 <;> norm_num
  exact hq'.trans (hbound.trans hAbs')

theorem comparator_raw_width_uniform (m N : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (hNm : ∀ i, m i ≤ N i)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ))
      atTop (𝓝 (1+dStar))) (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ i : ℕ in atTop, ∀ (r : ℕ) (I : FixedProblem (N i) (m i) (N i) r 1),
      I.accuracy=comparatorAccuracy →
      I.theta=min (comparatorDimensionTheta (m i) (N i)) (1/1048576) →
      (m i:ℝ)^(-c) ≤ I.delta → r ≤ ⌊Real.sqrt (m i:ℝ)⌋₊ →
      (comparatorOuterDegreeCap I+1)*(r+1) ≤ m i := by
  let η : ℝ := (1/2-5*dStar/4)/2
  have hd := family_parameter_margins dStar optimized_parameter_in_family.1 optimized_parameter_in_family.2
  have hη : 0 < η := by dsimp [η]; linarith [hd.2.1]
  have ha : 5*dStar/4+η+1/2 < 1 := by dsimp [η]; linarith [hd.2.1]
  have hmR : Tendsto (fun i => (m i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  filter_upwards [comparator_degree_exponent_uniform m N hm hNm hgrowth c hc η hη,
    hmR.eventually (family_const_mul_rpow_lt_linear 2 (5*dStar/4+η+1/2) ha),
    hm.eventually (eventually_ge_atTop (1:ℕ))] with i hq hcap hmi
  intro r I haccuracy htheta hdelta hr
  have hq' := hq r I haccuracy htheta hdelta
  have hr' := (family_rounded_rank_width (m i) r hmi hr).1
  have hm0 : (0:ℝ) < m i := by exact_mod_cast hmi
  have hprod := mul_le_mul hq' hr' (by positivity : (0:ℝ) ≤ r+1)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have he : (m i:ℝ)^(5*dStar/4+η)*(2*Real.sqrt (m i:ℝ))=
      2*(m i:ℝ)^(5*dStar/4+η+1/2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = 2*((m i:ℝ)^(5*dStar/4+η)*(m i:ℝ)^(1/2:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hm0]
  rw [he] at hprod
  have hh : ((comparatorOuterDegreeCap I+1)*(r+1):ℝ) < m i := by
    push_cast
    exact hprod.trans_lt hcap
  exact_mod_cast hh.le

end
end HierarchicalAbsoluteSpectral
