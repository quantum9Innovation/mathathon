import HierarchicalAbsoluteSpectral.CorollaryOptimizedKernels
import HierarchicalAbsoluteSpectral.RuntimeFamilyOptimization

/-! Logarithmic dimension, accuracy and rank statements for the optimized
integer-dimensional family, and conversion of the actual Gram circuit cost
to powers of the explicit output dimension. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Matmul.RectangularPrograms Matmul.RectangularOptimization
open scoped Topology

theorem optimized_reciprocal_parameters :
    (1+dStar)⁻¹=alphaStar ∧ alphaStar⁻¹=1+dStar := by
  have hd : 0 < 1+dStar := by linarith [optimized_parameter_in_family.1]
  have ha : 0 < alphaStar := optimized_total_comparison.2.2.2.2.1
  have he := optimized_parameters.2.1
  constructor
  · simpa only [one_div] using ((eq_div_iff hd.ne').mpr he).symm
  · have he' : (1+dStar)*alphaStar=1 := by simpa only [mul_comm] using he
    simpa only [one_div] using ((eq_div_iff ha.ne').mpr he').symm

theorem optimized_dimension_growth_iff {ι : Type*} (l : Filter ι) (m N : ι → ℝ) :
    Tendsto (fun i => Real.log (m i)/Real.log (N i)) l (𝓝 alphaStar) ↔
      Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (1+dStar)) := by
  have hd : 0 < 1+dStar := by linarith [optimized_parameter_in_family.1]
  have ha : 0 < alphaStar := optimized_total_comparison.2.2.2.2.1
  constructor
  · intro h
    simpa only [inv_div,optimized_reciprocal_parameters.2] using h.inv₀ ha.ne'
  · intro h
    simpa only [inv_div,optimized_reciprocal_parameters.1] using h.inv₀ hd.ne'

theorem optimized_theta_log (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    Real.log ((m/N)^2*Real.sqrt (m/N)) = (5/2 : ℝ)*(Real.log m-Real.log N) := by
  rw [Real.log_mul (pow_ne_zero _ (div_pos hm hN).ne')
      (Real.sqrt_pos.mpr (div_pos hm hN)).ne',
    Real.log_pow,Real.log_sqrt (div_pos hm hN).le,Real.log_div hm.ne' hN.ne']
  ring

theorem optimized_accuracy_exponent {ι : Type*} (l : Filter ι) (m N : ι → ℝ)
    (hm : Tendsto m l atTop) (hNm : ∀ᶠ i in l, m i ≤ N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (1+dStar))) :
    Tendsto (fun i => Real.log ((m i/N i)^2*Real.sqrt (m i/N i))/Real.log (N i))
      l (𝓝 (-10*savingStar)) := by
  have hrecip := (optimized_dimension_growth_iff l m N).mpr hgrowth
  have hlim := (hrecip.sub_const 1).const_mul (5/2 : ℝ)
  have he : (5/2 : ℝ)*(alphaStar-1) = -10*savingStar := by
    linarith [optimized_parameters.2.2.1]
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [hm.eventually (eventually_gt_atTop (1:ℝ)),hNm] with i hmi hNi
  have hm0 : 0 < m i := by linarith
  have hN1 : 1 < N i := hmi.trans_le hNi
  have hN0 : 0 < N i := by linarith
  have hlogN : Real.log (N i) ≠ 0 := (Real.log_pos hN1).ne'
  rw [optimized_theta_log (m i) (N i) hm0 hN0]
  field_simp
  <;> ring

theorem optimized_sqrt_rank_exponent {ι : Type*} (l : Filter ι) (m N : ι → ℝ)
    (hm : ∀ᶠ i in l, 0 ≤ m i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 (1+dStar))) :
    Tendsto (fun i => Real.log (Real.sqrt (m i))/Real.log (N i)) l (𝓝 (alphaStar/2)) := by
  have hrecip := (optimized_dimension_growth_iff l m N).mpr hgrowth
  have hlim := hrecip.div_const 2
  apply hlim.congr'
  filter_upwards [hm] with i hmi
  rw [Real.log_sqrt hmi]
  ring

/-- This helper converts a proved circuit or program envelope; its cost
hypothesis is never used as an original-input algorithm assumption. -/
theorem sequence_cost_exponent_in_output {ι : Type*} (l : Filter ι)
    (m N cost : ι → ℝ) (κ E : ℝ) (hκ : 0 < κ) (hE : 0 ≤ E)
    (hm : Tendsto m l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i)/Real.log (m i)) l (𝓝 κ))
    (hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, cost i ≤ (m i)^(E+η)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, cost i ≤ (N i)^(E/κ+ε) := by
  intro ε hε
  let η : ℝ := κ*ε/2
  let B : ℝ := E/κ+ε
  have hη : 0 < η := by dsimp [η]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hcut : (E+η)/B < κ := by
    apply (div_lt_iff₀ hB).mpr
    have he : κ*B=E+κ*ε := by dsimp [B]; field_simp
    rw [he]
    dsimp [η]
    nlinarith [mul_pos hκ hε]
  have hlower := hgrowth.eventually (eventually_gt_nhds hcut)
  filter_upwards [hcost η hη,hlower,hN,hm.eventually (eventually_gt_atTop (1:ℝ))]
    with i hci hratio hNi hmi
  have hm0 : 0 < m i := by linarith
  have hlog : 0 < Real.log (m i) := Real.log_pos hmi
  have hlogs := (lt_div_iff₀ hlog).mp hratio
  have hlogs' := mul_le_mul_of_nonneg_right hlogs.le hB.le
  have hcancel : ((E+η)/B*Real.log (m i))*B = Real.log (m i)*(E+η) := by
    field_simp
    <;> ring
  rw [hcancel] at hlogs'
  exact hci.trans (by
    rw [Real.rpow_def_of_pos hm0,Real.rpow_def_of_pos hNi]
    exact Real.exp_le_exp.mpr hlogs')

theorem optimized_integer_rank_range (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hN : ∀ᶠ i : ℕ in atTop, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ))
      atTop (𝓝 (1+dStar))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop,
      ∀ r : ℕ, r ≤ ⌊Real.sqrt (m i:ℝ)⌋₊ → (r:ℝ) ≤ (N i:ℝ)^(alphaStar/2+ε) := by
  have hκ : 0 < 1+dStar := by linarith [optimized_parameter_in_family.1]
  have hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i : ℕ in atTop,
      Real.sqrt (m i:ℝ) ≤ (m i:ℝ)^((1/2:ℝ)+η) := by
    intro η hη
    filter_upwards [hm.eventually (eventually_ge_atTop (1:ℕ))] with i hi
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hi)
    linarith
  have hh := sequence_cost_exponent_in_output atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    (fun i => Real.sqrt (m i:ℝ)) (1+dStar) (1/2) hκ (by norm_num)
    (tendsto_natCast_atTop_atTop.comp hm)
    (hN.mono (fun i hi => by exact_mod_cast hi)) hgrowth hcost
  have he : (1/2:ℝ)/(1+dStar) = alphaStar/2 := by
    rw [div_eq_mul_inv,optimized_reciprocal_parameters.1]
    ring
  rw [he] at hh
  intro ε hε
  filter_upwards [hh ε hε] with i hi
  intro r hr
  have hr' : (r:ℝ) ≤ Real.sqrt (m i:ℝ) :=
    (by exact_mod_cast hr : (r:ℝ) ≤ ⌊Real.sqrt (m i:ℝ)⌋₊).trans
      (Nat.floor_le (Real.sqrt_nonneg _))
  exact hr'.trans hi

theorem optimized_gram_rectangular_exponent :
    rectangularBound (1+dStar)/(1+dStar) = 2+savingStar := by
  have hd : (1/2:ℝ) < 1+dStar := by linarith [optimized_parameter_in_family.1]
  have he : rectangularBound (1+dStar) = 2+dStar+1/(4*(1+dStar)) := by
    simp only [rectangularBound,if_neg (not_le.mpr hd)]
    ring
  rw [he]
  exact optimized_total_comparison.2.1

/-- Both quoted comparator exponents agree in the original m scale. -/
theorem optimized_comparator_core_exponents :
    2+9*dStar/4 = rectangularBound (1+dStar) ∧
      2+9*dStar/4 = (1+dStar)*(2+savingStar) ∧
      9/4 < 2+9*dStar/4 := by
  have hd : 0 < 1+dStar := by linarith [optimized_parameter_in_family.1]
  have hk := (div_eq_iff hd.ne').mp optimized_total_comparison.1
  have hg := (div_eq_iff hd.ne').mp optimized_gram_rectangular_exponent
  refine ⟨by linarith,by linarith,?_⟩
  linarith [optimized_parameter_in_family.1]

/-- A literal true-Gram circuit family with the optimized 2+s* exponent.
The program witnesses are fixed before the asymptotic slack is quantified. -/
theorem exists_optimized_gram_arithmetic_family :
    ∃ P : ∀ j n : ℕ, ArithmeticKernel n (width (1+dStar+1/(j+1:ℝ)) n) n,
      ∀ (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop)
        (hN : ∀ᶠ i : ℕ in atTop, 0 < N i)
        (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ))
          atTop (𝓝 (1+dStar)))
        (fallback : ℕ → ∀ a b c : ℕ, ArithmeticKernel a b c)
        (ε : ℝ) (hε : 0 < ε),
      ∀ᶠ i : ℕ in atTop,
        ((comparatorGramKernelFamily (1+dStar) P (fallback i) (m i) (m i) (N i) (m i)).cost:ℝ) ≤
          (N i:ℝ)^(2+savingStar+ε) := by
  have hκ : 0 < 1+dStar := by linarith [optimized_parameter_in_family.1]
  obtain ⟨P,hP⟩ := exists_comparator_gram_kernel_family (1+dStar) hκ.le
  refine ⟨P,?_⟩
  intro m N hm hN hgrowth fallback ε hε
  have hE : 0 ≤ rectangularBound (1+dStar) :=
    le_trans (by norm_num) (two_le_rectangularBound hκ.le)
  have hh := sequence_cost_exponent_in_output atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    (fun i => ((comparatorGramKernelFamily (1+dStar) P (fallback i) (m i) (m i) (N i) (m i)).cost:ℝ))
    (1+dStar) (rectangularBound (1+dStar)) hκ hE
    (tendsto_natCast_atTop_atTop.comp hm)
    (hN.mono (fun i hi => by exact_mod_cast hi)) hgrowth
    (hP m N hm hN hgrowth fallback) ε hε
  simpa only [optimized_gram_rectangular_exponent] using hh

end
end HierarchicalAbsoluteSpectral
