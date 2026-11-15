import HierarchicalAbsoluteSpectral.BaseFixedPaperData
import HierarchicalAbsoluteSpectral.RuntimeFamilyBounds

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
variable {n m p r L : ℕ}

/-- The fixed-depth logarithmic gauge contains only original inputs. -/
def fixedPolylogGauge (I : FixedProblem n m p r L) : ℝ :=
  1+Real.log n+Real.log p+Real.log m+Real.log (1/I.theta)+Real.log (1/I.delta)+
    ∑ j : Fin (L+1), Real.log (1/I.accuracy j.val)

theorem fixedPolylog_accuracy_log_nonneg (I : FixedProblem n m p r L)
    (j : ℕ) (hj : j ≤ L) : 0 ≤ Real.log (1/I.accuracy j) := by
  have hp := I.accuracy_positive j hj
  have hb := I.accuracy_bounded j hj
  exact Real.log_nonneg ((le_div_iff₀ hp).mpr (by linarith))

theorem fixedPolylog_primitive_nonneg (I : FixedProblem n m p r L) :
    0 ≤ Real.log n ∧ 0 ≤ Real.log p ∧ 0 ≤ Real.log m ∧
      0 ≤ Real.log (1/I.theta) ∧ 0 ≤ Real.log (1/I.delta) ∧
        0 ≤ ∑ j : Fin (L+1), Real.log (1/I.accuracy j.val) := by
  have hm := I.rank_positive.trans I.rank_le_core
  have hn := hm.trans I.core_le_rows
  have hp := hm.trans I.core_le_cols
  refine ⟨Real.log_nonneg (by exact_mod_cast hn), Real.log_nonneg (by exact_mod_cast hp),
    Real.log_nonneg (by exact_mod_cast hm), ?_, ?_, ?_⟩
  · apply Real.log_nonneg
    apply (le_div_iff₀ I.theta_positive).mpr
    linarith [I.theta_le_last,I.accuracy_bounded L le_rfl]
  · exact Real.log_nonneg ((le_div_iff₀ I.delta_positive).mpr (by linarith [I.delta_lt_one]))
  · exact Finset.sum_nonneg (fun j _ => fixedPolylog_accuracy_log_nonneg I j.val (by omega))

theorem fixedPolylogGauge_ge_one (I : FixedProblem n m p r L) : 1 ≤ fixedPolylogGauge I := by
  have h := fixedPolylog_primitive_nonneg I
  unfold fixedPolylogGauge
  linarith [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]

theorem fixedPolylog_primitive_le (I : FixedProblem n m p r L) :
    Real.log n ≤ fixedPolylogGauge I ∧ Real.log p ≤ fixedPolylogGauge I ∧
      Real.log m ≤ fixedPolylogGauge I ∧ Real.log (1/I.theta) ≤ fixedPolylogGauge I ∧
        Real.log (1/I.delta) ≤ fixedPolylogGauge I ∧
          (∑ j : Fin (L+1), Real.log (1/I.accuracy j.val)) ≤ fixedPolylogGauge I := by
  have h := fixedPolylog_primitive_nonneg I
  unfold fixedPolylogGauge
  constructor
  · linarith [h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]
  constructor
  · linarith [h.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]
  constructor
  · linarith [h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]
  constructor
  · linarith [h.1,h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]
  constructor
  · linarith [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2]
  · linarith [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1]

theorem fixedPolylog_accuracy_log_le (I : FixedProblem n m p r L)
    (j : ℕ) (hj : j ≤ L) : Real.log (1/I.accuracy j) ≤ fixedPolylogGauge I := by
  have hh := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin (L+1))))
    (f := fun j : Fin (L+1) => Real.log (1/I.accuracy j.val))
    (fun j _ => fixedPolylog_accuracy_log_nonneg I j.val (by omega))
    (Finset.mem_univ (⟨j,by omega⟩ : Fin (L+1)))
  exact hh.trans (fixedPolylog_primitive_le I).2.2.2.2.2

theorem fixedPolylog_const_add {z x c d : ℝ} (hz : 1 ≤ z) (hc : 0 ≤ c)
    (hx : x ≤ d*z) : c+x ≤ (c+d)*z := by
  have hh := mul_le_mul_of_nonneg_left hz hc
  nlinarith only [hh,hx]

theorem fixedPolylog_halving_bound (x ε z c : ℝ) (hε : 0 < ε)
    (hz : 1 ≤ z) (hc : 0 ≤ c) (hx : Real.log (x/ε) ≤ c*z) :
    (leastHalvings x ε hε:ℝ) ≤ (1+c/Real.log 2)*z := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmax : Real.log (max 1 (x/ε)) ≤ c*z := by
    by_cases hh : x/ε ≤ 1
    · rw [max_eq_left hh,Real.log_one]
      exact mul_nonneg hc (by linarith)
    · rw [max_eq_right (le_of_not_ge hh)]
      exact hx
  have hh := leastHalvings_log_bound x ε hε
  have hd := div_le_div_of_nonneg_right hmax hl2.le
  calc
    _ ≤ 1+Real.log (max 1 (x/ε))/Real.log 2 := hh
    _ ≤ 1+c*z/Real.log 2 := by linarith only [hd]
    _ ≤ z+c*z/Real.log 2 := by linarith only [hz]
    _ = _ := by ring

theorem fixedPolylog_padding_bound (I : FixedProblem n m p r L) :
    (dyadicPaddingLevel n:ℝ) ≤ 3*fixedPolylogGauge I ∧
      (dyadicPaddingLevel p:ℝ) ≤ 3*fixedPolylogGauge I := by
  have hz := fixedPolylogGauge_ge_one I
  have hlog := fixedPolylog_primitive_le I
  have hl2 := family_log_two_lower
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 1+1/Real.log 2 ≤ 3 := by
    have hd : 1/Real.log 2 ≤ 2 := (div_le_iff₀ hl2p).mpr (by linarith)
    linarith
  constructor
  · have hh := fixedPolylog_halving_bound (n:ℝ) 1 (fixedPolylogGauge I) 1
      (by norm_num) hz (by norm_num) (by simpa using hlog.1)
    change (dyadicPaddingLevel n:ℝ) ≤ _ at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hc (by linarith))
  · have hh := fixedPolylog_halving_bound (p:ℝ) 1 (fixedPolylogGauge I) 1
      (by norm_num) hz (by norm_num) (by simpa using hlog.2.1)
    change (dyadicPaddingLevel p:ℝ) ≤ _ at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hc (by linarith))

theorem fixedPolylog_singleFailure_log (I : FixedProblem n m p r L) :
    Real.log (1/I.singleFailure) ≤ 20*fixedPolylogGauge I := by
  have hz := fixedPolylogGauge_ge_one I
  have hd := (fixedPolylog_primitive_le I).2.2.2.2.1
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<20)
  have he : Real.log (1/I.singleFailure) = Real.log 20+Real.log (1/I.delta) := by
    unfold FixedProblem.singleFailure
    rw [one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by norm_num),one_div,Real.log_inv]
    ring
  rw [he]
  linarith

theorem fixedPolylog_near_log (I : FixedProblem n m p r L) :
    Real.log (1/I.nearTolerance) ≤ 500000*fixedPolylogGauge I := by
  have hC := hierarchyConstant_ge_one L
  have hh := I.accuracy_positive L le_rfl
  have hnear : I.theta/500000 ≤ I.nearTolerance := by
    unfold FixedProblem.nearTolerance literalFinalX literalFinalAlpha
    have he : 4*hierarchyConstant L*(I.theta/(1000000*(hierarchyConstant L+1)*I.accuracy L))*I.accuracy L =
        (4*hierarchyConstant L*I.theta)/(1000000*(hierarchyConstant L+1)) := by
      field_simp [hh.ne',show hierarchyConstant L+1 ≠ 0 by linarith]
      <;> ring
    rw [he]
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<500000) (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) I.theta_positive.le]
  have hi : 1/I.nearTolerance ≤ 500000/I.theta := by
    simpa only [one_div_div] using one_div_le_one_div_of_le
      (div_pos I.theta_positive (by norm_num) : 0<I.theta/500000) hnear
  have hl := Real.log_le_log (one_div_pos.mpr I.nearTolerance_positive) hi
  have he : Real.log (500000/I.theta) = Real.log 500000+Real.log (1/I.theta) := by
    rw [Real.log_div (by norm_num) I.theta_positive.ne',one_div,Real.log_inv]
    ring
  rw [he] at hl
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<500000)
  have hz := fixedPolylogGauge_ge_one I
  have ht := (fixedPolylog_primitive_le I).2.2.2.1
  linarith

end
end HierarchicalAbsoluteSpectral
