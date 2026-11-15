import HierarchicalAbsoluteSpectral.BaseFixedPolylogBasic

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
variable {n m p r L : ℕ}

theorem fixedPolylog_initializer_log (I : FixedProblem n m p r L) :
    Real.log (16*initializerRatio m I.singleFailure) ≤ 400*fixedPolylogGauge I := by
  have hm := I.rank_positive.trans I.rank_le_core
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hβ1 : I.singleFailure ≤ 1 := by
    unfold FixedProblem.singleFailure
    linarith [I.delta_lt_one]
  have hR := gaussianCaptureRadius_ge_one m 1 I.singleFailure hm le_rfl hβ hβ1
  have hRpos : 0 < gaussianCaptureRadius m 1 I.singleFailure := by linarith
  have hbudget : 16*initializerRatio m I.singleFailure ≤
      32*Real.sqrt (m:ℝ)*gaussianCaptureRadius m 1 I.singleFailure := by
    unfold initializerRatio
    nlinarith [mul_nonneg (Real.sqrt_nonneg (m:ℝ)) (sub_nonneg.mpr hR)]
  have hpos : 0 < 16*initializerRatio m I.singleFailure := by
    have hh := initializerRatio_pos m I.singleFailure hm hβ
    positivity
  have hl := Real.log_le_log hpos hbudget
  have he : Real.log (32*Real.sqrt (m:ℝ)*gaussianCaptureRadius m 1 I.singleFailure) =
      Real.log 32+Real.log (m:ℝ)/2+
        3*(Real.log 100+Real.log (m:ℝ)+Real.log (1/I.singleFailure)) := by
    unfold gaussianCaptureRadius
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_sqrt hm0.le,Real.log_pow,Real.log_div (by positivity) hβ.ne',mul_one,
      Real.log_mul (by norm_num) hm0.ne',one_div,Real.log_inv]
    ring
  rw [he] at hl
  have hc32 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<32)
  have hc100 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
  have hmLog := (fixedPolylog_primitive_le I).2.2.1
  have hβLog := fixedPolylog_singleFailure_log I
  have hz := fixedPolylogGauge_ge_one I
  linarith

theorem fixedPolylog_queryCap_bound (I : FixedProblem n m p r L) :
    (I.queryCap:ℝ) ≤ 2000000*fixedPolylogGauge I := by
  have hβ : 0 < I.singleFailure := div_pos I.delta_positive (by norm_num)
  have hbudget := initializerRatio_pos m I.singleFailure (I.rank_positive.trans I.rank_le_core) hβ
  have hl := fixedPolylog_initializer_log I
  have hn := fixedPolylog_near_log I
  rw [one_div,Real.log_inv] at hn
  have hratio : Real.log ((16*initializerRatio m I.singleFailure)/I.nearTolerance) ≤
      500400*fixedPolylogGauge I := by
    rw [Real.log_div (by positivity) I.nearTolerance_positive.ne']
    linarith
  have hh := fixedPolylog_halving_bound (16*initializerRatio m I.singleFailure)
    I.nearTolerance (fixedPolylogGauge I) 500400 I.nearTolerance_positive
    (fixedPolylogGauge_ge_one I) (by norm_num) hratio
  change (I.queryCap:ℝ) ≤ _ at hh
  have hlog2 := family_log_two_lower
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 1+500400/Real.log 2 ≤ 2000000 := by
    have hd : 500400/Real.log 2 ≤ 1000800 := (div_le_iff₀ hlog2p).mpr (by linarith)
    linarith
  exact hh.trans (mul_le_mul_of_nonneg_right hc (by linarith [fixedPolylogGauge_ge_one I]))

theorem fixedPolylog_repetitions_bound (I : FixedProblem n m p r L) :
    (I.repetitions:ℝ) ≤ 5000000*fixedPolylogGauge I := by
  have hq := fixedPolylog_queryCap_bound I
  have hd := (fixedPolylog_primitive_le I).2.2.2.2.1
  rw [one_div,Real.log_inv] at hd
  have hc20 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<20)
  have hlogQ : Real.log ((I.queryCap:ℝ)+1) ≤ I.queryCap := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(I.queryCap:ℝ)+1)
    linarith
  have hz := fixedPolylogGauge_ge_one I
  have hl : Real.log (1/I.queryFailure) ≤ 2000020*fixedPolylogGauge I := by
    unfold FixedProblem.queryFailure
    rw [one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hh := fixedPolylog_halving_bound 1 I.queryFailure (fixedPolylogGauge I) 2000020
    I.queryFailure_positive hz (by norm_num) hl
  change (I.repetitions:ℝ) ≤ _ at hh
  have hlog2 := family_log_two_lower
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 1+2000020/Real.log 2 ≤ 5000000 := by
    have hd : 2000020/Real.log 2 ≤ 4000040 := (div_le_iff₀ hlog2p).mpr (by linarith)
    linarith
  exact hh.trans (mul_le_mul_of_nonneg_right hc (by linarith))

theorem fixedPolylog_sketchFailure_log (I : FixedProblem n m p r L) :
    Real.log (1/I.sketchFailure) ≤ ((L:ℝ)+20)*fixedPolylogGauge I := by
  have hd := (fixedPolylog_primitive_le I).2.2.2.2.1
  have hz := fixedPolylogGauge_ge_one I
  have hc20 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<20)
  have hL : Real.log ((L:ℝ)+1) ≤ L := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<(L:ℝ)+1)
    linarith
  have he : Real.log (1/I.sketchFailure) =
      Real.log 20+Real.log ((L:ℝ)+1)+Real.log (1/I.delta) := by
    unfold FixedProblem.sketchFailure
    rw [one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by positivity),
      Real.log_mul (by norm_num) (by positivity),one_div,Real.log_inv]
    ring
  rw [he]
  have hc : (L:ℝ)+19 ≤ ((L:ℝ)+19)*fixedPolylogGauge I :=
    by simpa using mul_le_mul_of_nonneg_left hz (show 0≤(L:ℝ)+19 by positivity)
  linarith

theorem fixedPolylog_embeddingMoment_bound (I : FixedProblem n m p r L) :
    (embeddingMomentOrder m I.sketchFailure:ℝ) ≤
      100*((L:ℝ)+2)*fixedPolylogGauge I := by
  have hδ : 0 < I.sketchFailure := by
    unfold FixedProblem.sketchFailure
    exact div_pos I.delta_positive (by positivity)
  have hδ1 : I.sketchFailure ≤ 1 := by
    unfold FixedProblem.sketchFailure
    apply (div_le_iff₀ (by positivity : (0:ℝ)<20*((L:ℝ)+1))).mpr
    have hL : (0:ℝ)≤L := Nat.cast_nonneg _
    linarith [I.delta_lt_one]
  have hm := I.rank_positive.trans I.rank_le_core
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmoment := embeddingMomentOrder_log_bound m I.sketchFailure hm hδ hδ1
  have hβ := fixedPolylog_sketchFailure_log I
  have hmlog := (fixedPolylog_primitive_le I).2.2.1
  have hz := fixedPolylogGauge_ge_one I
  have hc4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  have he : Real.log (4*(m:ℝ)/I.sketchFailure) =
      Real.log 4+Real.log (m:ℝ)+Real.log (1/I.sketchFailure) := by
    rw [Real.log_div (by positivity) hδ.ne',Real.log_mul (by norm_num) hm0.ne',one_div,Real.log_inv]
    ring
  have harg : Real.log (4*(m:ℝ)/I.sketchFailure) ≤
      ((L:ℝ)+24)*fixedPolylogGauge I := by rw [he]; nlinarith only [hβ,hmlog,hc4,hz]
  have hlog2 := family_log_two_lower
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ((L:ℝ)+24)/Real.log 2 ≤ 2*((L:ℝ)+24) := by
    apply (div_le_iff₀ hlog2p).mpr
    have hh := mul_le_mul_of_nonneg_left hlog2 (show 0≤2*((L:ℝ)+24) by positivity)
    nlinarith only [hh]
  calc
    _ ≤ 2+Real.log (4*(m:ℝ)/I.sketchFailure)/Real.log 2 := hmoment
    _ ≤ 2+(((L:ℝ)+24)*fixedPolylogGauge I)/Real.log 2 := by gcongr
    _ = 2+(((L:ℝ)+24)/Real.log 2)*fixedPolylogGauge I := by ring
    _ ≤ 2+2*((L:ℝ)+24)*fixedPolylogGauge I := by gcongr
    _ ≤ _ := by
      have hL : (0:ℝ)≤L := Nat.cast_nonneg _
      have hLZ := mul_nonneg hL (show 0≤fixedPolylogGauge I by linarith)
      nlinarith only [hz,hLZ]

def fixedPolylogSketchCoefficient (L : ℕ) : ℝ := 3000*((L:ℝ)+1)*((L:ℝ)+2)

theorem fixedPolylog_sketchLogFactor_bound (I : FixedProblem n m p r L) :
    (fixedSketchLogFactor I:ℝ) ≤ fixedPolylogSketchCoefficient L*fixedPolylogGauge I := by
  obtain ⟨hn,hp⟩ := fixedPolylog_padding_bound I
  have hm := fixedPolylog_embeddingMoment_bound I
  have hz := fixedPolylogGauge_ge_one I
  have hinner : 128*((dyadicPaddingLevel n:ℝ)+(dyadicPaddingLevel p:ℝ)+2)+
      6*(embeddingMomentOrder m I.sketchFailure:ℝ)+40 ≤
        (128*8+600*((L:ℝ)+2)+40)*fixedPolylogGauge I := by nlinarith only [hn,hp,hm,hz]
  have hc : 128*8+600*((L:ℝ)+2)+40 ≤ 3000*((L:ℝ)+2) := by
    have hL : (0:ℝ)≤L := Nat.cast_nonneg _
    linarith
  have hc' := mul_le_mul_of_nonneg_right hc (show 0≤fixedPolylogGauge I by linarith)
  have hh := mul_le_mul_of_nonneg_left (hinner.trans hc') (show 0≤(L:ℝ)+1 by positivity)
  simpa only [fixedSketchLogFactor,fixedPolylogSketchCoefficient,Nat.cast_mul,Nat.cast_add,
    Nat.cast_ofNat,Nat.cast_one,mul_assoc,mul_left_comm,mul_comm] using hh

end
end HierarchicalAbsoluteSpectral
