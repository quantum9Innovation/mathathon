import HierarchicalAbsoluteSpectral.CorollaryTwoLevelSketches
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalKernels
import HierarchicalAbsoluteSpectral.BaseMainTotalCost
import HierarchicalAbsoluteSpectral.BaseMainTapeCost
import HierarchicalAbsoluteSpectral.RuntimeFamilyDimensions

/-! Counted initial sketch formation and coarse support work for the
two-level program. The caps include input reads, padded Gaussian draws,
the executed dyadic budgets, and all stored sketch entries. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Filter Matrix SRHT Matmul.RectangularPrograms
open ArithmeticProgram hiding pure
variable {N m r : ℕ}

def twoLevelInitialSketchWorkCap (N m : ℕ) (β : ℝ) : ℕ :=
  2*m*N+12*2^dyadicPaddingLevel N+4*sketchFormationCap N m β

theorem twoLevelInitialSketchWorkCap_actual (I : TwoLevelProblem N m r)
    (g : MainRandomTape I.fixed) :
    m*(N+N)+3*(1+1)*(2^dyadicPaddingLevel N+2^dyadicPaddingLevel N)+
        (mainSketchProgram I.fixed g).work ≤
      twoLevelInitialSketchWorkCap N m I.fixed.sketchFailure := by
  have h := mainSketchProgram_work_le I.fixed g
  unfold twoLevelInitialSketchWorkCap
  nlinarith only [h]

def twoLevelSketchLogCoefficient (D : ℝ) : ℝ :=
  1200+12*((D+5)/Real.log 2)

theorem twoLevelInitialSketchWorkCap_log_bound (N m : ℕ) (β D : ℝ)
    (hN : 0 < N) (hm : 2 ≤ m) (hβ : 0 < β) (hβ1 : β ≤ 1) (hD : 0 ≤ D)
    (hconfidence : Real.log (1/β) ≤ D*Real.log (m:ℝ)) :
    (twoLevelInitialSketchWorkCap N m β:ℝ) ≤
      twoLevelSketchLogCoefficient D*(m:ℝ)*(N:ℝ)*
        (1+Real.log (N:ℝ)+Real.log (m:ℝ)) := by
  have hm1 : 1 ≤ m := by omega
  have hmn : (1:ℝ) ≤ (m:ℝ)*(N:ℝ) := by
    exact_mod_cast (show 1 ≤ m*N from one_le_mul hm1 hN)
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg hmr
  have hlN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNr
  have hpad : (2^dyadicPaddingLevel N:ℕ) ≤ 2*N := (dyadicPaddingLevel_lt_two N hN).le
  have hpadR : ((2^dyadicPaddingLevel N:ℕ):ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hpad
  have hlevel := leastHalvings_log_bound (N:ℝ) 1 (by norm_num : (0:ℝ)<1)
  have hlevel' : (dyadicPaddingLevel N:ℝ)+1 ≤ 2+2*Real.log (N:ℝ) := by
    have htwo := family_log_two_lower
    have hlog2 : 0 < Real.log 2 := by linarith
    have hdiv : Real.log (N:ℝ)/Real.log 2 ≤ 2*Real.log (N:ℝ) := by
      apply (div_le_iff₀ hlog2).mpr
      nlinarith
    simp only [div_one,max_eq_right hNr] at hlevel
    change (dyadicPaddingLevel N:ℝ) ≤ 1+Real.log (N:ℝ)/Real.log 2 at hlevel
    linarith
  have horder := family_embedding_order_uniform_bound m β D hm hβ hβ1 hconfidence
  have hformation : (sketchFormationCap N m β:ℝ) ≤
      128*(m:ℝ)*((dyadicPaddingLevel N:ℝ)+1)*(N:ℝ)+
        3*(embeddingMomentOrder m β:ℝ)+20 := by
    exact_mod_cast sketchFormationCap_input_bound N m β hN hm1
  have hK : 0 ≤ (D+5)/Real.log 2 := by positivity
  have hlevelmul := mul_le_mul_of_nonneg_left hlevel'
    (show 0 ≤ 512*(m:ℝ)*(N:ℝ) by positivity)
  have hpadmul := mul_le_mul_of_nonneg_left hpadR (by norm_num : (0:ℝ)≤12)
  have hNscale : (N:ℝ) ≤ (m:ℝ)*(N:ℝ) := by nlinarith
  have hlogscale := mul_le_mul_of_nonneg_right hmn hlm
  have hlogscaleN := mul_le_mul_of_nonneg_right hmn hlN
  have horderscale := mul_le_mul_of_nonneg_left hlogscale
    (show 0 ≤ 12*((D+5)/Real.log 2) by positivity)
  have hcross : 0 ≤ 12*((D+5)/Real.log 2)*(m:ℝ)*(N:ℝ)*Real.log (N:ℝ) := by positivity
  have hKbase : 0 ≤ 12*((D+5)/Real.log 2)*(m:ℝ)*(N:ℝ) := by positivity
  unfold twoLevelInitialSketchWorkCap twoLevelSketchLogCoefficient
  push_cast
  push_cast at hpadR hpadmul
  nlinarith [hlevelmul,hpadmul,horderscale]

/-- Uniform in the input matrices, stored samples, and confidence parameter.
Every positive slack absorbs the executed logarithmic sketch budgets. -/
theorem twoLevelInitialSketchWorkCap_eventually (c B ε : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → (N:ℝ) ≤ (m:ℝ)^B →
      (twoLevelInitialSketchWorkCap N m I.fixed.sketchFailure:ℝ) ≤
        (m:ℝ)*(N:ℝ)*(m:ℝ)^ε := by
  let K := twoLevelSketchLogCoefficient (c+6)
  have hK : 0 ≤ K := by dsimp [K,twoLevelSketchLogCoefficient]; positivity
  have habs := family_core_polylog_absorbed (K*(B+3)) 1 ε 0 (by positivity) hε
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually habs,eventually_ge_atTop (2:ℕ)] with m hmAbs hm N r I hδ hN
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hNpos : 0 < N := (lt_of_lt_of_le (by omega : 0 < m) I.core_le_side)
  have hlogm : Real.log 2 ≤ Real.log (m:ℝ) := Real.log_le_log (by norm_num) hmR
  have hlogm0 : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg hm1
  have hlogN : Real.log (N:ℝ) ≤ B*Real.log (m:ℝ) := by
    have h := Real.log_le_log (show (0:ℝ)<N by exact_mod_cast hNpos) hN
    rwa [Real.log_rpow hm0] at h
  have hβ1 : I.fixed.sketchFailure ≤ 1 := by
    simp only [FixedProblem.sketchFailure,Nat.cast_one]
    change I.delta/(20*((1:ℝ)+1)) ≤ 1
    linarith [I.delta_lt_one]
  have hconf := I.sketchFailure_log_bound c hlogm hδ
  have hcap := twoLevelInitialSketchWorkCap_log_bound N m I.fixed.sketchFailure (c+6)
    hNpos hm (mainSketchFailure_positive I.fixed) hβ1 (by linarith) hconf
  have hlogs : 1+Real.log (N:ℝ)+Real.log (m:ℝ) ≤ (B+3)*Real.log (m:ℝ) := by
    have hh := family_log_two_lower
    nlinarith only [hlogN,hlogm,hh]
  have hlogscaled := mul_le_mul_of_nonneg_left hlogs
    (show 0 ≤ K*(m:ℝ)*(N:ℝ) by positivity)
  have habs' : K*(B+3)*Real.log (m:ℝ) ≤ (m:ℝ)^ε := by
    simpa only [Real.rpow_zero,Real.rpow_one,mul_one] using hmAbs
  calc
    _ ≤ K*(m:ℝ)*(N:ℝ)*(1+Real.log (N:ℝ)+Real.log (m:ℝ)) := hcap
    _ ≤ K*(m:ℝ)*(N:ℝ)*((B+3)*Real.log (m:ℝ)) := hlogscaled
    _ = (m:ℝ)*(N:ℝ)*(K*(B+3)*Real.log (m:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left habs' (by positivity)

theorem twoLevelInitialSketchWorkCap_power_eventually (c B ε : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → (N:ℝ) ≤ (m:ℝ)^B →
      (twoLevelInitialSketchWorkCap N m I.fixed.sketchFailure:ℝ) ≤ (m:ℝ)^(1+B+ε) := by
  filter_upwards [twoLevelInitialSketchWorkCap_eventually c B ε hc hB hε,
    eventually_ge_atTop (1:ℕ)] with m hm hm1 N r I hδ hN
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm1
  calc
    _ ≤ (m:ℝ)*(N:ℝ)*(m:ℝ)^ε := hm N r I hδ hN
    _ ≤ (m:ℝ)*(m:ℝ)^B*(m:ℝ)^ε := by gcongr
    _ = (m:ℝ)^(1:ℝ)*(m:ℝ)^B*(m:ℝ)^ε := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hm0,← Real.rpow_add hm0]

theorem coarseSupportWorkCap_bound_of_scalar_kernels
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ C*(D:ℝ)^p)
    (m s t : ℕ) (hm : 1 ≤ m) (B : ℝ)
    (hleft : ((kernels m s m).cost:ℝ) ≤ B)
    (hright : ((kernels m t m).cost:ℝ) ≤ B) :
    (coarseSupportWorkCap kernels m s t:ℝ) ≤ 2*B+11*(C+1)*(m:ℝ)^p := by
  have hglobal := fun a b c D (_hmax : 1 ≤ max a (max b c)) hD ha hb hc => hK a b c D hD ha hb hc
  have henv := kernelEnvelope_bound kernels C p hC hglobal m hm
  have hpsd := psdGramCost_bound kernels C p hC hp hglobal m hm
  have hpow : 0 ≤ (m:ℝ)^p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold coarseSupportWorkCap
  push_cast
  nlinarith only [hleft,hright,henv,hpsd,hpow]

theorem twoLevelMainSketch_coarse_rows (I : TwoLevelProblem N m r)
    (g : MainRandomTape I.fixed) :
    ((mainSketchProgram I.fixed g).eval.levelA 0).1 ≤
        embeddingComputedRowCount (2^dyadicPaddingLevel N) m (twoLevelH0 m) I.fixed.sketchFailure ∧
    ((mainSketchProgram I.fixed g).eval.levelB 0).1 ≤
        embeddingComputedRowCount (2^dyadicPaddingLevel N) m (twoLevelH0 m) I.fixed.sketchFailure := by
  rw [mainSketchProgram_eval]
  constructor
  · change (boundedSketchProgram I.fixed.A (I.fixed.accuracy 0) I.fixed.sketchFailure
      (I.fixed.accuracy_positive 0 (by omega)) (mainSketchFailure_positive I.fixed)
      (mainLeftSketchInput I.fixed g 0)).eval.rows ≤ _
    rw [twoLevel_boundedSketch_rows]
    simpa only [TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,ite_true] using
      min_le_right N (embeddingComputedRowCount (2^dyadicPaddingLevel N) m
        (I.fixed.accuracy 0) I.fixed.sketchFailure)
  · change (boundedSketchProgram I.fixed.Bᵀ (I.fixed.accuracy 0) I.fixed.sketchFailure
      (I.fixed.accuracy_positive 0 (by omega)) (mainSketchFailure_positive I.fixed)
      (mainRightSketchInput I.fixed g 0)).eval.rows ≤ _
    rw [twoLevel_boundedSketch_rows]
    simpa only [TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,ite_true] using
      min_le_right N (embeddingComputedRowCount (2^dyadicPaddingLevel N) m
        (I.fixed.accuracy 0) I.fixed.sketchFailure)

theorem twoLevelMainSketch_coarse_rows_eventually (c η : ℝ) (hc : 0 ≤ c) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → ∀ g : MainRandomTape I.fixed,
      (((mainSketchProgram I.fixed g).eval.levelA 0).1:ℝ) ≤ (m:ℝ)^((57/50:ℝ)+η) ∧
      (((mainSketchProgram I.fixed g).eval.levelB 0).1:ℝ) ≤ (m:ℝ)^((57/50:ℝ)+η) := by
  filter_upwards [twoLevel_sketch_row_exponents c η hc hη] with m hm N r I hδ g
  have hrows := (hm N r I hδ (2^dyadicPaddingLevel N)).1
  have hactual := twoLevelMainSketch_coarse_rows I g
  exact ⟨(Nat.cast_le.mpr hactual.1).trans hrows,(Nat.cast_le.mpr hactual.2).trans hrows⟩

/-- The coarse support cap is bounded for the one fixed diagonal kernel
family; the conclusion is uniform in every stored sketch outcome. -/
theorem twoLevelCoarseSupportWorkCap_eventually (c ζ : ℝ) (hc : 0 ≤ c) (hζ : 0 < ζ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → ∀ g : MainRandomTape I.fixed,
      (coarseSupportWorkCap (twoLevelRuntimeFinalKernels m) m
        ((mainSketchProgram I.fixed g).eval.levelA 0).1
        ((mainSketchProgram I.fixed g).eval.levelB 0).1:ℝ) ≤
          (m:ℝ)^((3362/1425:ℝ)+ζ) := by
  obtain ⟨C,hC,hGlobal⟩ := twoLevelRuntimeFinalKernels_global
  obtain ⟨δ,hδ,hRect⟩ := twoLevelRuntimeFinalKernels_scalene (ζ/2) (by positivity)
  let shape := twoLevelCoarseShape.cyclic.swap
  have hshape : shape ∈ twoLevelRuntimeFinalShapes := by
    simp [shape,twoLevelRuntimeFinalShapes,PositiveScaleneShape.permutations]
  have hshapeBound : scaleneBound shape.u shape.v shape.w = (3362:ℝ)/1425 := by
    norm_num [shape,twoLevelCoarseShape,PositiveScaleneShape.cyclic,
      PositiveScaleneShape.swap,scaleneBound]
  have hp : 2 ≤ twoLevelRuntimeGlobalExponent := by norm_num [twoLevelRuntimeGlobalExponent]
  have hmargin : twoLevelRuntimeGlobalExponent < (3362/1425:ℝ)+ζ/2 := by
    norm_num [twoLevelRuntimeGlobalExponent]
    linarith
  have hPSD := family_core_polylog_absorbed (11*(C+1)) 0
    ((3362/1425:ℝ)+ζ/2) twoLevelRuntimeGlobalExponent (by positivity) hmargin
  have hthree := family_core_polylog_absorbed 3 0
    ((3362/1425:ℝ)+ζ) ((3362/1425:ℝ)+ζ/2) (by norm_num) (by linarith)
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hRect,twoLevelMainSketch_coarse_rows_eventually c δ hc hδ,
    hcast.eventually hPSD,hcast.eventually hthree,eventually_ge_atTop (1:ℕ)]
    with m hmRect hmRows hmPSD hmThree hm N r I hδI g
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hwidth : m ≤ width (1+δ) m := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hmR (show (1:ℝ) ≤ 1+δ by linarith)
    rw [Real.rpow_one] at hpow
    exact_mod_cast hpow.trans (Nat.le_ceil ((m:ℝ)^(1+δ)))
  have hrows := hmRows N r I hδI g
  have hA : ((mainSketchProgram I.fixed g).eval.levelA 0).1 ≤ width ((57/50:ℝ)+δ) m := by
    exact_mod_cast hrows.1.trans (Nat.le_ceil ((m:ℝ)^((57/50:ℝ)+δ)))
  have hB : ((mainSketchProgram I.fixed g).eval.levelB 0).1 ≤ width ((57/50:ℝ)+δ) m := by
    exact_mod_cast hrows.2.trans (Nat.le_ceil ((m:ℝ)^((57/50:ℝ)+δ)))
  have hleft := hmRect shape hshape m ((mainSketchProgram I.fixed g).eval.levelA 0).1 m
    (show shape.Fits δ m m ((mainSketchProgram I.fixed g).eval.levelA 0).1 m from
      ⟨hwidth,hA,hwidth⟩)
  have hright := hmRect shape hshape m ((mainSketchProgram I.fixed g).eval.levelB 0).1 m
    (show shape.Fits δ m m ((mainSketchProgram I.fixed g).eval.levelB 0).1 m from
      ⟨hwidth,hB,hwidth⟩)
  rw [hshapeBound] at hleft hright
  have hcap := coarseSupportWorkCap_bound_of_scalar_kernels (twoLevelRuntimeFinalKernels m)
    C twoLevelRuntimeGlobalExponent hC hp (hGlobal m) m _ _ hm _ hleft hright
  have hPSD' : 11*(C+1)*(m:ℝ)^twoLevelRuntimeGlobalExponent ≤
      (m:ℝ)^((3362/1425:ℝ)+ζ/2) := by
    simpa only [Real.rpow_zero,mul_one] using hmPSD
  have hthree' : 3*(m:ℝ)^((3362/1425:ℝ)+ζ/2) ≤ (m:ℝ)^((3362/1425:ℝ)+ζ) := by
    simpa only [Real.rpow_zero,mul_one] using hmThree
  exact hcap.trans (by linarith only [hPSD',hthree'])

theorem twoLevelCoarseSupportProgram_work_eventually (c ζ : ℝ) (hc : 0 ≤ c) (hζ : 0 < ζ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → ∀ g : MainRandomTape I.fixed,
      let S := (mainSketchProgram I.fixed g).eval
      ((coarseSupportProgram (twoLevelRuntimeFinalKernels m) S.initialA S.initialB).work:ℝ) ≤
        (m:ℝ)^((3362/1425:ℝ)+ζ) := by
  filter_upwards [twoLevelCoarseSupportWorkCap_eventually c ζ hc hζ] with m hm N r I hδ g
  have hwork := coarseSupportProgram_work_bound (twoLevelRuntimeFinalKernels m)
    (mainSketchProgram I.fixed g).eval.initialA (mainSketchProgram I.fixed g).eval.initialB I.core_positive
  exact (Nat.cast_le.mpr hwork).trans (hm N r I hδ g)

#print axioms twoLevelInitialSketchWorkCap_eventually
#print axioms twoLevelCoarseSupportProgram_work_eventually

end
end HierarchicalAbsoluteSpectral
