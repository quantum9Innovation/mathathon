import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalActions
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalAlgebra
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalCharge

/-! Discharging the finite thin-core envelope from the single certified
kernel family, the executed sketch sizes, and the computed degrees. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Filter
variable {N m r : ℕ}

def twoLevelRuntimeFinalKernelConstant : ℝ := chosenTwoLevelGlobalKernelFamily.constant

theorem twoLevelRuntimeFinalKernelConstant_pos : 0 < twoLevelRuntimeFinalKernelConstant :=
  chosenTwoLevelGlobalKernelFamily.constant_pos

theorem twoLevelRuntimeFinalKernels_bound (m a b c D : ℕ)
    (hD : 1 ≤ D) (ha : a ≤ D) (hb : b ≤ D) (hc : c ≤ D) :
    ((twoLevelRuntimeFinalKernels m a b c).cost:ℝ) ≤
      twoLevelRuntimeFinalKernelConstant*(D:ℝ)^twoLevelRuntimeGlobalExponent := by
  have hcost : (twoLevelRuntimeFinalKernels m a b c).cost ≤
      (chosenTwoLevelGlobalKernelFamily.kernel a b c).cost :=
    (finiteScaleneKernelFamily_cost_le_fallback _ _ m a b c).trans
      (ArithmeticKernel.cheaper_cost_le_left _ _)
  exact (Nat.cast_le.mpr hcost).trans (chosenTwoLevelGlobalKernelFamily.bound a b c D hD ha hb hc)

theorem twoLevelRuntimeThinCoreEnvelope_of_leaves
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed)
    (C : MainSupportData (mainSketchProgram I.fixed g).eval) (hm : 2 ≤ m)
    (hfactor : ∀ b ≤ r+1,
      mainFactorActionCost (twoLevelRuntimeFinalKernels m) I.fixed (mainSketchProgram I.fixed g).eval C b 1 ≤
        twoLevelRuntimeActionCharge m)
    (htrue : ∀ b ≤ r+1,
      mainTrueActionCost (twoLevelRuntimeFinalKernels m) I.fixed (mainSketchProgram I.fixed g).eval C b ≤
        twoLevelRuntimeActionCharge m)
    (hT : (matrixProductCost (twoLevelRuntimeFinalKernels m) N m (r+1):ℝ) ≤
      (m:ℝ)^twoLevelRuntimeGlobalExponent)
    (hTA : matrixProductCost (twoLevelRuntimeFinalKernels m) N m (r+1) ≤ twoLevelRuntimeActionCharge m)
    (hquery : ∀ hr : r < C.pair.dimension,
      mainQueryDegree I.fixed (mainSketchProgram I.fixed g).eval C hr ≤ twoLevelRuntimeDegreeCharge m)
    (hraw : ∀ hr : r < C.pair.dimension,
      (mainQueryDegree I.fixed (mainSketchProgram I.fixed g).eval C hr+1)*(r+1) ≤ m)
    (hstrong : ∀ hk : 1 ≤ C.pair.dimension,
      mainStrongDegree I.fixed (mainSketchProgram I.fixed g).eval C hk ≤ twoLevelRuntimeDegreeCharge m) :
    TwoLevelRuntimeThinCoreEnvelope (twoLevelRuntimeFinalKernels m) I.fixed
      (mainSketchProgram I.fixed g).eval C twoLevelRuntimeFinalKernelConstant twoLevelRuntimeGlobalExponent
      (twoLevelRuntimeActionCharge m) (twoLevelRuntimeSmallCharge twoLevelRuntimeFinalKernelConstant m)
      (twoLevelRuntimeSmallCharge twoLevelRuntimeFinalKernelConstant m) (twoLevelRuntimeDegreeCharge m) := by
  have hC := twoLevelRuntimeFinalKernelConstant_pos
  have hp : 2 ≤ twoLevelRuntimeGlobalExponent := by norm_num [twoLevelRuntimeGlobalExponent]
  have hm1 : 1 ≤ m := by omega
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hApos : 1 ≤ twoLevelRuntimeActionCharge m := by
    have hpA := Real.one_le_rpow hmR twoLevelRuntimeCoreExponent_bounds.1
    exact_mod_cast hpA.trans (Nat.le_ceil ((m:ℝ)^twoLevelRuntimeActionExponent))
  have hBpos : 1 ≤ twoLevelRuntimeSmallCharge twoLevelRuntimeFinalKernelConstant m := by
    simpa only [twoLevelRuntimeSmallCharge,twoLevelRuntimeCoreAlgebraCharge] using
      twoLevelRuntimeCoreAlgebraCharge_positive twoLevelRuntimeFinalKernelConstant twoLevelRuntimeGlobalExponent m
        hC (by linarith) hm1
  have hsmall := twoLevelRuntimeSmallAlgebraCharge_bounds (twoLevelRuntimeFinalKernels m)
    twoLevelRuntimeFinalKernelConstant twoLevelRuntimeGlobalExponent hC hp (twoLevelRuntimeFinalKernels_bound m)
    hm C.pair.dimension_le_fin I.rank_le_core
  have hbase := I.runtime_base_algebra_charge (twoLevelRuntimeFinalKernels m)
    twoLevelRuntimeFinalKernelConstant twoLevelRuntimeGlobalExponent hC hp (twoLevelRuntimeFinalKernels_bound m)
    hm C.pair.dimension C.pair.dimension_le_fin
  have houtput := twoLevelRuntimeThinOutputCoreCharge_bounds (twoLevelRuntimeFinalKernels m)
    twoLevelRuntimeFinalKernelConstant twoLevelRuntimeGlobalExponent hC hp (twoLevelRuntimeFinalKernels_bound m)
    I.fixed (mainSketchProgram I.fixed g).eval C hm I.core_le_side I.rank_le_core hT
  simp only [twoLevelRuntimeCoreAlgebraCharge] at hsmall hbase houtput
  refine {
    action_positive := hApos
    core_positive := hBpos
    output_positive := hBpos
    factor := hfactor
    true_action := htrue
    core_kernel := ?_
    block_entries := ?_
    base := hbase
    core_envelope := hsmall.1
    psd := hsmall.2.1
    square_entries := hsmall.2.2.1
    dimension := hsmall.2.2.2.1
    exact_output := houtput.1
    physical_range := houtput.2.1
    projection := houtput.2.2
    physical_kernel := ?_
    support_kernel := ?_
    query_degree := hquery
    query_range := fun hr => hsmall.2.2.2.2.2 _ (hraw hr)
    test := hsmall.2.2.2.2.1
    strong_degree := hstrong }
  · intro b hb
    exact (kernel_cost_le_matrixProductCost (twoLevelRuntimeFinalKernels m) C.pair.dimension C.pair.dimension b
      N m (r+1) (C.pair.dimension_le_fin.trans I.core_le_side) C.pair.dimension_le_fin hb).trans hTA
  · have hh := matrixProductCost_scalar_floor (twoLevelRuntimeFinalKernels m) N m (r+1)
    have hmul := Nat.mul_le_mul_right (r+1) C.pair.dimension_le_fin
    omega
  · exact (kernel_cost_le_matrixProductCost (twoLevelRuntimeFinalKernels m) N m r N m (r+1)
      le_rfl le_rfl (by omega)).trans hTA
  · exact (kernel_cost_le_matrixProductCost (twoLevelRuntimeFinalKernels m) m C.pair.dimension r N m (r+1)
      I.core_le_side C.pair.dimension_le_fin (by omega)).trans hTA

theorem twoLevelRuntimeFinalCoreCharge_bound_eventually (c : ℝ) (hc : 0 ≤ c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (N r : ℕ) (I : TwoLevelProblem N m r), (m:ℝ)^(-c) ≤ I.delta →
      (N:ℝ) ≤ (m:ℝ)^((59/50:ℝ)+τ) → ∀ g : MainRandomTape I.fixed,
      ∀ C : MainSupportData (mainSketchProgram I.fixed g).eval,
      twoLevelFactorCoreWorkCap (twoLevelRuntimeFinalKernels m) I.fixed (mainSketchProgram I.fixed g).eval C
        (fun hr => mainFlexibleQueryWorkCap (twoLevelRuntimeFinalKernels m)
          (rangeDeflationWorkCap (twoLevelRuntimeFinalKernels m)) I.fixed (mainSketchProgram I.fixed g).eval C hr
            twoLevelRuntimeFinalKernelConstant twoLevelRuntimeGlobalExponent) ≤
        twoLevelRuntimeFinalCoreCharge c twoLevelRuntimeFinalKernelConstant m := by
  have hη : 0 < twoLevelRuntimeFinalSlack := by norm_num [twoLevelRuntimeFinalSlack]
  obtain ⟨τ,hτ,hActions⟩ := twoLevelRuntime_actions_eventually c twoLevelRuntimeFinalSlack hc hη
  obtain ⟨δ,hδ,hProducts⟩ := twoLevelRuntime_product_eventually twoLevelRuntimeFinalSlack hη
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hRank := family_core_polylog_absorbed 3 0 ((14/25:ℝ)+δ) (14/25)
    (by norm_num) (by linarith)
  refine ⟨min τ δ,lt_min hτ hδ,?_⟩
  filter_upwards [hActions,hProducts,hcast.eventually hRank,
    twoLevelQueryDegree_eventually twoLevelRuntimeFinalSlack hη,
    twoLevelRuntimeStrongDegree_eventually c twoLevelRuntimeFinalSlack hc hη,
    twoLevel_main_raw_width_eventually,eventually_ge_atTop (2:ℕ)]
    with m hmActions hmProducts hmRank hmQuery hmStrong hmRaw hm N r I hδI hN g C
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hNAction : (N:ℝ) ≤ (m:ℝ)^((59/50:ℝ)+τ) := hN.trans
    (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith [min_le_left τ δ]))
  have hNProduct : (N:ℝ) ≤ (m:ℝ)^((59/50:ℝ)+δ) := hN.trans
    (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith [min_le_right τ δ]))
  have hmb : (m:ℝ) ≤ (m:ℝ)^((1:ℝ)+δ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1
      (show (1:ℝ) ≤ 1+δ by linarith)
  have hrank := twoLevel_rounded_rank_width m r I.core_positive I.rank_le_power
  have hrank' : ((r+1:ℕ):ℝ) ≤ (m:ℝ)^((14/25:ℝ)+δ) := by
    have hh : 3*(m:ℝ)^(14/25:ℝ) ≤ (m:ℝ)^((14/25:ℝ)+δ) := by
      simpa only [Real.rpow_zero,mul_one] using hmRank
    simpa only [Nat.cast_add,Nat.cast_one] using hrank.trans hh
  have hT := hmProducts twoLevelTrueShape twoLevelRuntime_true_permutations
    (by rw [twoLevelTrueShape_bound]; norm_num [twoLevelTrueShape])
    (by rw [twoLevelTrueShape_bound]; norm_num [twoLevelTrueShape])
    (by rw [twoLevelTrueShape_bound]; norm_num [twoLevelTrueShape])
    N m (r+1) hNProduct hmb hrank'
  rw [twoLevelTrueShape_bound] at hT
  have hTglobal : (matrixProductCost (twoLevelRuntimeFinalKernels m) N m (r+1):ℝ) ≤
      (m:ℝ)^twoLevelRuntimeGlobalExponent := hT.trans
    (Real.rpow_le_rpow_of_exponent_le hm1 (by
      norm_num [twoLevelRuntimeFinalSlack,twoLevelRuntimeGlobalExponent]))
  have hTAreal : (matrixProductCost (twoLevelRuntimeFinalKernels m) N m (r+1):ℝ) ≤
      (m:ℝ)^twoLevelRuntimeActionExponent := hT.trans
    (Real.rpow_le_rpow_of_exponent_le hm1 (by
      norm_num [twoLevelRuntimeFinalSlack,twoLevelRuntimeActionExponent]))
  have hTA : matrixProductCost (twoLevelRuntimeFinalKernels m) N m (r+1) ≤ twoLevelRuntimeActionCharge m := by
    exact_mod_cast hTAreal.trans (Nat.le_ceil ((m:ℝ)^twoLevelRuntimeActionExponent))
  have hActionsHere := hmActions N r I hδI hNAction g C
  have hfactor : ∀ b ≤ r+1,
      mainFactorActionCost (twoLevelRuntimeFinalKernels m) I.fixed (mainSketchProgram I.fixed g).eval C b 1 ≤
        twoLevelRuntimeActionCharge m := by
    intro b hb
    have hh := (hActionsHere b hb).2.2
    exact_mod_cast hh.trans (Nat.le_ceil ((m:ℝ)^twoLevelRuntimeActionExponent))
  have htrue : ∀ b ≤ r+1,
      mainTrueActionCost (twoLevelRuntimeFinalKernels m) I.fixed (mainSketchProgram I.fixed g).eval C b ≤
        twoLevelRuntimeActionCharge m := by
    intro b hb
    have hh := (hActionsHere b hb).1
    have hp : (m:ℝ)^((9006001/4130000:ℝ)+twoLevelRuntimeFinalSlack) ≤
        (m:ℝ)^twoLevelRuntimeActionExponent :=
      Real.rpow_le_rpow_of_exponent_le hm1 (by
        norm_num [twoLevelRuntimeActionExponent,twoLevelRuntimeFinalSlack])
    exact_mod_cast (hh.trans hp).trans (Nat.le_ceil ((m:ℝ)^twoLevelRuntimeActionExponent))
  have hquery : ∀ hr : r < C.pair.dimension,
      mainQueryDegree I.fixed (mainSketchProgram I.fixed g).eval C hr ≤ twoLevelRuntimeDegreeCharge m := by
    intro hr
    have hk : 1 ≤ C.pair.dimension := by omega
    have hq := hmQuery N r I C.pair.dimension hk C.pair.dimension_le_fin
    have he : twoLevelQueryDegree I C.pair.dimension hk =
        mainQueryDegree I.fixed (mainSketchProgram I.fixed g).eval C hr := rfl
    rw [he] at hq
    exact_mod_cast hq.trans (Nat.le_ceil ((m:ℝ)^twoLevelRuntimeDegreeExponent))
  have hraw : ∀ hr : r < C.pair.dimension,
      (mainQueryDegree I.fixed (mainSketchProgram I.fixed g).eval C hr+1)*(r+1) ≤ m := by
    intro hr
    have hh := hmRaw N r I (mainSketchProgram I.fixed g).eval C hr
    have he : mainQueryDegree I.fixed (mainSketchProgram I.fixed g).eval C hr =
        mainKrylovDegree I.fixed (mainSketchProgram I.fixed g).eval C hr := rfl
    rw [he]
    exact (Nat.mul_le_mul_right (r+1) (by omega :
      mainKrylovDegree I.fixed (mainSketchProgram I.fixed g).eval C hr+1 ≤
        2*mainKrylovDegree I.fixed (mainSketchProgram I.fixed g).eval C hr+1)).trans hh.le
  have hstrong : ∀ hk : 1 ≤ C.pair.dimension,
      mainStrongDegree I.fixed (mainSketchProgram I.fixed g).eval C hk ≤ twoLevelRuntimeDegreeCharge m := by
    intro hk
    have hh := hmStrong N r I hδI C.pair.dimension hk C.pair.dimension_le_fin
    rw [twoLevelRuntimeStrongDegree_eq_main I (mainSketchProgram I.fixed g).eval C hk] at hh
    exact_mod_cast hh.trans (Nat.le_ceil ((m:ℝ)^twoLevelRuntimeDegreeExponent))
  have hEnvelope := twoLevelRuntimeThinCoreEnvelope_of_leaves I g C hm
    hfactor htrue hTglobal hTA hquery hraw hstrong
  have hcore := TwoLevelRuntimeThinCoreEnvelope.core_work (twoLevelRuntimeFinalKernels m) I.fixed
    (mainSketchProgram I.fixed g).eval C twoLevelRuntimeFinalKernelConstant twoLevelRuntimeGlobalExponent
    (twoLevelRuntimeActionCharge m) (twoLevelRuntimeSmallCharge twoLevelRuntimeFinalKernelConstant m)
    (twoLevelRuntimeSmallCharge twoLevelRuntimeFinalKernelConstant m) (twoLevelRuntimeDegreeCharge m) hEnvelope
  have hlog2 : Real.log 2 ≤ Real.log (m:ℝ) := Real.log_le_log (by norm_num) hmR
  have hqueryCap : I.fixed.queryCap ≤ twoLevelRuntimeQueryCharge c m := by
    exact_mod_cast (I.queryCap_log_bound c hc hlog2 hδI).trans
      (Nat.le_ceil (twoLevelQueryCapCoefficient c*Real.log (m:ℝ)))
  have hrepetitions : I.fixed.repetitions ≤ twoLevelRuntimeRepetitionCharge c m := by
    exact_mod_cast (I.repetitions_log_bound c hc hlog2 hδI).trans
      (Nat.le_ceil (twoLevelRepetitionCoefficient c*Real.log (m:ℝ)))
  apply hcore.trans
  unfold twoLevelRuntimeFinalCoreCharge
  simp only [two_mul,Nat.add_assoc]
  gcongr

theorem twoLevelRuntimeFinalCore_eventually (c : ℝ) (hc : 0 ≤ c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (N r : ℕ) (I : TwoLevelProblem N m r), (m:ℝ)^(-c) ≤ I.delta →
      (N:ℝ) ≤ (m:ℝ)^((59/50:ℝ)+τ) → ∀ g : MainRandomTape I.fixed,
      let S := (mainSketchProgram I.fixed g).eval
      let C := (coarseSupportProgram (twoLevelRuntimeFinalKernels m) S.initialA S.initialB).eval
      (twoLevelFactorCoreWorkCap (twoLevelRuntimeFinalKernels m) I.fixed S C
        (fun hr => mainFlexibleQueryWorkCap (twoLevelRuntimeFinalKernels m)
          (rangeDeflationWorkCap (twoLevelRuntimeFinalKernels m)) I.fixed S C hr
            twoLevelRuntimeFinalKernelConstant twoLevelRuntimeGlobalExponent):ℝ) ≤ (m:ℝ)^(3362/1425:ℝ) := by
  obtain ⟨τ,hτ,hcore⟩ := twoLevelRuntimeFinalCoreCharge_bound_eventually c hc
  refine ⟨τ,hτ,?_⟩
  filter_upwards [hcore,twoLevelRuntimeFinalCoreCharge_eventually c twoLevelRuntimeFinalKernelConstant
    hc twoLevelRuntimeFinalKernelConstant_pos] with m hm hcharge N r I hδ hN g
  exact (Nat.cast_le.mpr (hm N r I hδ hN g _)).trans hcharge

#print axioms twoLevelRuntimeFinalCore_eventually

end
end HierarchicalAbsoluteSpectral
