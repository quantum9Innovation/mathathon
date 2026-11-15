import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalKernels
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalLogs
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelSketches
import HierarchicalAbsoluteSpectral.BaseFixedFactorCost

/-! Actual true, fine, and refined factor-action bounds for the fixed
two-level kernel family. Symmetric product envelopes retain every tensor
orientation and charge the three input/output write volumes. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
variable {N m r : ℕ}

theorem rectangularKernelCost_real_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hK : ∀ i j k : ℕ, i ≤ a → j ≤ b → k ≤ c → ((K i j k).cost:ℝ) ≤ B) :
    (rectangularKernelCost K a b c:ℝ) ≤ B := by
  have hh : rectangularKernelCost K a b c ≤ ⌊B⌋₊ := by
    apply Finset.sup_le
    intro i _
    apply Finset.sup_le
    intro j _
    apply Finset.sup_le
    intro k _
    exact Nat.le_floor (hK i.val j.val k.val (by omega) (by omega) (by omega))
  exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hB)

theorem positiveScaleneShape_permutation_bound (s t : PositiveScaleneShape)
    (ht : t ∈ s.permutations) :
    scaleneBound t.u t.v t.w = scaleneBound s.u s.v s.w := by
  simp only [PositiveScaleneShape.permutations,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with h | h | h | h | h | h <;> subst t
  · rfl
  · exact scaleneBound_swap.symm
  · exact scaleneBound_cyclic.symm
  · exact (scaleneBound_cyclic.trans scaleneBound_swap).symm
  · exact (scaleneBound_cyclic.trans scaleneBound_cyclic).symm
  · exact (scaleneBound_cyclic.trans (scaleneBound_cyclic.trans scaleneBound_swap)).symm

theorem twoLevelRuntime_true_permutations (t : PositiveScaleneShape)
    (ht : t ∈ twoLevelTrueShape.permutations) : t ∈ twoLevelRuntimeFinalShapes := by
  simp only [twoLevelRuntimeFinalShapes,List.mem_append]
  tauto

theorem twoLevelRuntime_fine_permutations (t : PositiveScaleneShape)
    (ht : t ∈ twoLevelFineShape.permutations) : t ∈ twoLevelRuntimeFinalShapes := by
  simp only [twoLevelRuntimeFinalShapes,List.mem_append]
  tauto

theorem symmetricKernelCost_scalene_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (s : PositiveScaleneShape)
    (δ ε : ℝ) (m a b c : ℕ)
    (hK : ∀ t ∈ s.permutations, ∀ i j k : ℕ, t.Fits δ m i j k →
      ((K i j k).cost:ℝ) ≤ (m:ℝ)^(scaleneBound t.u t.v t.w+ε))
    (hfit : s.Fits δ m a b c) :
    (symmetricKernelCost K a b c:ℝ) ≤ (m:ℝ)^(scaleneBound s.u s.v s.w+ε) := by
  have hrect (t : PositiveScaleneShape) (ht : t ∈ s.permutations)
      (A B C : ℕ) (hfit : t.Fits δ m A B C) :
      (rectangularKernelCost K A B C:ℝ) ≤ (m:ℝ)^(scaleneBound s.u s.v s.w+ε) := by
    apply rectangularKernelCost_real_bound K A B C _ (by positivity)
    intro i j k hi hj hk
    have hh := hK t ht i j k
      ⟨hi.trans hfit.1,hj.trans hfit.2.1,hk.trans hfit.2.2⟩
    rwa [positiveScaleneShape_permutation_bound s t ht] at hh
  have h1 := hrect s (by simp [PositiveScaleneShape.permutations]) a b c hfit
  have h2 := hrect s.swap (by simp [PositiveScaleneShape.permutations]) a c b
    ⟨hfit.1,hfit.2.2,hfit.2.1⟩
  have h3 := hrect s.cyclic.swap (by simp [PositiveScaleneShape.permutations]) b a c
    ⟨hfit.2.1,hfit.1,hfit.2.2⟩
  have h4 := hrect s.cyclic (by simp [PositiveScaleneShape.permutations]) b c a
    ⟨hfit.2.1,hfit.2.2,hfit.1⟩
  have h5 := hrect s.cyclic.cyclic (by simp [PositiveScaleneShape.permutations]) c a b
    ⟨hfit.2.2,hfit.1,hfit.2.1⟩
  have h6 := hrect s.cyclic.cyclic.swap (by simp [PositiveScaleneShape.permutations]) c b a
    ⟨hfit.2.2,hfit.2.1,hfit.1⟩
  simp only [symmetricKernelCost,Nat.cast_max]
  exact max_le h1 (max_le h2 (max_le h3 (max_le h4 (max_le h5 h6))))

/-- The symmetric supremum of actual gate counts and all three write
volumes fit into the same scalene exponent with arbitrary positive slack. -/
theorem twoLevelRuntime_product_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ s : PositiveScaleneShape,
      (∀ t ∈ s.permutations, t ∈ twoLevelRuntimeFinalShapes) →
      s.u+s.v ≤ scaleneBound s.u s.v s.w →
      s.v+s.w ≤ scaleneBound s.u s.v s.w →
      s.w+s.u ≤ scaleneBound s.u s.v s.w →
      ∀ a b c : ℕ,
      (a:ℝ) ≤ (m:ℝ)^(s.u+δ) → (b:ℝ) ≤ (m:ℝ)^(s.v+δ) →
      (c:ℝ) ≤ (m:ℝ)^(s.w+δ) →
      (matrixProductCost (twoLevelRuntimeFinalKernels m) a b c:ℝ) ≤
        (m:ℝ)^(scaleneBound s.u s.v s.w+ε) := by
  obtain ⟨τ,hτ,hcap⟩ := twoLevelRuntimeFinalKernels_scalene (ε/2) (by positivity)
  let δ := min τ (ε/4)
  have hδ : 0 < δ := lt_min hτ (by positivity)
  have hδτ : δ ≤ τ := min_le_left _ _
  have hδε : δ ≤ ε/4 := min_le_right _ _
  have ht : Tendsto (fun m : ℕ => (m:ℝ)^(ε/2)) atTop atTop :=
    (tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp tendsto_natCast_atTop_atTop
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcap,eventually_ge_atTop (1:ℕ),ht.eventually (eventually_ge_atTop (5:ℝ))]
    with m hcap hm hlarge
  intro s hper huv hvw hwu a b c ha hb hc
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hfit : s.Fits δ m a b c := by
    exact ⟨by exact_mod_cast ha.trans (Nat.le_ceil _),
      by exact_mod_cast hb.trans (Nat.le_ceil _),by exact_mod_cast hc.trans (Nat.le_ceil _)⟩
  have hs := symmetricKernelCost_scalene_bound (twoLevelRuntimeFinalKernels m) s τ (ε/2) m a b c
    (fun t ht i j k hfit => hcap t (hper t ht) i j k hfit) (s.fits_mono hδτ hm hfit)
  have hpair (x y : ℕ) (X Y : ℝ) (hx : (x:ℝ) ≤ (m:ℝ)^(X+δ))
      (hy : (y:ℝ) ≤ (m:ℝ)^(Y+δ)) (hXY : X+Y ≤ scaleneBound s.u s.v s.w) :
      (x:ℝ)*y ≤ (m:ℝ)^(scaleneBound s.u s.v s.w+ε/2) := by
    calc
      _ ≤ (m:ℝ)^(X+δ)*(m:ℝ)^(Y+δ) := by gcongr
      _ = (m:ℝ)^((X+δ)+(Y+δ)) := (Real.rpow_add hm0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hmR (by linarith)
  have hab := hpair a b s.u s.v ha hb huv
  have hbc := hpair b c s.v s.w hb hc hvw
  have hca := hpair c a s.w s.u hc ha hwu
  have hF := scaleneBound_nonneg s.u_pos.le s.v_pos.le s.w_pos.le
  have hone : 1 ≤ (m:ℝ)^(scaleneBound s.u s.v s.w+ε/2) := Real.one_le_rpow hmR (by linarith)
  have hprod : (matrixProductCost (twoLevelRuntimeFinalKernels m) a b c:ℝ) ≤
      5*(m:ℝ)^(scaleneBound s.u s.v s.w+ε/2) := by
    unfold matrixProductCost
    push_cast
    linarith
  calc
    _ ≤ 5*(m:ℝ)^(scaleneBound s.u s.v s.w+ε/2) := hprod
    _ ≤ (m:ℝ)^(ε/2)*(m:ℝ)^(scaleneBound s.u s.v s.w+ε/2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hm0]; congr 1; ring

theorem twoLevelRuntime_fine_rows_eventually (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → ∀ g : MainRandomTape I.fixed,
      (((mainSketchProgram I.fixed g).eval.levelA (safeSketchIndex 1 (0+1))).1:ℝ) ≤
          (m:ℝ)^((7/6:ℝ)+ε) ∧
      (((mainSketchProgram I.fixed g).eval.levelB (safeSketchIndex 1 (0+1))).1:ℝ) ≤
          (m:ℝ)^((7/6:ℝ)+ε) := by
  filter_upwards [twoLevel_sketch_row_exponents c ε hc hε] with m hm N r I hδ g
  have hrows := (hm N r I hδ (2^dyadicPaddingLevel N)).2
  constructor
  · rw [mainSketchProgram_rowsA]
    simp only [safeSketchIndex,Nat.zero_add,Nat.min_self,TwoLevelProblem.fixed_accuracy,
      twoLevelAccuracy,one_ne_zero,ite_false]
    exact (Nat.cast_le.mpr (min_le_right _ _)).trans hrows
  · rw [mainSketchProgram_rowsB]
    simp only [safeSketchIndex,Nat.zero_add,Nat.min_self,TwoLevelProblem.fixed_accuracy,
      twoLevelAccuracy,one_ne_zero,ite_false]
    exact (Nat.cast_le.mpr (min_le_right _ _)).trans hrows

theorem twoLevelRuntime_actions_eventually (c η : ℝ) (hc : 0 ≤ c) (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (N r : ℕ) (I : TwoLevelProblem N m r), (m:ℝ)^(-c) ≤ I.delta →
      (N:ℝ) ≤ (m:ℝ)^((59/50:ℝ)+τ) → ∀ g : MainRandomTape I.fixed,
      ∀ C : MainSupportData (mainSketchProgram I.fixed g).eval, ∀ b : ℕ, b ≤ r+1 →
      (mainTrueActionCost (twoLevelRuntimeFinalKernels m) I.fixed (mainSketchProgram I.fixed g).eval C b:ℝ) ≤
        (m:ℝ)^((9006001/4130000:ℝ)+η) ∧
      (mainFineActionCost (twoLevelRuntimeFinalKernels m) I.fixed (mainSketchProgram I.fixed g).eval C 0 b:ℝ) ≤
        (m:ℝ)^((867/400:ℝ)+η) ∧
      (mainFactorActionCost (twoLevelRuntimeFinalKernels m) I.fixed (mainSketchProgram I.fixed g).eval C b 1:ℝ) ≤
        (m:ℝ)^((867/400:ℝ)+1/75+η) := by
  obtain ⟨τ,hτ,hprod⟩ := twoLevelRuntime_product_eventually (η/4) (by positivity)
  have hcast : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hrank := hcast.eventually (family_core_polylog_absorbed 3 0 ((14/25:ℝ)+τ) (14/25)
    (by norm_num) (by linarith))
  have htrue := hcast.eventually (family_core_polylog_absorbed 12640 1
    ((9006001/4130000:ℝ)+η) ((9006001/4130000:ℝ)+η/4) (by norm_num) (by linarith))
  have hfine := hcast.eventually (family_core_polylog_absorbed 3360 1
    ((867/400:ℝ)+η) ((867/400:ℝ)+η/4) (by norm_num) (by linarith))
  have hfactor := hcast.eventually (family_core_polylog_absorbed (10^20) 3
    ((867/400:ℝ)+1/75+η) ((867/400:ℝ)+1/75+η/4) (by norm_num) (by linarith))
  refine ⟨τ,hτ,?_⟩
  filter_upwards [hprod,twoLevelRuntime_fine_rows_eventually c τ hc hτ,hrank,htrue,hfine,hfactor,
    eventually_ge_atTop (2:ℕ),hcast.eventually (eventually_ge_atTop (Real.exp 1))]
    with m hprod hrows hrank htrue hfine hfactor hm hmexp N r I hδ hN g C b hb
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hm0 : (0:ℝ) < m := by linarith
  have hlog : 1 ≤ Real.log (m:ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hmexp
    rwa [Real.log_exp] at hh
  have hmb : (m:ℝ) ≤ (m:ℝ)^((1:ℝ)+τ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 (show (1:ℝ) ≤ 1+τ by linarith)
  have hrankwidth := twoLevel_rounded_rank_width m r I.core_positive I.rank_le_power
  have hbR : (b:ℝ) ≤ (m:ℝ)^((14/25:ℝ)+τ) := by
    have hb0 : (b:ℝ) ≤ (r+1:ℝ) := by exact_mod_cast hb
    exact hb0.trans (hrankwidth.trans (by simpa only [Real.rpow_zero,mul_one] using hrank))
  have hT := hprod twoLevelTrueShape twoLevelRuntime_true_permutations
    (by rw [twoLevelTrueShape_bound]; norm_num [twoLevelTrueShape])
    (by rw [twoLevelTrueShape_bound]; norm_num [twoLevelTrueShape])
    (by rw [twoLevelTrueShape_bound]; norm_num [twoLevelTrueShape]) N m b hN hmb hbR
  rw [twoLevelTrueShape_bound] at hT
  have hrows0 := hrows N r I hδ g
  let S := (mainSketchProgram I.fixed g).eval
  have hFA := hprod twoLevelFineShape twoLevelRuntime_fine_permutations
    (by rw [twoLevelFineShape_bound]; norm_num [twoLevelFineShape])
    (by rw [twoLevelFineShape_bound]; norm_num [twoLevelFineShape])
    (by rw [twoLevelFineShape_bound]; norm_num [twoLevelFineShape])
    (S.levelA (safeSketchIndex 1 (0+1))).1 m b hrows0.1 hmb hbR
  have hFB := hprod twoLevelFineShape twoLevelRuntime_fine_permutations
    (by rw [twoLevelFineShape_bound]; norm_num [twoLevelFineShape])
    (by rw [twoLevelFineShape_bound]; norm_num [twoLevelFineShape])
    (by rw [twoLevelFineShape_bound]; norm_num [twoLevelFineShape])
    (S.levelB (safeSketchIndex 1 (0+1))).1 m b hrows0.2 hmb hbR
  rw [twoLevelFineShape_bound] at hFA hFB
  have hFineProd : (mainFineProductCost (twoLevelRuntimeFinalKernels m) S 0 b:ℝ) ≤
      2*(m:ℝ)^((867/400:ℝ)+η/4) := by
    unfold mainFineProductCost
    push_cast
    linarith
  have hTrueProd : (mainInputProductCost (twoLevelRuntimeFinalKernels m) N m N b:ℝ) ≤
      2*(m:ℝ)^((9006001/4130000:ℝ)+η/4) := by
    unfold mainInputProductCost
    push_cast
    linarith
  have hTrueCost := mainTrueActionCost_product_bound (twoLevelRuntimeFinalKernels m) I.fixed S C b
  have hFineCost := mainActualFineActionCost_product_bound (twoLevelRuntimeFinalKernels m) I.fixed g C 0 b
  have hTrueLog := I.runtime_true_neumann_log hmR
  have hFineLog := I.runtime_fine_neumann_log hmR
  have hTrueBound : (mainTrueActionCost (twoLevelRuntimeFinalKernels m) I.fixed S C b:ℝ) ≤
      12640*(m:ℝ)^((9006001/4130000:ℝ)+η/4)*Real.log m := by
    calc
      _ ≤ 40*(1+4*Real.log (1/I.fixed.massAccuracy))*mainInputProductCost (twoLevelRuntimeFinalKernels m) N m N b := hTrueCost
      _ ≤ 40*(158*Real.log m)*(2*(m:ℝ)^((9006001/4130000:ℝ)+η/4)) := by gcongr
      _ = _ := by ring
  have hFineBound : (mainFineActionCost (twoLevelRuntimeFinalKernels m) I.fixed S C 0 b:ℝ) ≤
      3360*(m:ℝ)^((867/400:ℝ)+η/4)*Real.log m := by
    calc
      _ ≤ 40*mainFineNeumannLog I.fixed 0*mainFineProductCost (twoLevelRuntimeFinalKernels m) S 0 b := hFineCost
      _ ≤ 40*(42*Real.log m)*(2*(m:ℝ)^((867/400:ℝ)+η/4)) := by gcongr
      _ = _ := by ring
  have hFineFullLog : fixedFineLog I.fixed ≤ 44*Real.log m := by
    simp only [fixedFineLog,Fin.sum_univ_one,Fin.val_zero]
    linarith
  have hFactorCost := mainActualFactorActionCost_fine_sum (twoLevelRuntimeFinalKernels m) I.fixed g C b
  simp only [pow_one,fixedFineProductSum,Finset.sum_range_one] at hFactorCost
  have hAcc0 := I.fixed.accuracy_positive 0 (by omega)
  have hAcc1 := I.fixed.accuracy_positive 1 le_rfl
  have hFactorBound : (mainFactorActionCost (twoLevelRuntimeFinalKernels m) I.fixed S C b 1:ℝ) ≤
      42*fixedFineLog I.fixed*fixedRefinementCostMultiplier I.fixed*
        (I.fixed.accuracy 0/I.fixed.accuracy 1)*mainFineProductCost (twoLevelRuntimeFinalKernels m) S 0 b := by
    apply le_of_mul_le_mul_left _ hAcc1
    calc
      _ ≤ 42*fixedFineLog I.fixed*fixedRefinementCostMultiplier I.fixed*
          (I.fixed.accuracy 0*mainFineProductCost (twoLevelRuntimeFinalKernels m) S 0 b) := hFactorCost
      _ = _ := by field_simp [hAcc1.ne'] <;> ring
  have hFixedFineNonneg : 0 ≤ fixedFineLog I.fixed := (by norm_num : (0:ℝ) ≤ 1).trans (fixedFineLog_ge_one _)
  have hMultNonneg : 0 ≤ fixedRefinementCostMultiplier I.fixed :=
    (by norm_num : (0:ℝ) ≤ 1).trans (fixedRefinementCostMultiplier_ge_one _)
  have hRatioNonneg : 0 ≤ I.fixed.accuracy 0/I.fixed.accuracy 1 := div_nonneg hAcc0.le hAcc1.le
  have hRefineBound := I.runtime_refinement_multiplier hmR
  have hInverseBound := I.runtime_inverse_accuracy_ratio
  have hFactorPolylog : (mainFactorActionCost (twoLevelRuntimeFinalKernels m) I.fixed S C b 1:ℝ) ≤
      (10^20)*(m:ℝ)^((867/400:ℝ)+1/75+η/4)*(Real.log m)^3 := by
    calc
      _ ≤ 42*(44*Real.log m)*(204800000000000*(Real.log m)^2)*
          (4*(m:ℝ)^(1/75:ℝ))*(2*(m:ℝ)^((867/400:ℝ)+η/4)) := by
        apply hFactorBound.trans
        gcongr
      _ = (42*44*204800000000000*4*2)*(m:ℝ)^((867/400:ℝ)+1/75+η/4)*(Real.log m)^3 := by
        have he : (m:ℝ)^((867/400:ℝ)+1/75+η/4) =
            (m:ℝ)^(1/75:ℝ)*(m:ℝ)^((867/400:ℝ)+η/4) := by
          rw [← Real.rpow_add hm0]; congr 1; ring
        rw [he]
        ring
      _ ≤ _ := by gcongr <;> norm_num
  refine ⟨hTrueBound.trans ?_,hFineBound.trans ?_,hFactorPolylog.trans ?_⟩
  · simpa only [Real.rpow_one] using htrue
  · simpa only [Real.rpow_one] using hfine
  · simpa only [Real.rpow_ofNat] using hfactor

#print axioms twoLevelRuntime_actions_eventually

end
end HierarchicalAbsoluteSpectral
