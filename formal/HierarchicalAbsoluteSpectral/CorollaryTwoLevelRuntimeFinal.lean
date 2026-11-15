import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalCore
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalAssembly
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelUniformExponents
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelExpansionCost
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRoundedAsymptotics

/-! Unconditional asymptotic runtime of the actual two-level programs.
All four stage bounds are discharged by the fixed coefficient kernel family,
the rounded schedule, and the literal finite work counters. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology

theorem twoLevelRuntimeFinalConstruction_bound (c : ℝ) (hc : 0 ≤ c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
        (m:ℝ)^(-c) ≤ I.delta → (N:ℝ) ≤ (m:ℝ)^((59/50:ℝ)+τ) →
        ∀ g : MainRandomTape I.fixed,
        (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels m) I g:ℝ) ≤
          (m:ℝ)^((3362/1425:ℝ)+ε) := by
  obtain ⟨τ,hτ,hcore⟩ := twoLevelRuntimeFinalCore_eventually c hc
  let σ : ℝ := min τ (1/100)
  have hσ : 0 < σ := lt_min hτ (by norm_num)
  refine ⟨σ,hσ,?_⟩
  intro ε hε
  have hfour := core_polylog_absorbed 4 0 ((3362/1425:ℝ)+ε)
    ((3362/1425:ℝ)+ε/2) (by norm_num) (by linarith)
  filter_upwards [hcore,
    twoLevelRuntimeRestWorkCap_power_eventually c (119/100) (1/100) hc (by norm_num) (by norm_num),
    twoLevelInitialSketchWorkCap_power_eventually c (119/100) (1/100) hc (by norm_num) (by norm_num),
    twoLevelCoarseSupportWorkCap_eventually c (ε/2) hc (by positivity),hfour,
    eventually_ge_atTop (1:ℕ)] with m hcore hrest hsketch hsupport hfour hm N r I hδ hN g
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hNτ : (N:ℝ) ≤ (m:ℝ)^((59/50:ℝ)+τ) := hN.trans
    (Real.rpow_le_rpow_of_exponent_le hmR (by have := min_le_left τ (1/100:ℝ); dsimp [σ] at hN ⊢; linarith))
  have hNpower : (N:ℝ) ≤ (m:ℝ)^(119/100:ℝ) := hN.trans
    (Real.rpow_le_rpow_of_exponent_le hmR (by have := min_le_right τ (1/100:ℝ); dsimp [σ]; linarith))
  have hc0 := hcore N r I hδ hNτ g
  change (twoLevelRuntimeActualCoreWorkCap twoLevelRuntimeFinalKernelConstant I g:ℝ) ≤ _ at hc0
  have hr0 := hrest N r I hδ hNpower
  have hs0 := hsketch N r I hδ hNpower
  have hp0 := hsupport N r I hδ g
  change (twoLevelRuntimeActualSupportWorkCap I g:ℝ) ≤ _ at hp0
  have hreadExp : (1+(119/100:ℝ)+1/100) ≤ (3362/1425:ℝ)+ε/2 := by norm_num; linarith
  have hreadPow := Real.rpow_le_rpow_of_exponent_le hmR hreadExp
  have hcorePow := Real.rpow_le_rpow_of_exponent_le hmR
    (show (3362/1425:ℝ) ≤ (3362/1425:ℝ)+ε/2 by linarith)
  have hfinite := twoLevelRuntimeFinalConstruction_decompose twoLevelRuntimeFinalKernelConstant
    twoLevelRuntimeFinalKernelConstant_pos (twoLevelRuntimeFinalKernels_bound m) I g
  have hfiniteR :
      (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels m) I g:ℝ) ≤
        (twoLevelRuntimeRestWorkCap I+twoLevelInitialSketchWorkCap N m I.fixed.sketchFailure+
          twoLevelRuntimeActualSupportWorkCap I g+
          twoLevelRuntimeActualCoreWorkCap twoLevelRuntimeFinalKernelConstant I g:ℕ) := by
    exact_mod_cast hfinite
  push_cast at hfiniteR
  have hfour' : 4*(m:ℝ)^((3362/1425:ℝ)+ε/2) ≤ (m:ℝ)^((3362/1425:ℝ)+ε) := by
    simpa only [Real.rpow_zero,mul_one] using hfour
  exact (hfiniteR.trans (by linarith only [hc0,hr0,hs0,hp0,hreadPow,hcorePow])).trans hfour'

/-- The actual factor construction is subquadratic in the ambient dimension,
uniformly over every original input and every random tape outcome. -/
theorem twoLevelRuntimeFinalConstruction_family {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, TwoLevelProblem (N i) (m i) (r i))
    (c : ℝ) (hc : 0 ≤ c) (hm : Tendsto m l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^((6724/3363:ℝ)+ε) := by
  obtain ⟨τ,hτ,hconstruction⟩ := twoLevelRuntimeFinalConstruction_bound c hc
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hm
  have hN : ∀ᶠ i in l, (0:ℝ) < N i := Eventually.of_forall (fun i => by
    have hpos : 0 < N i := lt_of_lt_of_le (show 0 < m i from (I i).core_positive) (I i).core_le_side
    exact_mod_cast hpos)
  have hg : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+(9/50:ℝ))) := by
    convert hgrowth using 1 <;> norm_num
  have hdim := family_sequence_dimension_powers l (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    (9/50) τ hτ hmR hN hg
  apply twoLevel_exponent_transfer_uniform (α := fun i => MainRandomTape (I i).fixed) l
    (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    (fun i g => (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ))
    (3362/1425) (6724/3363) (by norm_num) (by norm_num) hmR hN hgrowth
  intro η hη
  filter_upwards [hm.eventually (hconstruction η hη),hdim,hδ] with i hcost hi hδi g
  exact hcost (N i) (r i) (I i) hδi (by convert hi.2 using 1 <;> norm_num) g

/-- Materializing the dense product adds the actual expansion circuit and
all output writes, giving exponent two in the ambient dimension. -/
theorem twoLevelRuntimeFinalFull_family {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, TwoLevelProblem (N i) (m i) (r i))
    (c : ℝ) (hc : 0 ≤ c) (hm : Tendsto m l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      (twoLevelFullExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^((2:ℝ)+ε) :=
  twoLevel_full_cost_of_construction_bound l m N r I hm hgrowth
    (twoLevelRuntimeFinalConstruction_family l m N r I c hc hm hgrowth hδ)

theorem twoLevelRuntimeFinalCosts {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, TwoLevelProblem (N i) (m i) (r i))
    (c : ℝ) (hc : 0 ≤ c) (hm : Tendsto m l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^((6724/3363:ℝ)+ε)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      (twoLevelFullExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^((2:ℝ)+ε)) :=
  ⟨twoLevelRuntimeFinalConstruction_family l m N r I c hc hm hgrowth hδ,
    twoLevelRuntimeFinalFull_family l m N r I c hc hm hgrowth hδ⟩

theorem twoLevelRuntimeFinalConstantConfidence {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, TwoLevelProblem (N i) (m i) (r i))
    (δ : ℝ) (hδ : 0 < δ) (hconfidence : ∀ i, (I i).delta = δ)
    (hm : Tendsto m l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ))) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^((6724/3363:ℝ)+ε)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      (twoLevelFullExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^((2:ℝ)+ε)) := by
  apply twoLevelRuntimeFinalCosts l m N r I 1 (by norm_num) hm hgrowth
  filter_upwards [twoLevel_constant_confidence_family l m hm δ hδ] with i hi
  simpa only [hconfidence i] using hi

#print axioms twoLevelRuntimeFinalConstruction_family
#print axioms twoLevelRuntimeFinalFull_family

end
end HierarchicalAbsoluteSpectral
