import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamilyBound
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamilyWidth
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamilyCaps
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinal

/-! The absolute corollary on the manuscript's integer dimension families.
One verified kernel implementation is fixed before the input sequence or
asymptotic slack, and the very same measurable event gives all guarantees. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option pp.proofs false
noncomputable section
open Filter Matrix MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
variable {N m : ℕ}

/-- This event depends only on the original input and the fixed kernel
implementation. In particular it is independent of the asymptotic slack. -/
def absoluteFamilySuccessEvent
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) : Set (AbsoluteFamilyTape I) :=
  Classical.choose (absolute_fixed_threshold_all_ranks_good_event kernels I.fixed)

theorem absoluteFamilySuccessEvent_spec
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) :
    MeasurableSet (absoluteFamilySuccessEvent kernels I) ∧
      (absoluteFamilyRandomLaw I).real (absoluteFamilySuccessEvent kernels I) ≥ 1-I.delta ∧
      ∀ g ∈ absoluteFamilySuccessEvent kernels I,
        let S := (mainSketchProgram I.fixed.seed g.1).eval
        let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
        MainSketchGood I.fixed.seed S ∧ AbsoluteCoreThresholdGood kernels I.fixed S C g.2 :=
  Classical.choose_spec (absolute_fixed_threshold_all_ranks_good_event kernels I.fixed)

theorem absolute_family_correct_on_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I)
    (hsketch : MainSketchGood I.fixed.seed (mainSketchProgram I.fixed.seed g.1).eval)
    (hgood : let S := (mainSketchProgram I.fixed.seed g.1).eval
      let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
      AbsoluteCoreThresholdGood kernels I.fixed S C g.2) :
    let out := (absoluteFamilyProgram kernels I g).eval
    out.result.width ≤ 2*I.slackRank ∧ ‖I.A*I.B-out.result.product‖ ≤ I.tolerance := by
  have hc := absoluteCoreProgram_correct kernels I.fixed _ hsketch _ g.2 hgood
  rw [absoluteFamilyProgram_eval,absoluteAlgorithmProgram_eval]
  refine ⟨hc.1.trans (Nat.mul_le_mul_left 2 I.internal_slackRank_le),?_⟩
  have he := hc.2
  have hA : I.fixed.A=I.A := I.seed.prepared.input_left
  have hB : I.fixed.B=I.B := I.seed.prepared.input_right
  rw [hA,hB] at he
  exact he

theorem absoluteFamilyProgram_sequence_log_bound {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (I : ∀ i, AbsoluteFamilyProblem (N i) (m i))
    (ζ d c : ℝ) (hζ : 0 < ζ) (hd : FamilyExponentAdmissible d) (hc : 0 < c)
    (hm : Tendsto (fun i => (m i:ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let K := familyFinalKernelImplementation ζ hζ
    ∃ Cdepth γ Ccore : ℝ, 0 ≤ Ccore ∧ ∀ᶠ i in l,
      ∀ g ∈ absoluteFamilySuccessEvent (K.kernels (N i) (m i) (I i).core_positive) (I i),
          let out := (absoluteFamilyProgram (K.kernels (N i) (m i) (I i).core_positive) (I i) g).eval
          out.result.width ≤ 2*(I i).slackRank ∧ ‖(I i).A*(I i).B-out.result.product‖ ≤ (I i).tolerance ∧
            ((I i).slackRank ≤ Nat.sqrt (m i)/2 →
              (absoluteFamilyExplicitWork (K.kernels (N i) (m i) (I i).core_positive) (I i) g:ℝ) ≤
                (N i:ℝ)^2*max (K.overhead (m i)) (K.outputOverhead (N i))*
                  Real.exp (Cdepth*(1+Real.log (Real.log (2*(m i:ℝ))))^2)+
                Ccore*(m i:ℝ)^(9/4+ζ)*(Real.log (m i:ℝ))^γ) := by
  intro K
  obtain ⟨D,hD,hscale⟩ := familyProgram_sequence_scale l m N d hd.positive hm
    (Eventually.of_forall (fun i => (I i).seed.side_positive)) hgrowth
  let c' := c+2
  let Cmain := 4*familyFinalMainCoefficient D c'
  let Ccore := 4*familyFinalCoreCoefficient D c' K.coreConstant ζ
  let Cdepth := familyFactorLoglogConstant D+Real.log Cmain+13
  let γ : ℝ := 3*(9/4+ζ)+3
  have hconstants := family_final_constants_positive D c' K.coreConstant ζ hD (by dsimp [c']; linarith) K.core_positive
  have hCmain : 1 ≤ Cmain := by dsimp [Cmain]; linarith only [hconstants.1]
  have hCcore : 0 ≤ Ccore := mul_nonneg (by norm_num) hconstants.2
  refine ⟨Cdepth,γ,Ccore,hCcore,?_⟩
  have hmLog := (Real.tendsto_log_atTop.comp hm).eventually (eventually_ge_atTop (1:ℝ))
  have hmTwo := hm.eventually (eventually_ge_atTop (2:ℝ))
  have hraw := absolute_family_prescribed_width l m N I d hd hm hgrowth D c' (by linarith) (by dsimp [c']; linarith)
  have hnormal := familyPreparationProgram_eventually_normal l m N (fun _ => 1) (fun i => (I i).seed)
    d hd.positive hm hgrowth
  filter_upwards [hscale,hmLog,hmTwo,hraw,hδ,hnormal]
    with i hscalei hlogmi hmi hrawi hδi hnormali
  let kernels := K.kernels (N i) (m i) (I i).core_positive
  intro g hg
  obtain ⟨hsketch,hgood⟩ := (absoluteFamilySuccessEvent_spec kernels (I i)).2.2 g hg
  have hcorrect := absolute_family_correct_on_good_event kernels (I i) g hsketch hgood
  refine ⟨hcorrect.1,hcorrect.2,?_⟩
  intro hsmall
  have hL : (I i).seed.prepared.scalars.schedule.depth ≠ 0 := by
    rw [familyPreparationProgram_scalars]
    exact hnormali.ne'
  have hδseed : (m i:ℝ)^(-c') ≤ (I i).seed.delta :=
    (I i).seed_confidence_lower c (by exact_mod_cast hmi) hδi
  have hactual := absolute_family_actual_work_log_bound kernels (I i) g ζ
    (K.overhead (m i)) (K.outputOverhead (N i))
      (max (K.overhead (m i)) (K.outputOverhead (N i))) K.coreConstant D c'
    hζ (K.overhead_one _) (K.output_overhead_one _) (le_max_left _ _) (le_max_right _ _)
    K.core_positive (K.envelopes _ _ (I i).core_positive (I i).core_le_side) hD (by dsimp [c']; linarith)
    (by exact_mod_cast hmi) hlogmi hL hscalei.2 hδseed hrawi hsketch hsmall
  have habs := family_final_polylog_depth_absorb (m i:ℝ) Cmain 13 (familyFactorLoglogConstant D)
    (by exact_mod_cast (I i).core_positive) hlogmi hCmain (by norm_num)
  rw [show (Real.log (m i:ℝ))^(13:ℝ)=(Real.log (m i:ℝ))^(13:ℕ) from
    Real.rpow_natCast _ 13] at habs
  have hmain := mul_le_mul_of_nonneg_left habs
    (show 0 ≤ (N i:ℝ)^2*max (K.overhead (m i)) (K.outputOverhead (N i)) by
      have hh : 0 ≤ max (K.overhead (m i)) (K.outputOverhead (N i)) :=
        (show 0 ≤ K.overhead (m i) by linarith [K.overhead_one (m i)]).trans (le_max_left _ _)
      positivity)
  dsimp only [Cmain,Ccore,Cdepth,γ] at hactual hmain ⊢
  nlinarith only [hactual,hmain]

theorem absoluteFamilyProgram_quadratic_runtime {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (I : ∀ i, AbsoluteFamilyProblem (N i) (m i))
    (ζ d c : ℝ) (hζ : 0 < ζ) (hd : FamilyExponentAdmissible d) (hc : 0 < c)
    (hζbudget : ζ < 2+2*d-9/4)
    (hm : Tendsto (fun i => (m i:ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let K := familyFinalKernelImplementation ζ hζ
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
      ∀ g ∈ absoluteFamilySuccessEvent (K.kernels (N i) (m i) (I i).core_positive) (I i),
          let out := (absoluteFamilyProgram (K.kernels (N i) (m i) (I i).core_positive) (I i) g).eval
          out.result.width ≤ 2*(I i).slackRank ∧ ‖(I i).A*(I i).B-out.result.product‖ ≤ (I i).tolerance ∧
            ((I i).slackRank ≤ Nat.sqrt (m i)/2 →
              (absoluteFamilyExplicitWork (K.kernels (N i) (m i) (I i).core_positive) (I i) g:ℝ) ≤
                (N i:ℝ)^(2+ε)) := by
  intro K
  obtain ⟨Cdepth,γ,Ccore,hCcore,hcost⟩ :=
    absoluteFamilyProgram_sequence_log_bound l m N I ζ d c hζ hd hc hm hgrowth hδ
  let χ := fun i => max (K.overhead (m i)) (K.outputOverhead (N i))
  let profile := fun i => (N i:ℝ)^2*χ i*
    Real.exp (Cdepth*(1+Real.log (Real.log (2*(m i:ℝ))))^2)+
      Ccore*(m i:ℝ)^(9/4+ζ)*(Real.log (m i:ℝ))^γ
  have hχ := family_final_kernel_overhead_sequence l m N K.overhead K.outputOverhead d hd.positive
    hm (fun i => (I i).core_le_side) (fun i => (I i).seed.side_positive) hgrowth
    K.overhead_subpolynomial K.output_overhead_subpolynomial
  have htop := family_sequence_top_cost l (fun i => (m i:ℝ)) (fun i => (N i:ℝ)) χ profile
    d ζ Cdepth γ Ccore hm hd.1 hζbudget hCcore
    (Eventually.of_forall (fun i => by exact_mod_cast (I i).seed.side_positive)) hgrowth
    (Eventually.of_forall (fun i =>
      (show 0 ≤ K.overhead (m i) by linarith [K.overhead_one (m i)]).trans (le_max_left _ _)))
    hχ (Eventually.of_forall (fun _ => le_rfl))
  intro ε hε
  filter_upwards [hcost,htop ε hε] with i hi hprofile g hg
  obtain ⟨hw,he,ht⟩ := hi g hg
  exact ⟨hw,he,fun hs => (ht hs).trans hprofile⟩

/-- No supplied rank, the least slack rank includes zero, and the actual
arithmetic algorithm has absolute error, adaptive width and quadratic
family runtime together with probability at least 1-delta. -/
theorem absoluteFamilyProgram_paper_corollary {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (I : ∀ i, AbsoluteFamilyProblem (N i) (m i))
    (d c : ℝ) (hd : FamilyExponentAdmissible d) (hc : 0 < c)
    (hm : Tendsto (fun i => (m i:ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let K := familyFinalKernelForExponent d hd
    ∃ E : ∀ i, Set (AbsoluteFamilyTape (I i)),
      (∀ i, MeasurableSet (E i) ∧ (absoluteFamilyRandomLaw (I i)).real (E i) ≥ 1-(I i).delta ∧
        ∀ g ∈ E i,
          let out := (absoluteFamilyProgram (K.kernels (N i) (m i) (I i).core_positive) (I i) g).eval
          out.result.width ≤ 2*(I i).slackRank ∧ ‖(I i).A*(I i).B-out.result.product‖ ≤ (I i).tolerance) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g ∈ E i,
        (I i).slackRank ≤ Nat.sqrt (m i)/2 →
          (absoluteFamilyExplicitWork (K.kernels (N i) (m i) (I i).core_positive) (I i) g:ℝ) ≤
            (N i:ℝ)^(2+ε)) := by
  intro K
  let E := fun i => absoluteFamilySuccessEvent (K.kernels (N i) (m i) (I i).core_positive) (I i)
  refine ⟨E,?_,?_⟩
  · intro i
    have hs := absoluteFamilySuccessEvent_spec (K.kernels (N i) (m i) (I i).core_positive) (I i)
    refine ⟨hs.1,hs.2.1,?_⟩
    intro g hg
    obtain ⟨hsketch,hgood⟩ := hs.2.2 g hg
    exact absolute_family_correct_on_good_event (K.kernels (N i) (m i) (I i).core_positive)
      (I i) g hsketch hgood
  · have hζ : 0 < (2+2*d-9/4)/2 := by linarith [hd.1]
    have hbudget : (2+2*d-9/4)/2 < 2+2*d-9/4 := by linarith [hd.1]
    have hh := absoluteFamilyProgram_quadratic_runtime l m N I ((2+2*d-9/4)/2) d c
      hζ hd hc hbudget hm hgrowth hδ
    intro ε hε
    filter_upwards [hh ε hε] with i hi g hg
    exact (hi g hg).2.2


end
end HierarchicalAbsoluteSpectral
