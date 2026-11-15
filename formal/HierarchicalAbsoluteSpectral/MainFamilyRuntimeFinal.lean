import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalBound
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalAsymptotics
import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedOutputKernelFamily

/-! The growing-depth runtime theorem for the literal prepared program.
The kernel implementation is chosen once, before the input sequence,
random tape, or positive asymptotic slack is supplied. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Matmul.RectangularPrograms
open scoped Topology

structure FamilyFinalKernelImplementation (ζ : ℝ) where
  kernels : ∀ N m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c
  overhead : ℕ → ℝ
  outputOverhead : ℕ → ℝ
  coreConstant : ℝ
  core_positive : 0 < coreConstant
  overhead_one : ∀ m, 1 ≤ overhead m
  output_overhead_one : ∀ N, 1 ≤ outputOverhead N
  overhead_subpolynomial : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, overhead m ≤ (m:ℝ)^ε
  output_overhead_subpolynomial : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, outputOverhead N ≤ (N:ℝ)^ε
  envelopes : ∀ N m : ℕ, ∀ hm : 0 < m, m ≤ N →
    FixedFamilyKernelEnvelopes ζ N m (kernels N m hm) (overhead m) (outputOverhead N) coreConstant

def familyFinalKernelImplementation (ζ : ℝ) (hζ : 0 < ζ) : FamilyFinalKernelImplementation ζ :=
  Classical.choice (by
    obtain ⟨K,χ,χOut,C,hC,hχ,hχOut,hχSub,hχOutSub,hEnv⟩ := exists_fixed_family_kernel ζ hζ
    exact ⟨⟨K,χ,χOut,C,hC,hχ,hχOut,hχSub,hχOutSub,hEnv⟩⟩)

theorem growingDepthProgram_sequence_log_bound {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (ζ d c : ℝ) (hζ : 0 < ζ) (hd : FamilyExponentAdmissible d) (hc : 0 < c)
    (hm : Tendsto (fun i => (m i:ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let K := familyFinalKernelImplementation ζ hζ
    ∃ Cdepth γ Ccore : ℝ, 0 ≤ Ccore ∧ ∀ᶠ i in l, ∀ g : FamilyRandomTape (I i),
      (growingDepthExplicitWork (K.kernels (N i) (m i) (I i).core_positive) (I i) g:ℝ) ≤
        (N i:ℝ)^2*max (K.overhead (m i)) (K.outputOverhead (N i))*
          Real.exp (Cdepth*(1+Real.log (Real.log (2*(m i:ℝ))))^2)+
        Ccore*(m i:ℝ)^(9/4+ζ)*(Real.log (m i:ℝ))^γ := by
  intro K
  obtain ⟨D,hD,hscale⟩ := familyProgram_sequence_scale l m N d hd.positive hm
    (Eventually.of_forall (fun i => (I i).side_positive)) hgrowth
  let Cmain := familyFinalMainCoefficient D c
  let Ccore := familyFinalCoreCoefficient D c K.coreConstant ζ
  let Cdepth := familyFactorLoglogConstant D+Real.log Cmain+12
  let γ : ℝ := 3*(9/4+ζ)+2
  have hconstants := family_final_constants_positive D c K.coreConstant ζ hD hc.le K.core_positive
  refine ⟨Cdepth,γ,Ccore,hconstants.2,?_⟩
  have hmLog := (Real.tendsto_log_atTop.comp hm).eventually (eventually_ge_atTop (1:ℝ))
  have hmTwo := hm.eventually (eventually_ge_atTop (2:ℝ))
  have hraw := family_final_prescribed_width l m N r I d hd hm hgrowth D c (by linarith) hc.le
  filter_upwards [hscale,hmLog,hmTwo,hraw,hδ,
    familyPreparationProgram_eventually_normal l m N r I d hd.positive hm hgrowth]
    with i hscalei hlogmi hmi hrawi hδi hnormal g
  have hL : (I i).prepared.scalars.schedule.depth ≠ 0 := by
    rw [familyPreparationProgram_scalars]
    exact hnormal.ne'
  have hactual := family_final_actual_work_log_bound (K.kernels (N i) (m i) (I i).core_positive)
    (I i) g ζ (K.overhead (m i)) (K.outputOverhead (N i))
      (max (K.overhead (m i)) (K.outputOverhead (N i))) K.coreConstant D c
    hζ (K.overhead_one _) (K.output_overhead_one _) (le_max_left _ _) (le_max_right _ _)
    K.core_positive (K.envelopes _ _ (I i).core_positive (I i).core_le_side) hD hc.le
    (by exact_mod_cast hmi) hlogmi hL hscalei.2 hδi hrawi
  have habs := family_final_polylog_depth_absorb (m i:ℝ) Cmain 12 (familyFactorLoglogConstant D)
    (by exact_mod_cast (I i).core_positive) hlogmi hconstants.1 (by norm_num)
  rw [show (Real.log (m i:ℝ))^(12:ℝ)=(Real.log (m i:ℝ))^(12:ℕ) from
    Real.rpow_natCast _ 12] at habs
  have hmain := mul_le_mul_of_nonneg_left habs
    (show 0 ≤ (N i:ℝ)^2*max (K.overhead (m i)) (K.outputOverhead (N i)) by
      have hh : 0 ≤ max (K.overhead (m i)) (K.outputOverhead (N i)) :=
        (show 0 ≤ K.overhead (m i) by linarith [K.overhead_one (m i)]).trans (le_max_left _ _)
      positivity)
  dsimp only [Cmain,Ccore,Cdepth,γ] at hactual hmain ⊢
  nlinarith only [hactual,hmain]

theorem growingDepthProgram_quadratic_runtime {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (ζ d c : ℝ) (hζ : 0 < ζ) (hd : FamilyExponentAdmissible d) (hc : 0 < c)
    (hζbudget : ζ < 2+2*d-9/4)
    (hm : Tendsto (fun i => (m i:ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let K := familyFinalKernelImplementation ζ hζ
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : FamilyRandomTape (I i),
      (growingDepthExplicitWork (K.kernels (N i) (m i) (I i).core_positive) (I i) g:ℝ) ≤
        (N i:ℝ)^(2+ε) := by
  intro K
  obtain ⟨Cdepth,γ,Ccore,hCcore,hcost⟩ :=
    growingDepthProgram_sequence_log_bound l m N r I ζ d c hζ hd hc hm hgrowth hδ
  let χ := fun i => max (K.overhead (m i)) (K.outputOverhead (N i))
  let profile := fun i => (N i:ℝ)^2*χ i*
    Real.exp (Cdepth*(1+Real.log (Real.log (2*(m i:ℝ))))^2)+
      Ccore*(m i:ℝ)^(9/4+ζ)*(Real.log (m i:ℝ))^γ
  have hχ := family_final_kernel_overhead_sequence l m N K.overhead K.outputOverhead d hd.positive
    hm (fun i => (I i).core_le_side) (fun i => (I i).side_positive) hgrowth
    K.overhead_subpolynomial K.output_overhead_subpolynomial
  have htop := family_sequence_top_cost l (fun i => (m i:ℝ)) (fun i => (N i:ℝ)) χ profile
    d ζ Cdepth γ Ccore hm hd.1 hζbudget hCcore
    (Eventually.of_forall (fun i => by exact_mod_cast (I i).side_positive)) hgrowth
    (Eventually.of_forall (fun i =>
      (show 0 ≤ K.overhead (m i) by linarith [K.overhead_one (m i)]).trans (le_max_left _ _)))
    hχ (Eventually.of_forall (fun _ => le_rfl))
  intro ε hε
  filter_upwards [hcost,htop ε hε] with i hi hprofile g
  exact (hi g).trans hprofile

def familyFinalKernelForExponent (d : ℝ) (hd : FamilyExponentAdmissible d) :
    FamilyFinalKernelImplementation ((2+2*d-9/4)/2) :=
  familyFinalKernelImplementation ((2+2*d-9/4)/2) (by linarith [hd.1])

/-- Literal manuscript interval and original input assumptions. Every
Gaussian sample and every explicit output entry is included in the cost. -/
theorem growingDepthProgram_paper_runtime {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (d c : ℝ) (hd : FamilyExponentAdmissible d) (hc : 0 < c)
    (hm : Tendsto (fun i => (m i:ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let K := familyFinalKernelForExponent d hd
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : FamilyRandomTape (I i),
      (growingDepthExplicitWork (K.kernels (N i) (m i) (I i).core_positive) (I i) g:ℝ) ≤
        (N i:ℝ)^(2+ε) := by
  have hζ : 0 < (2+2*d-9/4)/2 := by linarith [hd.1]
  have hbudget : (2+2*d-9/4)/2 < 2+2*d-9/4 := by linarith [hd.1]
  exact growingDepthProgram_quadratic_runtime l m N r I ((2+2*d-9/4)/2) d c hζ hd hc hbudget hm hgrowth hδ

end
end HierarchicalAbsoluteSpectral
