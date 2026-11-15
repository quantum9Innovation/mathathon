import HierarchicalAbsoluteSpectral.CorollaryOptimizedFamilyPrograms
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeWhole
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeAsymptotics
import HierarchicalAbsoluteSpectral.MainExplicitOutputCost

/-! Both comparator algorithms, with one fixed verified kernel choice,
on the original optimized integer-dimensional input families. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator
variable {N m r : ℕ}

structure OptimizedComparatorKernelImplementation (ζ : ℝ) where
  kernels : ∀ _N _m a b c : ℕ, ArithmeticKernel a b c
  overhead : ℕ → ℝ
  outputOverhead : ℕ → ℝ
  coreConstant : ℝ
  core_positive : 0 < coreConstant
  overhead_one : ∀ m, 1 ≤ overhead m
  output_overhead_one : ∀ N, 1 ≤ outputOverhead N
  overhead_subpolynomial : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, overhead m ≤ (m:ℝ)^ε
  output_overhead_subpolynomial : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, outputOverhead N ≤ (N:ℝ)^ε
  envelopes : ∀ N m : ℕ, 0 < m → m ≤ N →
    FixedFamilyKernelEnvelopes ζ N m (kernels N m) (overhead m) (outputOverhead N) coreConstant
  gram_sequence : ∀ (m N : ℕ → ℕ), Tendsto m atTop atTop →
    (∀ᶠ i : ℕ in atTop, 0 < N i) →
    Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) atTop (𝓝 (1+dStar)) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop,
      (comparatorGramShapeWorkCap (kernels (N i) (m i)) (m i) (N i):ℝ) ≤
        (N i:ℝ)^(2+savingStar+ε)

def optimizedComparatorKernelImplementation (ζ : ℝ) (hζ : 0 < ζ) :
    OptimizedComparatorKernelImplementation ζ := Classical.choice (by
  obtain ⟨K,χ,χOut,C,hC,hχ,hχOut,hχSub,hχOutSub,hEnv,hGram⟩ :=
    exists_optimized_comparator_kernel_family ζ hζ
  exact ⟨⟨K,χ,χOut,C,hC,hχ,hχOut,hχSub,hχOutSub,hEnv,hGram⟩⟩)

def optimizedComparatorSlack : ℝ := (2+2*dStar-9/4)/2

theorem optimizedComparatorSlack_positive : 0 < optimizedComparatorSlack := by
  unfold optimizedComparatorSlack
  linarith [optimized_parameter_in_family.1]

theorem optimizedComparatorSlack_budget : 9/4+optimizedComparatorSlack < 2+9*dStar/4 := by
  unfold optimizedComparatorSlack
  linarith [optimized_parameter_in_family.1]

def optimizedComparatorImplementation : OptimizedComparatorKernelImplementation optimizedComparatorSlack :=
  optimizedComparatorKernelImplementation optimizedComparatorSlack optimizedComparatorSlack_positive

def optimizedKrylovComparatorExplicitWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) : ℕ :=
  m*(N+N)+(optimizedKrylovComparator kernels I g).eval.entryCount+mainRandomizedWork (comparatorProblemForFamily I)
    (optimizedKrylovComparator kernels I g).work

def optimizedGramComparatorExplicitWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) : ℕ :=
  m*(N+N)+(optimizedGramComparator kernels I g).eval.entryCount+mainRandomizedWork (comparatorProblemForFamily I)
    (optimizedGramComparator kernels I g).work

theorem optimizedKrylovComparatorExplicitWork_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) :
    optimizedKrylovComparatorExplicitWork kernels I g ≤
      2*m*(N+N)+N*N+mainRandomizedWork (comparatorProblemForFamily I)
        (5+(constantDistortionComparatorProgram kernels (comparatorProblemForFamily I) g).work) := by
  have he := (optimizedKrylovComparator kernels I g).eval.entryCount_le I.rank_le_core
  unfold optimizedKrylovComparatorExplicitWork
  rw [optimizedKrylovComparator_work]
  nlinarith only [he]

theorem optimizedGramComparatorExplicitWork_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : ComparatorFamilyRandomTape I) :
    optimizedGramComparatorExplicitWork kernels I g ≤
      2*m*(N+N)+N*N+mainRandomizedWork (comparatorProblemForFamily I)
        (5+(exactGramComparatorProgram kernels (comparatorProblemForFamily I) g).work) := by
  have he := (optimizedGramComparator kernels I g).eval.entryCount_le I.rank_le_core
  unfold optimizedGramComparatorExplicitWork
  rw [optimizedGramComparator_work]
  nlinarith only [he]

theorem comparatorGramRowWorkCap_le_shape (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (m N : ℕ) :
    comparatorGramRowWorkCap K m N ≤ comparatorGramShapeWorkCap K m N := by
  unfold comparatorGramRowWorkCap
  apply Finset.sup_le
  intro s _
  exact comparatorGramShapeWorkCap_le K m N m s.val m le_rfl (by omega) le_rfl

theorem comparator_total_coefficients_nonneg (D c : ℝ) (hD : 1 ≤ D) (hc : 0 ≤ c) :
    0 ≤ comparatorTotalMainCoefficient D c ∧ 0 ≤ comparatorTotalSmallCoefficient D := by
  have hF := comparatorFactorConstant_ge_one
  have hA := comparatorAlphaRootConstant_ge_one
  have hcore : 0 ≤ comparatorCoreConstant := by unfold comparatorCoreConstant; positivity
  constructor
  · unfold comparatorTotalMainCoefficient
    apply add_nonneg _ (comparator_rest_coefficient_nonneg D c hc)
    unfold comparatorCoreNumericCoefficient comparatorOuterNumericCoefficient
      comparatorQueryCoefficient comparatorActionCoefficient
    positivity
  · unfold comparatorTotalSmallCoefficient comparatorSmallNumericCoefficient comparatorOuterNumericCoefficient
    positivity

theorem optimizedComparatorPrograms_sequence_numeric
    (m N r : ℕ → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (ζ c : ℝ) (K : OptimizedComparatorKernelImplementation ζ) (hζ : 0 < ζ) (hc : 0 ≤ c)
    (hm : Tendsto m atTop atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) atTop (𝓝 (1+dStar)))
    (hδ : ∀ᶠ i : ℕ in atTop, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let D := comparatorFamilyMagnitudeCoefficient c
    ∀ᶠ i : ℕ in atTop, ∀ g : ComparatorFamilyRandomTape (I i),
      let bound := 2*(comparatorGramRowWorkCap (K.kernels (N i) (m i)) (m i) (N i):ℝ)+
        optimizedComparatorAnalyticEnvelope (m i) (N i)
          (max (K.overhead (m i)) (K.outputOverhead (N i)))
          (comparatorTotalMainCoefficient D c) (comparatorTotalSmallCoefficient D*(K.coreConstant+1)) ζ
      (optimizedKrylovComparatorExplicitWork (K.kernels (N i) (m i)) (I i) g:ℝ) ≤ bound ∧
        (optimizedGramComparatorExplicitWork (K.kernels (N i) (m i)) (I i) g:ℝ) ≤ bound := by
  intro D
  have hD : 1 ≤ D := comparator_family_magnitude_coefficient_ge_one c hc
  have hmR : Tendsto (fun i => (m i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hN0 : ∀ᶠ i : ℕ in atTop, (0:ℝ) < N i :=
    Eventually.of_forall (fun i => by exact_mod_cast (I i).side_positive)
  have hdim := family_sequence_dimension_powers atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    dStar 1 (by norm_num) hmR hN0 hgrowth
  have hraw := comparator_raw_width_uniform m N hm (fun i => (I i).core_le_side) hgrowth c hc
  filter_upwards [hdim,hraw,hδ,hm.eventually (eventually_ge_atTop (2:ℕ)),
    (Real.tendsto_log_atTop.comp hmR).eventually (eventually_ge_atTop (1:ℝ))]
    with i hNi hrawi hδi hmi hlogmi g
  have hm0 : (0:ℝ) < m i := by exact_mod_cast (I i).core_positive
  have hm1 : (1:ℝ) ≤ m i := by exact_mod_cast (show 1 ≤ m i by omega)
  have hN3 : (N i:ℝ) ≤ (m i:ℝ)^3 := by
    apply hNi.2.trans
    have hd : dStar < 1 := by
      have hh := family_parameter_margins dStar optimized_parameter_in_family.1 optimized_parameter_in_family.2
      linarith [hh.2.1]
    have hh := Real.rpow_le_rpow_of_exponent_le hm1 (show 1+dStar+1 ≤ (3:ℝ) by linarith)
    simpa only [Real.rpow_ofNat] using hh
  have hside : Real.log (N i:ℝ) ≤ 3*Real.log (m i:ℝ) := by
    have hh := Real.log_le_log (by exact_mod_cast (I i).side_positive : (0:ℝ) < N i) hN3
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hconfidence : Real.log (1/(I i).delta) ≤ c*Real.log (m i:ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hm0 _) hδi
    rw [Real.log_rpow hm0] at hh
    rw [one_div,Real.log_inv]
    linarith
  let J := comparatorProblemForFamily (I i)
  have haccuracy : J.accuracy=comparatorAccuracy := rfl
  have htheta : J.theta=min (comparatorDimensionTheta (m i) (N i)) (1/1048576) := rfl
  have hmag := comparator_family_magnitude J haccuracy htheta c hmi hN3 hδi
  have hwidth := hrawi (r i) J haccuracy htheta hδi (I i).rank_le_sqrt
  have hEnv := K.envelopes (N i) (m i) (I i).core_positive (I i).core_le_side
  have hK := constantDistortionComparatorProgram_complete_numeric (K.kernels (N i) (m i)) ζ
    (K.overhead (m i)) (K.outputOverhead (N i)) K.coreConstant
    (max (K.overhead (m i)) (K.outputOverhead (N i))) D c (Real.log (m i:ℝ))
    hζ (K.overhead_one _) (K.output_overhead_one _) K.core_positive
    (le_max_left _ _) (le_max_right _ _) hD hc hlogmi hEnv J haccuracy htheta hmi
    (I i).rank_le_sqrt rfl hmag hconfidence hside hwidth g
  have hG := exactGramComparatorProgram_complete_numeric (K.kernels (N i) (m i)) ζ
    (K.overhead (m i)) (K.outputOverhead (N i)) K.coreConstant
    (max (K.overhead (m i)) (K.outputOverhead (N i))) D c (Real.log (m i:ℝ))
    hζ (K.overhead_one _) (K.output_overhead_one _) K.core_positive
    (le_max_left _ _) (le_max_right _ _) hD hc hlogmi hEnv J haccuracy htheta hmi
    (I i).rank_le_sqrt rfl hmag hconfidence hside hwidth g
  constructor
  · apply (Nat.cast_le.mpr (optimizedKrylovComparatorExplicitWork_le _ _ _)).trans
    simpa only [optimizedComparatorAnalyticEnvelope,add_assoc,mul_assoc,J] using hK
  · apply (Nat.cast_le.mpr (optimizedGramComparatorExplicitWork_le _ _ _)).trans
    simpa only [optimizedComparatorAnalyticEnvelope,add_assoc,mul_assoc,J] using hG

theorem optimizedComparatorPrograms_sequence_runtime
    (m N r : ℕ → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (ζ c : ℝ) (K : OptimizedComparatorKernelImplementation ζ) (hζ : 0 < ζ) (hc : 0 ≤ c)
    (hζbudget : 9/4+ζ < 2+9*dStar/4)
    (hm : Tendsto m atTop atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) atTop (𝓝 (1+dStar)))
    (hδ : ∀ᶠ i : ℕ in atTop, (m i:ℝ)^(-c) ≤ (I i).delta) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop, ∀ g : ComparatorFamilyRandomTape (I i),
      (optimizedKrylovComparatorExplicitWork (K.kernels (N i) (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^(2+savingStar+ε) ∧
      (optimizedGramComparatorExplicitWork (K.kernels (N i) (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^(2+savingStar+ε) := by
  let D := comparatorFamilyMagnitudeCoefficient c
  let X := fun i => max (K.overhead (m i)) (K.outputOverhead (N i))
  let G := fun i => (comparatorGramRowWorkCap (K.kernels (N i) (m i)) (m i) (N i):ℝ)
  have hD : 1 ≤ D := comparator_family_magnitude_coefficient_ge_one c hc
  have hcoeff := comparator_total_coefficients_nonneg D c hD hc
  have hNm : ∀ i, m i ≤ N i := fun i => (I i).core_le_side
  have hN : ∀ i, 0 < N i := fun i => (I i).side_positive
  have hX : ∀ i, 1 ≤ X i := fun i => (K.overhead_one _).trans (le_max_left _ _)
  have hXsub := family_final_kernel_overhead_sequence atTop m N K.overhead K.outputOverhead
    dStar (by linarith [optimized_parameter_in_family.1]) (tendsto_natCast_atTop_atTop.comp hm)
    hNm hN hgrowth K.overhead_subpolynomial K.output_overhead_subpolynomial
  have hG : ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop, G i ≤ (N i:ℝ)^(2+savingStar+ε) := by
    intro ε hε
    filter_upwards [K.gram_sequence m N hm (Eventually.of_forall hN) hgrowth ε hε] with i hi
    exact (Nat.cast_le.mpr (comparatorGramRowWorkCap_le_shape _ _ _)).trans hi
  have hbound := optimized_comparator_full_envelope_exponent m N X G hm hNm hgrowth hX hXsub hG
    (comparatorTotalMainCoefficient D c) (comparatorTotalSmallCoefficient D*(K.coreConstant+1)) ζ
    hcoeff.1 (mul_nonneg hcoeff.2 (by linarith [K.core_positive])) hζbudget
  intro ε hε
  filter_upwards [optimizedComparatorPrograms_sequence_numeric m N r I ζ c K hζ hc hm hgrowth hδ,
    hbound ε hε] with i hi hbi g
  exact ⟨(hi g).1.trans hbi,(hi g).2.trans hbi⟩

/-- The kernel implementation is chosen before the input sequence and
epsilon. Only original dimension, rank, confidence and matrix inputs occur. -/
theorem optimizedComparatorPrograms_family_theorem
    (c : ℝ) (hc : 0 < c) (m N r : ℕ → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (hm : Tendsto m atTop atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) atTop (𝓝 (1+dStar)))
    (hδ : ∀ᶠ i : ℕ in atTop, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let K := optimizedComparatorImplementation
    (∀ i (g : ComparatorFamilyRandomTape (I i)),
      (optimizedKrylovComparator (K.kernels (N i) (m i)) (I i) g).admissible ∧
      (optimizedGramComparator (K.kernels (N i) (m i)) (I i) g).admissible ∧
      (optimizedKrylovComparator (K.kernels (N i) (m i)) (I i) g).eval.width ≤ r i ∧
      (optimizedGramComparator (K.kernels (N i) (m i)) (I i) g).eval.width ≤ r i) ∧
    (∀ i, (comparatorFamilyLaw (I i)).real {g : ComparatorFamilyRandomTape (I i) |
      ‖(I i).A*(I i).B-(optimizedKrylovComparator (K.kernels (N i) (m i)) (I i) g).eval.product‖ ≤
        (1+(I i).theta)*tailSingularValue ((I i).A*(I i).B) (r i)} ≥ 1-(I i).delta ∧
      (comparatorFamilyLaw (I i)).real {g : ComparatorFamilyRandomTape (I i) |
      ‖(I i).A*(I i).B-(optimizedGramComparator (K.kernels (N i) (m i)) (I i) g).eval.product‖ ≤
        (1+(I i).theta)*tailSingularValue ((I i).A*(I i).B) (r i)} ≥ 1-(I i).delta) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop, ∀ g : ComparatorFamilyRandomTape (I i),
      (optimizedKrylovComparatorExplicitWork (K.kernels (N i) (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^(2+savingStar+ε) ∧
      (optimizedGramComparatorExplicitWork (K.kernels (N i) (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^(2+savingStar+ε)) := by
  intro K
  refine ⟨?_,?_,?_⟩
  · intro i g
    exact ⟨optimizedKrylovComparator_admissible _ _ _,optimizedGramComparator_admissible _ _ _,
      (optimizedKrylovComparator _ _ _).eval.width_le,(optimizedGramComparator _ _ _).eval.width_le⟩
  · intro i
    exact ⟨optimizedKrylovComparator_error_probability _ _,optimizedGramComparator_error_probability _ _⟩
  · exact optimizedComparatorPrograms_sequence_runtime m N r I optimizedComparatorSlack c K
      optimizedComparatorSlack_positive hc.le optimizedComparatorSlack_budget hm hgrowth hδ

end
end HierarchicalAbsoluteSpectral
