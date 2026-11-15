import HierarchicalAbsoluteSpectral.CorollaryOptimizedComparators
import HierarchicalAbsoluteSpectral.MainFamilyProgramFinal

/-! The optimized paper corollary. The hypotheses are the original matrix,
integer dimension, rank and confidence assumptions. All three algorithms
are literal counted arithmetic programs with verified kernel choices. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator

/-- `m=N^(alpha*+o(1))`, theta=`N^(-10s*+o(1))`, and ranks up to
sqrt(m) are handled by the same actual hierarchical algorithm in
`N^(2+o(1))` total work. Both actual comparator programs have total work
`N^(2+s*+o(1))`. No successful intermediate certificate is supplied. -/
theorem optimized_paper_corollary
    (c : ℝ) (hc : 0 < c) (m N r : ℕ → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (hm : Tendsto m atTop atTop)
    (hgrowth : Tendsto (fun i => Real.log (m i:ℝ)/Real.log (N i:ℝ)) atTop (𝓝 alphaStar))
    (hδ : ∀ᶠ i : ℕ in atTop, (m i:ℝ)^(-c) ≤ (I i).delta) :
    let H := growingFamilyKernelImplementation dStar optimized_parameter_in_family.1
    let K := optimizedComparatorImplementation
    (dStar=(3*Real.sqrt 5-5)/10 ∧ alphaStar=(3*Real.sqrt 5-5)/2 ∧
      savingStar=(7-3*Real.sqrt 5)/8 ∧ 0 < savingStar ∧ 0 < alphaStar) ∧
    (∀ d : ℝ, 0 ≤ d → min (krylovComparisonGap d) (gramComparisonGap d) ≤ savingStar) ∧
    Tendsto (fun i => Real.log (I i).theta/Real.log (N i:ℝ)) atTop (𝓝 (-10*savingStar)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop,
      ∀ q : ℕ, q ≤ ⌊Real.sqrt (m i:ℝ)⌋₊ → (q:ℝ) ≤ (N i:ℝ)^(alphaStar/2+ε)) ∧
    (∀ i (g : FamilyRandomTape (I i)),
      let program := growingDepthProgram (H.kernels (N i) (m i) (I i).core_positive) (I i) g
      program.admissible ∧ program.eval.width ≤ r i ∧ program.eval.product.rank ≤ r i ∧
        program.eval.product=program.eval.left*program.eval.right) ∧
    (∀ i, (familyRandomLaw (I i)).real {g : FamilyRandomTape (I i) |
      ‖(I i).A*(I i).B-(growingDepthProgram (H.kernels (N i) (m i) (I i).core_positive) (I i) g).eval.product‖ ≤
        (1+(I i).theta)*tailSingularValue ((I i).A*(I i).B) (r i)} ≥ 1-(I i).delta) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop, ∀ g : FamilyRandomTape (I i),
      (growingDepthExplicitWork (H.kernels (N i) (m i) (I i).core_positive) (I i) g:ℝ) ≤
        (N i:ℝ)^(2+ε)) ∧
    (∀ i (g : ComparatorFamilyRandomTape (I i)),
      let ordinary := optimizedKrylovComparator (K.kernels (N i) (m i)) (I i) g
      let gram := optimizedGramComparator (K.kernels (N i) (m i)) (I i) g
      ordinary.admissible ∧ gram.admissible ∧
      ordinary.eval.width ≤ r i ∧ gram.eval.width ≤ r i ∧
      ordinary.eval.product.rank ≤ r i ∧ gram.eval.product.rank ≤ r i ∧
      ordinary.eval.product=ordinary.eval.left*ordinary.eval.right ∧
      gram.eval.product=gram.eval.left*gram.eval.right) ∧
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
  intro H K
  have hmR : Tendsto (fun i => (m i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hgrowth' := (optimized_dimension_growth_iff atTop
    (fun i => (m i:ℝ)) (fun i => (N i:ℝ))).mp hgrowth
  have hN : ∀ᶠ i : ℕ in atTop, 0 < N i := Eventually.of_forall (fun i => (I i).side_positive)
  have hf := growingDepthProgram_family_theorem dStar c
    optimized_parameter_in_family.1 optimized_parameter_in_family.2 hc
    atTop m N r I hmR hgrowth' hδ
  have hcomp := optimizedComparatorPrograms_family_theorem c hc m N r I hm hgrowth' hδ
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨rfl,rfl,rfl,optimized_total_comparison.2.2.2.1,optimized_total_comparison.2.2.2.2.1⟩
  · exact optimized_comparison_saving_maximal
  · exact optimized_accuracy_exponent atTop (fun i => (m i:ℝ)) (fun i => (N i:ℝ)) hmR
      (Eventually.of_forall (fun i => by exact_mod_cast (I i).core_le_side)) hgrowth'
  · exact optimized_integer_rank_range m N hm hN hgrowth'
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2.2.2.2
  · intro i g
    have ha := hcomp.1 i g
    exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,
      (optimizedKrylovComparator _ _ _).eval.rank_le,(optimizedGramComparator _ _ _).eval.rank_le,
      (optimizedKrylovComparator _ _ _).eval.product_eq,(optimizedGramComparator _ _ _).eval.product_eq⟩
  · exact hcomp.2.1
  · exact hcomp.2.2

end
end HierarchicalAbsoluteSpectral
