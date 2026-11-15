import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinal
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRoundedAsymptotics
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelDegrees

/-! The two-level specialization of the actual prepared algorithm.
The hypotheses are the original matrix/rank/confidence inputs and
N=m^(59/50+o(1)); no success, action-cost, or algorithm certificate is assumed.
All eventual bounds use a single dimension threshold for every tape outcome. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open ArithmeticProgram hiding pure
open scoped Topology Matrix.Norms.L2Operator

structure TwoLevelSpecialization {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, TwoLevelProblem (N i) (m i) (r i)) (δ : ℝ) : Prop where
  parameter_powers :
    Tendsto (fun i => Real.log (twoLevelH0 (m i:ℝ))/Real.log (m i:ℝ)) l (𝓝 (-(7/100:ℝ))) ∧
    Tendsto (fun i => Real.log (twoLevelH1 (m i:ℝ))/Real.log (m i:ℝ)) l (𝓝 (-(1/12:ℝ))) ∧
    Tendsto (fun i => Real.log (twoLevelTheta (m i:ℝ))/Real.log (m i:ℝ)) l (𝓝 (-(11/25:ℝ)))
  construction_admissible : ∀ i (g : MainRandomTape (I i).fixed),
    (twoLevelConstructionProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).admissible
  output_admissible : ∀ i (g : MainRandomTape (I i).fixed),
    (twoLevelConstructAndExpandProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).admissible
  all_outcome_width : ∀ i (g : MainRandomTape (I i).fixed),
    (twoLevelConstructionProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.width ≤ r i
  explicit_factorization : ∀ i (g : MainRandomTape (I i).fixed),
    (twoLevelConstructAndExpandProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.product =
      (twoLevelConstructAndExpandProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.left*
      (twoLevelConstructAndExpandProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.right
  construction_error_probability : ∀ i,
    (mainRandomLaw (I i).fixed).real {g : MainRandomTape (I i).fixed |
      ‖(I i).A*(I i).B-(twoLevelConstructionProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.product‖ ≤
        (1+(m i:ℝ)^(-(11/25:ℝ)))*tailSingularValue ((I i).A*(I i).B) (r i)} ≥ 1-δ
  output_error_probability : ∀ i,
    (mainRandomLaw (I i).fixed).real {g : MainRandomTape (I i).fixed |
      ‖(I i).A*(I i).B-(twoLevelConstructAndExpandProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.product‖ ≤
        (1+(m i:ℝ)^(-(11/25:ℝ)))*tailSingularValue ((I i).A*(I i).B) (r i)} ≥ 1-δ
  raw_width : ∀ᶠ i in l, ∀ (S : StoredSketches (N i) (m i) (N i) 1) (C : MainSupportData S)
    (hr : r i < C.pair.dimension), (2*mainKrylovDegree (I i).fixed S C hr+1)*(r i+1) < m i
  construction_time : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
    (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤
      (N i:ℝ)^((6724/3363:ℝ)+ε)
  explicit_output_time : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
    (twoLevelFullExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤ (N i:ℝ)^((2:ℝ)+ε)

/-- Constant-confidence two-level corollary, with the actual fixed kernel
family, actual rounded scalar parameters, factor construction, dense
expansion, and every finite cap. -/
theorem two_level_specialization {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, TwoLevelProblem (N i) (m i) (r i))
    (δ : ℝ) (hδ : 0 < δ) (hfixed : ∀ i, (I i).delta=δ)
    (hm : Tendsto m l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ))) :
    TwoLevelSpecialization l m N r I δ := by
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hm
  have hconfidence : ∀ᶠ i in l, (m i:ℝ)^(-(1:ℝ)) ≤ (I i).delta := by
    filter_upwards [twoLevel_constant_confidence_family l m hm δ hδ] with i hi
    rwa [hfixed i]
  have hcost := twoLevelRuntimeFinalCosts l m N r I 1 (by norm_num) hm hgrowth hconfidence
  refine
    { parameter_powers := ⟨twoLevel_parameter_log_exponents.1.comp hmR,
        twoLevel_parameter_log_exponents.2.1.comp hmR,twoLevel_parameter_log_exponents.2.2.comp hmR⟩
      construction_admissible := fun i g => twoLevelConstructionProgram_admissible
        (twoLevelRuntimeFinalKernels (m i)) (I i) g
      output_admissible := ?_
      all_outcome_width := fun i g =>
        (twoLevelConstructionProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.width_le
      explicit_factorization := fun i g =>
        (twoLevelConstructAndExpandProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.product_eq
      construction_error_probability := ?_
      output_error_probability := ?_
      raw_width := ?_
      construction_time := hcost.1
      explicit_output_time := hcost.2 }
  · intro i g
    simp only [twoLevelConstructAndExpandProgram,admissible_bind,
      twoLevelConstructionProgram_admissible,twoLevelExpandProgram_admissible,and_self]
  · intro i
    simpa only [hfixed i] using twoLevelConstructionProgram_error_probability
      (twoLevelRuntimeFinalKernels (m i)) (I i)
  · intro i
    simpa only [hfixed i] using twoLevelConstructAndExpandProgram_error_probability
      (twoLevelRuntimeFinalKernels (m i)) (I i)
  · filter_upwards [hm.eventually twoLevel_main_raw_width_eventually] with i hi S C hr
    exact hi (N i) (r i) (I i) S C hr

#print axioms two_level_specialization

end
end HierarchicalAbsoluteSpectral
