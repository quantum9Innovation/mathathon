import HierarchicalAbsoluteSpectral.MainFamilyProgramProbability
import HierarchicalAbsoluteSpectral.MainFamilyProgramCost
import HierarchicalAbsoluteSpectral.MainFamilyProgramUniform
import HierarchicalAbsoluteSpectral.MainFamilyProgramSketchRows
import HierarchicalAbsoluteSpectral.MainFamilyProgramActionBounds
import HierarchicalAbsoluteSpectral.MainFamilyProgramActionOverhead
import HierarchicalAbsoluteSpectral.MainFamilyProgramCombinedDegree
import HierarchicalAbsoluteSpectral.MainFamilyProgramPreparationCost
import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedCyclicRowFamily

/-! Original-input construction with actual fixed-shape circuit witnesses.
This finite correctness and operation-cap endpoint is separate from the
remaining quantitative unfolding of the total family cost. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Filter

theorem exists_growingDepthProgram_original_input_guarantees
    (d : ℝ) (hd : FamilyExponentAdmissible d) :
    ∃ (ζ : ℝ) (K : ∀ N m : ℕ, 0 < m → ∀ a b c : ℕ, ArithmeticKernel a b c)
      (χ χOut : ℕ → ℝ) (C : ℝ),
      0 < ζ ∧ ζ < 2+2*d-9/4 ∧ 0 < C ∧
      (∀ m, 1 ≤ χ m) ∧ (∀ N, 1 ≤ χOut N) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, χ m ≤ (m : ℝ)^ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, χOut N ≤ (N : ℝ)^ε) ∧
      ∀ (N m r : ℕ) (I : FamilyProblem N m r),
        FixedFamilyKernelEnvelopes ζ N m (K N m I.core_positive) (χ m) (χOut N) C ∧
        FixedSixRowKernelEnvelopes m (K N m I.core_positive) (χ m) ∧
        (familyRandomLaw I).real (familySuccessEvent (K N m I.core_positive) I) ≥ 1-I.delta ∧
        ∀ g : FamilyRandomTape I,
          (growingDepthProgram (K N m I.core_positive) I g).admissible ∧
          (growingDepthProgram (K N m I.core_positive) I g).eval.width ≤ r ∧
          (growingDepthProgram (K N m I.core_positive) I g).eval.product.rank ≤ r ∧
          growingDepthExplicitWork (K N m I.core_positive) I g ≤
            2*m*(N+N)+N*N+growingDepthRealizedWorkCap (K N m I.core_positive) I g C (9/4+ζ) := by
  let ζ := (2+2*d-9/4)/2
  have hζ : 0 < ζ := by dsimp [ζ]; linarith [hd.1]
  have hζmargin : ζ < 2+2*d-9/4 := by dsimp [ζ]; linarith [hd.1]
  obtain ⟨K,χ,χOut,C,hC,hχ,hχOut,hχsub,hχOutsub,hK⟩ := exists_fixed_six_family_kernel ζ hζ
  refine ⟨ζ,K,χ,χOut,C,hζ,hζmargin,hC,hχ,hχOut,hχsub,hχOutsub,?_⟩
  intro N m r I
  have hEnv := hK N m I.core_positive I.core_le_side
  refine ⟨hEnv.1,hEnv.2,growingDepthProgram_error_probability (K N m I.core_positive) I,?_⟩
  intro g
  refine ⟨growingDepthProgram_admissible _ I g,(growingDepthProgram_rank_cap _ I g).1,
    (growingDepthProgram_rank_cap _ I g).2,?_⟩
  exact growingDepthExplicitWork_bound_deflation _ hEnv.1.«classical» C (9/4+ζ) hC
    (by linarith) hEnv.1.core I g

end
end HierarchicalAbsoluteSpectral
