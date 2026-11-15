import HierarchicalAbsoluteSpectral.CorollaryTwoLevelConstructionProgram
import HierarchicalAbsoluteSpectral.MainPreparedProbability
import HierarchicalAbsoluteSpectral.MainExplicitOutputCost

/-! The unconditional original-input success probability for the rounded
two-level algorithm, including the factor-only and dense-output callers. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator
variable {N m r : ℕ}

theorem TwoLevelProblem.theta_le_power (I : TwoLevelProblem N m r) :
    I.fixed.theta ≤ (m:ℝ)^(-(11/25:ℝ)) := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast I.core_positive
  exact (twoLevelParameters_bounds m hm).2.2.2.2.2

theorem TwoLevelProblem.relative_error_allowance (I : TwoLevelProblem N m r) :
    (1+I.fixed.theta)*tailSingularValue (I.A*I.B) r ≤
      (1+(m:ℝ)^(-(11/25:ℝ)))*tailSingularValue (I.A*I.B) r :=
  mul_le_mul_of_nonneg_right (add_le_add le_rfl I.theta_le_power) (tailSingularValue_nonneg _ _)

theorem preparedTwoLevelProgram_good_event (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) :
    ∃ E : Set (MainRandomTape I.fixed), MeasurableSet E ∧
      (mainRandomLaw I.fixed).real E ≥ 1-I.delta ∧ ∀ g ∈ E,
        (preparedTwoLevelProgram kernels I g).eval.width ≤ r ∧
        (preparedTwoLevelProgram kernels I g).eval.product.rank ≤ r ∧
        ‖I.A*I.B-(preparedTwoLevelProgram kernels I g).eval.product‖ ≤
          (1+(m:ℝ)^(-(11/25:ℝ)))*tailSingularValue (I.A*I.B) r := by
  obtain ⟨E,hEm,hEp,hE⟩ := fixedDepthProgram_good_event kernels I.fixed
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  rw [preparedTwoLevelProgram_eval]
  exact ⟨(fixedDepthProgram kernels I.fixed g).eval.width_le,(hE g hg).1,
    (hE g hg).2.trans I.relative_error_allowance⟩

theorem preparedTwoLevelProgram_error_probability (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) :
    (mainRandomLaw I.fixed).real {g : MainRandomTape I.fixed |
      ‖I.A*I.B-(preparedTwoLevelProgram kernels I g).eval.product‖ ≤
        (1+(m:ℝ)^(-(11/25:ℝ)))*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  obtain ⟨E,hEm,hEp,hE⟩ := preparedTwoLevelProgram_good_event kernels I
  exact hEp.trans (measureReal_mono (fun g hg => (hE g hg).2.2))

theorem twoLevelConstructionProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : TwoLevelProblem N m r) :
    (mainRandomLaw I.fixed).real {g : MainRandomTape I.fixed |
      ‖I.A*I.B-(twoLevelConstructionProgram kernels I g).eval.product‖ ≤
        (1+(m:ℝ)^(-(11/25:ℝ)))*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  simpa only [twoLevelConstructionProgram_eval,FixedRankOutput.twoLevelFactors_product,
    preparedTwoLevelProgram_eval] using preparedTwoLevelProgram_error_probability kernels I

theorem twoLevelConstructAndExpandProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : TwoLevelProblem N m r) :
    (mainRandomLaw I.fixed).real {g : MainRandomTape I.fixed |
      ‖I.A*I.B-(twoLevelConstructAndExpandProgram kernels I g).eval.product‖ ≤
        (1+(m:ℝ)^(-(11/25:ℝ)))*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  simpa only [twoLevelConstructAndExpandProgram_product,preparedTwoLevelProgram_eval] using
    preparedTwoLevelProgram_error_probability kernels I

def twoLevelConstructionExplicitWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) : ℕ :=
  m*(N+N)+N*(twoLevelConstructionProgram kernels I g).eval.width+
    (twoLevelConstructionProgram kernels I g).eval.width*N+
    mainRandomizedWork I.fixed (twoLevelConstructionProgram kernels I g).work

def twoLevelFullExplicitWork (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) : ℕ :=
  m*(N+N)+(twoLevelConstructAndExpandProgram kernels I g).eval.entryCount+
    mainRandomizedWork I.fixed (twoLevelConstructAndExpandProgram kernels I g).work

theorem twoLevelFullExplicitWork_split (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : TwoLevelProblem N m r) (g : MainRandomTape I.fixed) :
    twoLevelFullExplicitWork kernels I g = twoLevelConstructionExplicitWork kernels I g+
      N*N+(kernels N (twoLevelConstructionProgram kernels I g).eval.width N).cost := by
  have hw : (twoLevelConstructAndExpandProgram kernels I g).eval.width =
      (twoLevelConstructionProgram kernels I g).eval.width := by
    simp only [twoLevelConstructAndExpandProgram,eval_bind,twoLevelExpandProgram,eval_pure]
  unfold twoLevelFullExplicitWork
  rw [FixedRankOutput.entryCount,hw,twoLevelConstructAndExpandProgram_work]
  unfold twoLevelConstructionExplicitWork mainRandomizedWork
  omega

end
end HierarchicalAbsoluteSpectral
