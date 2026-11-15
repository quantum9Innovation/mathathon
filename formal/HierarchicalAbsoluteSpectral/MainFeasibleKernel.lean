import HierarchicalAbsoluteSpectral.MainFinalStatements
import HierarchicalAbsoluteSpectral.CoarseAlgebraDominatedKernelFamily

/-! The classical wide-range bound is constructed from any original
feasible kernel family; it is not an additional model assumption. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

def feasibleFixedDepthProgram (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :=
  preparedFixedDepthProgram (classicallyDominatedKernels K) I g

theorem fixed_depth_from_feasible_kernel
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost : ℝ) ≤ Ck*(N : ℝ)^exponent)
    (I : FixedProblem n m p r L) :
    (∀ g : MainRandomTape I,
      (feasibleFixedDepthProgram K I g).admissible ∧
      (feasibleFixedDepthProgram K I g).eval.width ≤ r ∧
      (feasibleFixedDepthProgram K I g).eval.product =
        (feasibleFixedDepthProgram K I g).eval.left*(feasibleFixedDepthProgram K I g).eval.right ∧
      (feasibleFixedDepthProgram K I g).eval.product.rank ≤ r ∧
      (preparedFixedDepthExplicitWork (classicallyDominatedKernels K) I g : ℝ) ≤
        fixedPaperExplicitPrefactor Ck I*
          fixedPaperMainTerm (classicallyDominatedKernels K) exponent I) ∧
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, ‖I.A*I.B-(feasibleFixedDepthProgram K I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  have hdom : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      (((classicallyDominatedKernels K) a b c).cost : ℝ) ≤ Ck*(N : ℝ)^exponent := by
    intro a b c N hN ha hb hc
    exact (Nat.cast_le.mpr (classicallyDominatedKernels_cost_le K a b c)).trans
      (hK a b c N hN ha hb hc)
  simpa only [feasibleFixedDepthProgram, fixedPaperMainTerm, fixedPaperWidePenalty] using
    fixed_depth_tradeoff (classicallyDominatedKernels K)
      (classicallyDominatedKernels_cost_classical K) Ck exponent hC hexponent hdom I

/-- The manuscript's fixed-depth theorem from a genuine feasible multiplication
family alone. The classical safeguard is constructed, and the soft-O factor is
an explicit polynomial in logarithms of the original inputs. -/
theorem fixed_depth_from_feasible_kernel_polylog
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost : ℝ) ≤ Ck*(N : ℝ)^exponent)
    (I : FixedProblem n m p r L) :
    (∀ g : MainRandomTape I,
      (feasibleFixedDepthProgram K I g).admissible ∧
      (feasibleFixedDepthProgram K I g).eval.width ≤ r ∧
      (feasibleFixedDepthProgram K I g).eval.product =
        (feasibleFixedDepthProgram K I g).eval.left*(feasibleFixedDepthProgram K I g).eval.right ∧
      (feasibleFixedDepthProgram K I g).eval.product.rank ≤ r ∧
      (preparedFixedDepthExplicitWork (classicallyDominatedKernels K) I g : ℝ) ≤
        (Ck+1)*fixedPolylogDepthConstant L*(fixedPolylogGauge I)^(2*L+4)*
          fixedPaperMainTerm (classicallyDominatedKernels K) exponent I) ∧
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, ‖I.A*I.B-(feasibleFixedDepthProgram K I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  have hdom : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      (((classicallyDominatedKernels K) a b c).cost : ℝ) ≤ Ck*(N : ℝ)^exponent := by
    intro a b c N hN ha hb hc
    exact (Nat.cast_le.mpr (classicallyDominatedKernels_cost_le K a b c)).trans
      (hK a b c N hN ha hb hc)
  simpa only [feasibleFixedDepthProgram] using
    fixed_depth_tradeoff_polylog (classicallyDominatedKernels K)
      (classicallyDominatedKernels_cost_classical K) Ck exponent hC hexponent hdom I

end
end HierarchicalAbsoluteSpectral
