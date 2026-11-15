import HierarchicalAbsoluteSpectral.MainStatementsProbability
import HierarchicalAbsoluteSpectral.MainExplicitOutputCost

/-!
Original-input finite guarantees for the literal prepared arithmetic program.

`FixedProblem` contains precisely the input matrices, rank, tolerance, failure
probability and finite accuracy schedule, with their original inequalities.
`tailSingularValue (I.A * I.B) r` is sigma_(r+1), using zero-based indexing.
The returned `product` is the explicitly computed dense matrix C, and
`product_eq` states C = U V for the two returned factors.

The theorem below is an exact finite-budget guarantee. Its budget is a finite
maximum over the preprocessing signs and sampled row sets, so it is uniform
over every Gaussian tape. It does not assert the manuscript's simplified
soft-O expression; that requires the separate analytic cost bounds.
-/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

/-- An explicit integer budget for one finite preprocessing state. It uses
only scalar caps and matrix-kernel costs, never the work of the main program
as its own bound. -/
def fixedDepthStoredExplicitWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (Ck exponent : ℝ) (S : StoredSketches n m p L) : ℕ :=
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  2*m*(n+p)+n*p+mainRandomizedWork I
    (4*L+3*I.queryCap+2*I.repetitions+29+
      ((L+1)*(sketchFormationCap n m I.sketchFailure+sketchFormationCap p m I.sketchFailure)+
        coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1+
        mainCoreWorkCapWithQuery kernels I S C
          (fun hr => mainFlexibleQueryWorkCap kernels (rangeDeflationWorkCap kernels) I S C hr Ck exponent)))

def fixedDepthFiniteStateExplicitWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (Ck exponent : ℝ) (z : MainSketchSampleTape I) : ℕ :=
  fixedDepthStoredExplicitWorkCap kernels I Ck exponent (mainSketchFromFiniteSample I z)

/-- A deterministic finite cap depending on the original problem and genuine
matrix-multiplication cost witnesses, with no dependence on a random tape. -/
def fixedDepthUniformExplicitWorkCap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (Ck exponent : ℝ) : ℕ := by
  classical
  letI := Fintype.ofFinite (MainSketchSampleTape I)
  exact Finset.univ.sup (fixedDepthFiniteStateExplicitWorkCap kernels I Ck exponent)

theorem fixedDepthFiniteStateExplicitWorkCap_actual
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (Ck exponent : ℝ) (g : MainRandomTape I) :
    2*m*(n+p)+n*p+
        preparedFixedDepthRealizedWorkCap kernels (rangeDeflationWorkCap kernels) I g Ck exponent =
      fixedDepthFiniteStateExplicitWorkCap kernels I Ck exponent (mainSketchFiniteSample I g) := by
  change fixedDepthStoredExplicitWorkCap kernels I Ck exponent (mainSketchProgram I g).eval =
    fixedDepthStoredExplicitWorkCap kernels I Ck exponent (mainSketchFromFiniteSample I (mainSketchFiniteSample I g))
  exact congrArg (fixedDepthStoredExplicitWorkCap kernels I Ck exponent) (mainSketchProgram_factorization I g)

theorem preparedFixedDepthExplicitWork_uniform_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ Ck*(N : ℝ)^exponent)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    preparedFixedDepthExplicitWork kernels I g ≤ fixedDepthUniformExplicitWorkCap kernels I Ck exponent := by
  classical
  have hb := preparedFixedDepthExplicitWork_bound_deflation kernels hClassical Ck exponent hC hexponent hK I g
  rw [fixedDepthFiniteStateExplicitWorkCap_actual] at hb
  apply hb.trans
  letI := Fintype.ofFinite (MainSketchSampleTape I)
  exact Finset.le_sup (f:=fixedDepthFiniteStateExplicitWorkCap kernels I Ck exponent)
    (Finset.mem_univ (mainSketchFiniteSample I g))

/-- The actual prepared program has the same original-input probability
guarantee, after charging the computation of every derived scalar parameter. -/
theorem preparedFixedDepthProgram_good_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, ‖I.A*I.B-(preparedFixedDepthProgram kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  obtain ⟨E,hEm,hEp,hE⟩ := fixedDepthProgram_good_event kernels I
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  rw [preparedFixedDepthProgram_eval]
  exact (hE g hg).2

theorem preparedFixedDepthProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) :
    (mainRandomLaw I).real {g : MainRandomTape I |
      ‖I.A*I.B-(preparedFixedDepthProgram kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.delta := by
  simpa only [preparedFixedDepthProgram_eval] using fixedDepthProgram_error_probability kernels I

/-- Original matrices and schedule, genuine multiplication-kernel bounds,
and the literal counted program. Every tape returns width at most r, factors
U,V, an explicitly formed C=UV, and obeys one deterministic finite work cap.
A measurable event of probability at least 1-delta gives the stated spectral
error. This is the finite-budget theorem, before simplifying its cost. -/
theorem fixed_depth_exact_budget_guarantee
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ Ck*(N : ℝ)^exponent)
    (I : FixedProblem n m p r L) :
    (∀ g : MainRandomTape I,
      (preparedFixedDepthProgram kernels I g).admissible ∧
      (preparedFixedDepthProgram kernels I g).eval.width ≤ r ∧
      (preparedFixedDepthProgram kernels I g).eval.product =
        (preparedFixedDepthProgram kernels I g).eval.left*(preparedFixedDepthProgram kernels I g).eval.right ∧
      (preparedFixedDepthProgram kernels I g).eval.product.rank ≤ r ∧
      preparedFixedDepthExplicitWork kernels I g ≤ fixedDepthUniformExplicitWorkCap kernels I Ck exponent) ∧
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, ‖I.A*I.B-(preparedFixedDepthProgram kernels I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  refine ⟨?_,preparedFixedDepthProgram_good_event kernels I⟩
  intro g
  exact ⟨preparedFixedDepthProgram_admissible kernels I g,
    (preparedFixedDepthProgram kernels I g).eval.width_le,
    (preparedFixedDepthProgram kernels I g).eval.product_eq,
    (preparedFixedDepthProgram kernels I g).eval.rank_le,
    preparedFixedDepthExplicitWork_uniform_bound kernels hClassical Ck exponent hC hexponent hK I g⟩

end
end HierarchicalAbsoluteSpectral
