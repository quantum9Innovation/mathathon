import HierarchicalAbsoluteSpectral.MainStatementsProbability
import HierarchicalAbsoluteSpectral.MainExplicitOutputCost
import HierarchicalAbsoluteSpectral.BaseFixedPaperTotal
import HierarchicalAbsoluteSpectral.BaseFixedPolylog

/-!
Original-input finite guarantees for the literal prepared arithmetic program.

`FixedProblem` contains precisely the input matrices, rank, tolerance, failure
probability and finite accuracy schedule, with their original inequalities.
`tailSingularValue (I.A * I.B) r` is sigma_(r+1), using zero-based indexing.
The returned `product` is the explicitly computed dense matrix C, and
`product_eq` states C = U V for the two returned factors.

The first theorem is an exact finite-budget guarantee. Its budget is a finite
maximum over the preprocessing signs and sampled row sets, so it is uniform
over every Gaussian tape. The final `fixed_depth_tradeoff` and its narrow
corollary display the manuscript's cost terms. Every fixed-depth logarithmic
coefficient is exposed by `fixedPaperExplicitPrefactor`.
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

/-- The fixed-depth main guarantee for the literal prepared program.
Here `exponent` is any genuine feasible core exponent, e.g. omega+zeta.
The displayed terms are I, G_(h0), the core power, the original-factor
action, the h_j-weighted fine actions, np, and explicit product formation.
`fixedFineProductCost ... j` uses accuracy h_(j+1), so its coefficient is
h_j, exactly the h_(j-1) coefficient of the manuscript's one-based sum.
The last conditional is zero in the cheap-width regime and m*w_K^2 otherwise.
The prefactor is independent of matrix entries, singular values and all
random thresholds. The event is constructed, not a theorem hypothesis. -/
theorem fixed_depth_tradeoff
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) :
    (∀ g : MainRandomTape I,
      (preparedFixedDepthProgram K I g).admissible ∧
      (preparedFixedDepthProgram K I g).eval.width ≤ r ∧
      (preparedFixedDepthProgram K I g).eval.product =
        (preparedFixedDepthProgram K I g).eval.left*(preparedFixedDepthProgram K I g).eval.right ∧
      (preparedFixedDepthProgram K I g).eval.product.rank ≤ r ∧
      (preparedFixedDepthExplicitWork K I g:ℝ) ≤ fixedPaperExplicitPrefactor Ck I*
        ((m*(n+p):ℕ)+(fixedCoarseProductCost K I:ℝ)+(m:ℝ)^exponent+
          Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ)+
          fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta)+
          (n*p:ℕ)+(matrixProductCost K n r p:ℝ)+
          (if fixedKrylovRawWidth I ≤ m then 0 else (m:ℝ)*(fixedKrylovRawWidth I:ℝ)^2))) ∧
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, ‖I.A*I.B-(preparedFixedDepthProgram K I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  refine ⟨?_,preparedFixedDepthProgram_good_event K I⟩
  intro g
  refine ⟨preparedFixedDepthProgram_admissible K I g,
    (preparedFixedDepthProgram K I g).eval.width_le,
    (preparedFixedDepthProgram K I g).eval.product_eq,
    (preparedFixedDepthProgram K I g).eval.rank_le,?_⟩
  simpa only [fixedPaperMainTerm,fixedPaperWidePenalty] using
    preparedFixedDepthExplicitWork_paper_bound K hClassical Ck exponent hC hexponent hK I g

/-- Equation (fixedcost), with every hidden logarithmic coefficient explicit.
The sufficient per-run cap is q=`fixedOuterDegreeCap I`, and
`fixedKrylovRawWidth I` is exactly (2*q+1)*(r+1). -/
theorem fixed_depth_tradeoff_narrow
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (hwidth : fixedKrylovRawWidth I ≤ m) :
    (∀ g : MainRandomTape I,
      (preparedFixedDepthProgram K I g).admissible ∧
      (preparedFixedDepthProgram K I g).eval.width ≤ r ∧
      (preparedFixedDepthProgram K I g).eval.product =
        (preparedFixedDepthProgram K I g).eval.left*(preparedFixedDepthProgram K I g).eval.right ∧
      (preparedFixedDepthProgram K I g).eval.product.rank ≤ r ∧
      (preparedFixedDepthExplicitWork K I g:ℝ) ≤ fixedPaperExplicitPrefactor Ck I*
        ((m*(n+p):ℕ)+(fixedCoarseProductCost K I:ℝ)+(m:ℝ)^exponent+
          Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ)+
          fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta)+
          (n*p:ℕ)+(matrixProductCost K n r p:ℝ))) ∧
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, ‖I.A*I.B-(preparedFixedDepthProgram K I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  simpa only [if_pos hwidth,add_zero] using
    fixed_depth_tradeoff K hClassical Ck exponent hC hexponent hK I

/-- The fixed-depth tilde overhead is proved, not an assumed runtime profile.
`fixedPolylogDepthConstant L` depends only on the fixed depth. The gauge is
1+log n+log p+log m+log(1/theta)+log(1/delta)+sum_j log(1/h_j), with no
matrix-entry, spectral-gap, condition-number, or random-threshold logarithm.
`fixedPaperMainTerm` is exactly the cost expression displayed above, including
the conditional m*w_K^2 fallback. All operations and output entries are charged. -/
theorem fixed_depth_tradeoff_polylog
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) :
    (∀ g : MainRandomTape I,
      (preparedFixedDepthProgram K I g).admissible ∧
      (preparedFixedDepthProgram K I g).eval.width ≤ r ∧
      (preparedFixedDepthProgram K I g).eval.product =
        (preparedFixedDepthProgram K I g).eval.left*(preparedFixedDepthProgram K I g).eval.right ∧
      (preparedFixedDepthProgram K I g).eval.product.rank ≤ r ∧
      (preparedFixedDepthExplicitWork K I g:ℝ) ≤
        (Ck+1)*fixedPolylogDepthConstant L*(fixedPolylogGauge I)^(2*L+4)*
          fixedPaperMainTerm K exponent I) ∧
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, ‖I.A*I.B-(preparedFixedDepthProgram K I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  refine ⟨?_,preparedFixedDepthProgram_good_event K I⟩
  intro g
  refine ⟨preparedFixedDepthProgram_admissible K I g,
    (preparedFixedDepthProgram K I g).eval.width_le,
    (preparedFixedDepthProgram K I g).eval.product_eq,
    (preparedFixedDepthProgram K I g).eval.rank_le,?_⟩
  have hwork := preparedFixedDepthExplicitWork_paper_bound K hClassical Ck exponent hC hexponent hK I g
  have hpoly := fixedPaperExplicitPrefactor_polylog_bound Ck hC.le I
  exact hwork.trans (mul_le_mul_of_nonneg_right hpoly (fixedPaperMainTerm_components K exponent I).1)

/-- The manuscript's cheap-width fixed-depth tradeoff with a formally bounded
polylogarithmic overhead, displayed together with its literal output and error. -/
theorem fixed_depth_tradeoff_narrow_polylog
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (hwidth : fixedKrylovRawWidth I ≤ m) :
    (∀ g : MainRandomTape I,
      (preparedFixedDepthProgram K I g).admissible ∧
      (preparedFixedDepthProgram K I g).eval.width ≤ r ∧
      (preparedFixedDepthProgram K I g).eval.product =
        (preparedFixedDepthProgram K I g).eval.left*(preparedFixedDepthProgram K I g).eval.right ∧
      (preparedFixedDepthProgram K I g).eval.product.rank ≤ r ∧
      (preparedFixedDepthExplicitWork K I g:ℝ) ≤
        (Ck+1)*fixedPolylogDepthConstant L*(fixedPolylogGauge I)^(2*L+4)*
          ((m*(n+p):ℕ)+(fixedCoarseProductCost K I:ℝ)+(m:ℝ)^exponent+
            Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ)+
            fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta)+
            (n*p:ℕ)+(matrixProductCost K n r p:ℝ))) ∧
    ∃ E : Set (MainRandomTape I), MeasurableSet E ∧ (mainRandomLaw I).real E ≥ 1-I.delta ∧
      ∀ g ∈ E, ‖I.A*I.B-(preparedFixedDepthProgram K I g).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r := by
  simpa only [fixedPaperMainTerm_narrow K exponent I hwidth] using
    fixed_depth_tradeoff_polylog K hClassical Ck exponent hC hexponent hK I

end
end HierarchicalAbsoluteSpectral
