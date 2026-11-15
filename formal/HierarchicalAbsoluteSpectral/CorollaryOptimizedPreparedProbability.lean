import HierarchicalAbsoluteSpectral.CorollaryOptimizedPrepared
import HierarchicalAbsoluteSpectral.CorollaryOptimizedProbability
import HierarchicalAbsoluteSpectral.BaseMainTapeCost
import HierarchicalAbsoluteSpectral.MainExplicitOutputCost

/-! Original-input relative-error theorems for both capped, prepared
comparators.  The all-outcome result type carries explicit factors and their
dense product, with width at most the original requested rank. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

/-- Draws, every field/comparison instruction, and all dense output entries
are included even for zero products and empty returned bases. -/
def comparatorTotalWork (I : FixedProblem n m p r L)
    (program : ArithmeticProgram (FixedRankOutput n p r)) : ℕ :=
  m*(n+p)+program.eval.entryCount+mainRandomizedWork I program.work

theorem preparedConstantComparatorProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    let I := comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1
    (mainRandomLaw I).real {g : MainRandomTape I |
      ‖A*B-(preparedConstantComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).eval.product‖ ≤
        (1+theta)*tailSingularValue (A*B) r} ≥ 1-delta := by
  let I := comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1
  have hp := constantDistortionComparatorProgram_error_probability kernels I
  refine hp.trans (measureReal_mono ?_)
  intro g hg
  have he := (preparedConstantComparatorProgram_specification kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).1
  change ‖A*B-(preparedConstantComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).eval.product‖ ≤ _
  rw [he]
  change ‖A*B-(constantDistortionComparatorProgram kernels I g).eval.product‖ ≤
    (1+min theta (1/1048576))*tailSingularValue (A*B) r at hg
  exact hg.trans (mul_le_mul_of_nonneg_right (by linarith [min_le_left theta (1/1048576:ℝ)])
    (tailSingularValue_nonneg (A*B) r))

theorem preparedGramComparatorProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (theta delta : ℝ) (hmn : m ≤ n) (hmp : m ≤ p)
    (hr : 1 ≤ r) (hrm : r ≤ m) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    let I := comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1
    (mainRandomLaw I).real {g : MainRandomTape I |
      ‖A*B-(preparedGramComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).eval.product‖ ≤
        (1+theta)*tailSingularValue (A*B) r} ≥ 1-delta := by
  let I := comparatorProblem A B theta delta hmn hmp hr hrm htheta hdelta hdelta1
  have hp := exactGramComparatorProgram_error_probability kernels I
  refine hp.trans (measureReal_mono ?_)
  intro g hg
  have he := (preparedGramComparatorProgram_specification kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).1
  change ‖A*B-(preparedGramComparatorProgram kernels A B theta delta hmn hmp hr hrm htheta hdelta hdelta1 g).eval.product‖ ≤ _
  rw [he]
  change ‖A*B-(exactGramComparatorProgram kernels I g).eval.product‖ ≤
    (1+min theta (1/1048576))*tailSingularValue (A*B) r at hg
  exact hg.trans (mul_le_mul_of_nonneg_right (by linarith [min_le_left theta (1/1048576:ℝ)])
    (tailSingularValue_nonneg (A*B) r))

end
end HierarchicalAbsoluteSpectral
