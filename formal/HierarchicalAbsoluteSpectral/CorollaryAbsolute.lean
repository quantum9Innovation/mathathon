import HierarchicalAbsoluteSpectral.CorollaryAbsoluteCorrectness
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteProbability
import HierarchicalAbsoluteSpectral.CorollaryAbsolutePrepared

/-! Absolute accuracy without a supplied rank. The success event is built
from the actual embeddings, query repetitions and carried-filter samples.
The slack rank occurs only in the conclusion, and its zero case is included. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {n m p L : ℕ}

theorem absolute_error_without_supplied_rank
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) :
    ∃ E : Set (AbsoluteTape I), MeasurableSet E ∧
      (absoluteRandomLaw I).real E ≥ 1-I.delta ∧ ∀ g ∈ E,
        let out := (absoluteAlgorithmProgram kernels I g).eval
        out.result.width ≤ 2*I.slackRank ∧ ‖I.A*I.B-out.result.product‖ ≤ I.tolerance := by
  obtain ⟨E,hEm,hEp,hE⟩ := absolute_fixed_threshold_all_ranks_good_event kernels I
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  obtain ⟨hsketch,hgood⟩ := hE g hg
  rw [absoluteAlgorithmProgram_eval]
  exact absoluteCoreProgram_correct kernels I _ hsketch _ g.2 hgood

theorem absolute_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) :
    (absoluteRandomLaw I).real {g |
      (absoluteAlgorithmProgram kernels I g).eval.result.width ≤ 2*I.slackRank ∧
        ‖I.A*I.B-(absoluteAlgorithmProgram kernels I g).eval.result.product‖ ≤ I.tolerance} ≥ 1-I.delta := by
  obtain ⟨E,hEm,hEp,hE⟩ := absolute_error_without_supplied_rank kernels I
  exact hEp.trans (measureReal_mono (fun g hg => hE g hg))

theorem prepared_absolute_error_without_supplied_rank
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem n m p L) :
    ∃ E : Set (AbsoluteTape I), MeasurableSet E ∧
      (absoluteRandomLaw I).real E ≥ 1-I.delta ∧ ∀ g ∈ E,
        let out := (preparedAbsoluteAlgorithmProgram kernels I g).eval
        out.result.width ≤ 2*I.slackRank ∧ ‖I.A*I.B-out.result.product‖ ≤ I.tolerance := by
  obtain ⟨E,hEm,hEp,hE⟩ := absolute_error_without_supplied_rank kernels I
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  rw [preparedAbsoluteAlgorithmProgram_eval]
  exact hE g hg

end
end HierarchicalAbsoluteSpectral
