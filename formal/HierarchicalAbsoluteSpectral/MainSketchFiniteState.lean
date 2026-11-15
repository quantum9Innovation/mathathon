import HierarchicalAbsoluteSpectral.MainSketchFiniteCore
import HierarchicalAbsoluteSpectral.MainSketchProgram
import HierarchicalAbsoluteSpectral.MainSketchGood

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory SRHT
variable {n m p r L : ℕ}

/-- The preprocessing state consists only of finitely many sign assignments and row sets. -/
abbrev MainSketchSampleTape (I : FixedProblem n m p r L) :=
  ((j : Fin (L+1)) → SketchFiniteSample (dyadicPaddingLevel n)
    (embeddingComputedRowCount (2^dyadicPaddingLevel n) m (I.accuracy j.val) I.sketchFailure)) ×
  ((j : Fin (L+1)) → SketchFiniteSample (dyadicPaddingLevel p)
    (embeddingComputedRowCount (2^dyadicPaddingLevel p) m (I.accuracy j.val) I.sketchFailure))

def mainSketchFiniteSample (I : FixedProblem n m p r L) (g : MainRandomTape I) : MainSketchSampleTape I :=
  ((fun j => gaussianSRHTSample (dyadicPaddingLevel n)
      (embeddingComputedRowCount (2^dyadicPaddingLevel n) m (I.accuracy j.val) I.sketchFailure)
      (min_le_left _ _) (mainLeftSketchInput I g j)),
   (fun j => gaussianSRHTSample (dyadicPaddingLevel p)
      (embeddingComputedRowCount (2^dyadicPaddingLevel p) m (I.accuracy j.val) I.sketchFailure)
      (min_le_left _ _) (mainRightSketchInput I g j)))

theorem mainSketchFiniteSample_measurable (I : FixedProblem n m p r L) :
    Measurable (mainSketchFiniteSample I) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro j
    apply (gaussianSRHTSample_measurable _ _ _).comp
    unfold mainLeftSketchInput
    fun_prop
  · apply measurable_pi_lambda
    intro j
    apply (gaussianSRHTSample_measurable _ _ _).comp
    unfold mainRightSketchInput
    fun_prop

def mainSketchFromFiniteSample (I : FixedProblem n m p r L) (z : MainSketchSampleTape I) :
    StoredSketches n m p L :=
  storedSketchesFromFactors
    (fun j => boundedSketchFromSample (dyadicPaddingLevel n) (dyadicPaddingLevel_ge n)
      I.A (I.accuracy j.val) I.sketchFailure (z.1 j))
    (fun j => boundedSketchFromSample (dyadicPaddingLevel p) (dyadicPaddingLevel_ge p)
      I.Bᵀ (I.accuracy j.val) I.sketchFailure (z.2 j))

theorem mainSketchProgram_factorization (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (mainSketchProgram I g).eval = mainSketchFromFiniteSample I (mainSketchFiniteSample I g) := by
  rw [mainSketchProgram_eval]
  unfold mainSketchFromFiniteSample mainSketchFiniteSample
  apply congrArg₂ storedSketchesFromFactors
  · funext j
    exact boundedSketchProgram_eval _ _ _ _ _ _
  · funext j
    exact boundedSketchProgram_eval _ _ _ _ _ _

/-- The event refers to the actual executed output; measurability follows from its finite state. -/
theorem mainSketchProgram_good_measurable (I : FixedProblem n m p r L) :
    MeasurableSet {g : MainRandomTape I | MainSketchGood I (mainSketchProgram I g).eval} := by
  classical
  have hm : MeasurableSet {z : MainSketchSampleTape I | MainSketchGood I (mainSketchFromFiniteSample I z)} :=
    (Set.to_countable _).measurableSet
  have he : {g : MainRandomTape I | MainSketchGood I (mainSketchProgram I g).eval} =
      mainSketchFiniteSample I ⁻¹' {z | MainSketchGood I (mainSketchFromFiniteSample I z)} := by
    ext g
    change MainSketchGood I (mainSketchProgram I g).eval ↔
      MainSketchGood I (mainSketchFromFiniteSample I (mainSketchFiniteSample I g))
    rw [mainSketchProgram_factorization]
  rw [he]
  exact hm.preimage (mainSketchFiniteSample_measurable I)

end
end HierarchicalAbsoluteSpectral
