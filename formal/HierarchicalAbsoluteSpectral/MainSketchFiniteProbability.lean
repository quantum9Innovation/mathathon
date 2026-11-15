import HierarchicalAbsoluteSpectral.MainSketchCommon
import HierarchicalAbsoluteSpectral.MainSketchFiniteState

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory
variable {n m p r L : ℕ}

/-- The success event is exactly the displayed Gram inequalities for the executed sketches. -/
theorem mainSketchProgram_good_probability (I : FixedProblem n m p r L) :
    (mainRandomLaw I).real {g : MainRandomTape I | MainSketchGood I (mainSketchProgram I g).eval}
      ≥ 1-I.delta/10 := by
  obtain ⟨E,hEm,hEp,hE⟩ := mainSketchProgram_good_event I
  exact hEp.trans (measureReal_mono (fun g hg => hE g hg))

theorem mainSketchFiniteSample_good_probability (I : FixedProblem n m p r L) :
    (mainRandomLaw I).real (mainSketchFiniteSample I ⁻¹'
      {z | MainSketchGood I (mainSketchFromFiniteSample I z)}) ≥ 1-I.delta/10 := by
  simpa only [Set.preimage_setOf_eq,← mainSketchProgram_factorization] using
    mainSketchProgram_good_probability I

end
end HierarchicalAbsoluteSpectral
