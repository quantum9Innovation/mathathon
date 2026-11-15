import HierarchicalAbsoluteSpectral.MinMaxProjector
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter
open scoped MatrixOrder Matrix.Norms.L2Operator Topology
variable {k r : ℕ}

/-- The canonical Borel structure for fixed finite matrix dimensions. -/
abbrev matrixBorelSpace (a b : ℕ) : MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := borel _

local instance matrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance matrixBorelInstance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

theorem matrix_inverse_measurable : Measurable (fun A : Core k => A⁻¹) := by
  have hd : Measurable (fun A : Core k => A.det) := continuous_id.matrix_det.measurable
  have ha : Measurable (fun A : Core k => A.adjugate) := continuous_id.matrix_adjugate.measurable
  simpa only [Matrix.inv_def,Ring.inverse_eq_inv] using hd.inv.smul ha

theorem regularizedRangeProjector_measurable (a : ℝ) :
    Measurable (fun Y : Matrix (Fin k) (Fin r) ℝ => regularizedRangeProjector Y a) := by
  have hH : Continuous (fun Y : Matrix (Fin k) (Fin r) ℝ => Y*Yᵀ) :=
    continuous_id.matrix_mul continuous_id.matrix_transpose
  exact hH.measurable.mul (matrix_inverse_measurable.comp ((hH.add continuous_const).measurable))

/-- The projector returned by the actual rank-deficient range algorithm is
Borel measurable, even though its basis dimension changes with the input.
The proof uses a fixed-size regularized limit, not a measurable eigenbasis
or an assumed measurable choice of bases. -/
theorem orthogonalRangeProgram_projector_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    Measurable (fun Y : Matrix (Fin k) (Fin r) ℝ =>
      (orthogonalRangeProgram kernels Y).eval.basis*(orthogonalRangeProgram kernels Y).eval.basisᵀ) := by
  apply measurable_of_tendsto_metrizable
    (fun n : ℕ => regularizedRangeProjector_measurable (1/((n:ℝ)+1)))
  apply tendsto_pi_nhds.mpr
  intro Y
  obtain ⟨V,hV⟩ := orthogonalRangeProgram_basis_in_range kernels Y
  exact regularizedRangeProjector_tendsto Y (orthogonalRangeProgram kernels Y).eval.basis V
    (orthogonalRangeProgram kernels Y).eval.orthogonal
    (orthogonalRangeProgram kernels Y).eval.projection_exact hV

end
end HierarchicalAbsoluteSpectral
