import HierarchicalAbsoluteSpectral.JointInertiaEvent
import HierarchicalAbsoluteSpectral.CoarseAlgebraProjectedInertia

/-! The canonical jointly measurable event is sufficient for the literal
rank-deficient fast inertia program, for every symmetric input matrix. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Matrix.Norms.L2Operator
local instance jointProgramMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance jointProgramMatrixBorelInstance (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

theorem jointInertiaGood_measurable_comp {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (D : Ω → Core n) (g : Ω → Fin (n*n) → ℝ) (hD : Measurable D) (hg : Measurable g) :
    MeasurableSet {ω | jointInertiaGood (D ω) (g ω)} := by
  have hf : Measurable (fun ω : Ω => (D ω,g ω)) := hD.prodMk hg
  change MeasurableSet ((fun ω : Ω => (D ω,g ω)) ⁻¹'
    {z : Core n × (Fin (n*n) → ℝ) | jointInertiaGood z.1 z.2})
  exact (jointInertiaGood_measurable (n := n)).preimage hf

theorem jointInertiaGood_section_measurable {n : ℕ} (D : Core n) :
    MeasurableSet {g : Fin (n*n) → ℝ | jointInertiaGood D g} :=
  jointInertiaGood_measurable_comp (n := n) (fun _ => D) id measurable_const measurable_id

theorem jointInertiaGood_probability_one {n : ℕ} (D : Core n) :
    (gaussianVector (n*n)).real {g | jointInertiaGood D g} = 1 := by
  have hm := (ae_iff_measure_eq (jointInertiaGood_section_measurable D).nullMeasurableSet).mp
    (jointInertiaGood_ae D)
  rw [Measure.real,hm]
  simp

theorem projectedSingularInertiaProgram_success_of_joint_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) (g : Fin (n*n) → ℝ)
    (hg : jointInertiaGood D g) :
    ∃ out, (projectedSingularInertiaProgram kernels n D hD g).eval = some out :=
  projectedSingularInertiaProgram_success_of_polynomial_event kernels n D hD g
    (jointInertiaGood_polynomial_event D g hg)

end
end HierarchicalAbsoluteSpectral
