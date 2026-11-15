import HierarchicalAbsoluteSpectral.GaussianBasics
import Mathlib.Probability.Independence.Basic

/-! Selecting disjoint preallocated Gaussian columns preserves their exact law. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

theorem gaussianColumns_restrict_measurePreserving (k h r : ℕ) (e : Fin h ↪ Fin r) :
    MeasurePreserving (fun G : Fin r → Fin k → ℝ => fun j => G (e j))
      (gaussianColumns k r) (gaussianColumns k h) := by
  have hi : iIndepFun (fun j : Fin r => fun G : Fin r → Fin k → ℝ => G j)
      (gaussianColumns k r) :=
    iIndepFun_pi (X := fun _ => id) (μ := fun _ : Fin r => gaussianVector k)
      (fun _ => aemeasurable_id)
  have his := hi.precomp e.injective
  refine ⟨by fun_prop, ?_⟩
  have hm := his.map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)
  change (gaussianColumns k r).map (fun G => fun j => G (e j)) = Measure.pi (fun _ => gaussianVector k)
  rw [hm]
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : Fin r => gaussianVector k) (e j)).map_eq

end
end HierarchicalAbsoluteSpectral
