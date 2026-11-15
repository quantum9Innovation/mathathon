import HierarchicalAbsoluteSpectral.GaussianBasics
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact second moments and a Markov tail for the finite Gaussian array. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Squared Frobenius energy, with the random array stored column first. -/
def gaussianEnergy {n r : ℕ} (G : Fin r → Fin n → ℝ) : ℝ :=
  ∑ j, ∑ i, (G j i)^2

theorem gaussianEnergy_nonneg {n r : ℕ} (G : Fin r → Fin n → ℝ) :
    0 ≤ gaussianEnergy G := by
  unfold gaussianEnergy
  positivity

theorem gaussianVector_coordinate_sq_integrable (n : ℕ) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => (x i)^2) (gaussianVector n) := by
  exact integrable_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1)
    (i := i) (f := fun x : ℝ => x^2) ((memLp_id_gaussianReal 2).integrable_sq)

theorem gaussianVector_coordinate_second_moment (n : ℕ) (i : Fin n) :
    ∫ x : Fin n → ℝ, (x i)^2 ∂gaussianVector n = 1 := by
  change ∫ x : Fin n → ℝ, (x i)^2 ∂Measure.pi (fun _ => gaussianReal 0 1) = 1
  exact (integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1)
    (i := i) (f := fun x : ℝ => x^2) (by fun_prop)).trans gaussianReal_unit_second_moment

theorem gaussianColumns_coordinate_sq_integrable (n r : ℕ) (j : Fin r) (i : Fin n) :
    Integrable (fun G : Fin r → Fin n → ℝ => (G j i)^2) (gaussianColumns n r) := by
  exact integrable_comp_eval (μ := fun _ : Fin r => gaussianVector n)
    (i := j) (f := fun x : Fin n → ℝ => (x i)^2)
    (gaussianVector_coordinate_sq_integrable n i)

theorem gaussianColumns_coordinate_second_moment (n r : ℕ) (j : Fin r) (i : Fin n) :
    ∫ G : Fin r → Fin n → ℝ, (G j i)^2 ∂gaussianColumns n r = 1 := by
  change ∫ G : Fin r → Fin n → ℝ, (G j i)^2 ∂Measure.pi (fun _ => gaussianVector n) = 1
  exact (integral_comp_eval (μ := fun _ : Fin r => gaussianVector n)
    (i := j) (f := fun x : Fin n → ℝ => (x i)^2)
    (gaussianVector_coordinate_sq_integrable n i).aestronglyMeasurable).trans
    (gaussianVector_coordinate_second_moment n i)

theorem gaussianEnergy_integrable (n r : ℕ) :
    Integrable (@gaussianEnergy n r) (gaussianColumns n r) := by
  exact integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun i _ => gaussianColumns_coordinate_sq_integrable n r j i))

theorem integral_gaussianEnergy (n r : ℕ) :
    ∫ G, gaussianEnergy G ∂gaussianColumns n r = (n : ℝ)*r := by
  unfold gaussianEnergy
  rw [integral_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun i _ => gaussianColumns_coordinate_sq_integrable n r j i))]
  simp_rw [integral_finsetSum _ (fun i _ => gaussianColumns_coordinate_sq_integrable n r _ i),
    gaussianColumns_coordinate_second_moment]
  simp [mul_comm]

/-- No independence with a head event is needed when this tail is union-bounded. -/
theorem gaussianEnergy_markov (n r : ℕ) (t : ℝ) (ht : 0 < t) :
    (gaussianColumns n r).real {G | t ≤ gaussianEnergy G} ≤ (n : ℝ)*r/t := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (@gaussianEnergy_nonneg n r))
    (gaussianEnergy_integrable n r) t
  rw [integral_gaussianEnergy] at hm
  exact (le_div_iff₀ ht).mpr (by simpa [mul_comm] using hm)

end
end HierarchicalAbsoluteSpectral
