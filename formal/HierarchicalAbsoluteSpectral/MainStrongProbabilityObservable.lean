import HierarchicalAbsoluteSpectral.MainStrongProbabilityProgram
import HierarchicalAbsoluteSpectral.ThresholdKrylovMeasurable
import HierarchicalAbsoluteSpectral.BaseHierarchyContinuity
import HierarchicalAbsoluteSpectral.ThresholdQueryMeasurable

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Polynomial
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p k r L : ℕ}

theorem strongPhysicalRangeProgram_eval_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {A : Core k} {Lmap : Matrix (Fin n) (Fin k) ℝ} (P : MatrixAction A r) (PL : MatrixAction Lmap r)
    (α : ℝ) (v : ℕ) (hα : 0 < α) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (strongPhysicalRangeProgram kernels P PL α v hα Ξ).eval =
      (orthogonalRangeProgram kernels (Lmap*(aeval A (strongFilterPolynomial α v)*Ξ))).eval := by
  simp only [strongPhysicalRangeProgram,eval_bind,eval_pure,OrthogonalRange.cast]
  exact orthogonalRangeProgram_transport kernels _

theorem automaticStrongPhysicalRangeProgram_eval_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {A : Core k} {Lmap : Matrix (Fin n) (Fin k) ℝ} (P : MatrixAction A r) (PL : MatrixAction Lmap r)
    (U β α : ℝ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    (automaticStrongPhysicalRangeProgram kernels P PL U β α hk hU hβ hβ1 hα hα1 Ξ).eval =
      ⟨strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1,
        (orthogonalRangeProgram kernels (Lmap*(aeval A (strongFilterPolynomial α
          (strongGaussianDegree k U β α hk hU hβ hβ1 hα hα1))*Ξ))).eval⟩ := by
  unfold automaticStrongPhysicalRangeProgram
  simp only [eval_bind,eval_pure]
  rw [(strongGaussianDegreeProgram_specification k U β α hk hU hβ hβ1 hα hα1).1]
  rw [strongPhysicalRangeProgram_eval_eq]

def mainStrongProductObservable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  let U := (orthogonalRangeProgram kernels (mainStrongPhysicalPolynomial kernels I S C hk t G)).eval.basis
  (U*Uᵀ)*(I.A*I.B)

theorem mainStrongThresholdProgram_product_eq_observable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (mainStrongThresholdProgram kernels I S C hk t G).eval.product =
      mainStrongProductObservable kernels I S C hk t G := by
  rw [mainStrongThresholdProgram_eval]
  unfold mainStrongCoreProgram
  rw [strongProjectionOutputProgram_eval,automaticStrongPhysicalRangeProgram_eval_eq,projectionOutputProgram_eval]
  simp only [mainStrongProductObservable,mainStrongPhysicalPolynomial,Matrix.mul_assoc]

end
end HierarchicalAbsoluteSpectral
