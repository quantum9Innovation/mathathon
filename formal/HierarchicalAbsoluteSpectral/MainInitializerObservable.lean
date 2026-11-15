import HierarchicalAbsoluteSpectral.ProbabilityInitializerProgram
import HierarchicalAbsoluteSpectral.MinMaxProjectorMeasurable

/-! The scalar residual computed by the executed initializer is a Borel
observable.  The observable uses the actual range program's fixed-size
projector, so no choice of a measurable basis or constant-rank hypothesis
is required. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k r : ℕ}

local instance initializerMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance initializerMatrixBorelInstance (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

/-- The actual range program's projector for the initializer sketch. -/
def mainInitializerProjector
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) : Core k :=
  let out := (orthogonalRangeProgram kernels (T*Ξ)).eval
  out.basis*out.basisᵀ

/-- Fixed-size residual, including every rank-deficient sketch. -/
def mainInitializerResidual
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) : Core k :=
  T-mainInitializerProjector kernels T Ξ*T

/-- The initializer's residual norm as an observable on fixed-size matrices. -/
def mainInitializerObservable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) : ℝ :=
  matrixFrobeniusValue (mainInitializerResidual kernels T Ξ)

theorem gaussianInitializerProgram_projector_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ) :
    (gaussianInitializerProgram kernels T Ξ β).eval.range.basis*
      (gaussianInitializerProgram kernels T Ξ β).eval.range.basisᵀ =
        mainInitializerProjector kernels T Ξ := by
  generalize heval : (gaussianInitializerProgram kernels T Ξ β).eval = out
  simp only [gaussianInitializerProgram, ArithmeticProgram.eval_bind,
    ArithmeticProgram.eval_pure] at heval
  subst out
  exact congrArg (fun Y : Matrix (Fin k) (Fin r) ℝ =>
    (orthogonalRangeProgram kernels Y).eval.basis*
      (orthogonalRangeProgram kernels Y).eval.basisᵀ)
    ((ArithmeticProgram.certify_eval ((kernels k k r).program T Ξ)).trans
      (ArithmeticKernel.program_eval _ _ _))

theorem gaussianInitializerProgram_residual_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ) :
    initializerResidual T (gaussianInitializerProgram kernels T Ξ β).eval.range.basis =
      mainInitializerResidual kernels T Ξ := by
  simp only [initializerResidual, mainInitializerResidual, ← Matrix.mul_assoc,
    gaussianInitializerProgram_projector_eq]

/-- Exact equality with the value returned by the executed arithmetic
program; in particular this equality has no probability or rank premise. -/
theorem gaussianInitializerProgram_value_eq_observable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ) :
    (gaussianInitializerProgram kernels T Ξ β).eval.value =
      mainInitializerObservable kernels T Ξ := by
  rw [(gaussianInitializerProgram kernels T Ξ β).eval.value_eq]
  simp only [initializerValue, mainInitializerObservable,
    gaussianInitializerProgram_residual_eq]

theorem gaussianInitializerProgram_value_eq_sqrt_sum
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ) :
    (gaussianInitializerProgram kernels T Ξ β).eval.value =
      Real.sqrt (∑ j, ∑ i, ((T-mainInitializerProjector kernels T Ξ*T) i j)^2) :=
  gaussianInitializerProgram_value_eq_observable kernels T Ξ β

theorem matrixFrobeniusValue_continuous {m n : ℕ} :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => matrixFrobeniusValue A) := by
  unfold matrixFrobeniusValue
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro i _
  exact (continuous_id.matrix_elem i j).pow 2

theorem mainInitializerProjector_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ =>
      mainInitializerProjector kernels x.1 x.2) :=
  (orthogonalRangeProgram_projector_measurable kernels).comp
    (continuous_fst.matrix_mul continuous_snd).measurable

theorem mainInitializerResidual_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ =>
      mainInitializerResidual kernels x.1 x.2) :=
  measurable_fst.sub ((mainInitializerProjector_joint_measurable kernels).mul measurable_fst)

theorem mainInitializerObservable_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ =>
      mainInitializerObservable kernels x.1 x.2) :=
  matrixFrobeniusValue_continuous.measurable.comp
    (mainInitializerResidual_joint_measurable kernels)

theorem gaussianInitializerProgram_value_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (β : ℝ) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ =>
      (gaussianInitializerProgram kernels x.1 x.2 β).eval.value) := by
  simpa only [gaussianInitializerProgram_value_eq_observable] using
    mainInitializerObservable_joint_measurable (k:=k) (r:=r) kernels

theorem gaussianInitializerProgram_value_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (T : Core k) (β : ℝ) :
    Measurable (fun Ξ : Matrix (Fin k) (Fin r) ℝ =>
      (gaussianInitializerProgram kernels T Ξ β).eval.value) :=
  (gaussianInitializerProgram_value_joint_measurable kernels β).comp
    (measurable_const.prodMk measurable_id)

/-- Joint measurability in the core and the Gaussian array used by
`gaussianColumns`, with the initializer's actual executed value. -/
theorem gaussianInitializerProgram_value_gaussian_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (β : ℝ) :
    Measurable (fun x : Core k × (Fin r → Fin k → ℝ) =>
      (gaussianInitializerProgram kernels x.1 (columnsMatrix x.2) β).eval.value) := by
  have hcols : Continuous (fun G : Fin r → Fin k → ℝ => columnsMatrix G) := by
    apply continuous_matrix
    intro i j
    exact (continuous_apply i).comp (continuous_apply j)
  exact (gaussianInitializerProgram_value_joint_measurable kernels β).comp
    (measurable_fst.prodMk (hcols.measurable.comp measurable_snd))

theorem gaussianInitializerProgram_value_gaussian_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (T : Core k) (β : ℝ) :
    Measurable (fun G : Fin r → Fin k → ℝ =>
      (gaussianInitializerProgram kernels T (columnsMatrix G) β).eval.value) :=
  (gaussianInitializerProgram_value_gaussian_joint_measurable kernels β).comp
    (measurable_const.prodMk measurable_id)

end
end HierarchicalAbsoluteSpectral
