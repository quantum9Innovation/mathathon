import HierarchicalAbsoluteSpectral.ThresholdKrylovMeasurable

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k r : ℕ}
local instance jointMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance jointMatrixBorelInstance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩
attribute [local irreducible] krylovSpanProjector krylovRitzFixedMatrix

theorem orderedEigenvalue_measurable_comp {X : Type*} [MeasurableSpace X]
    (f : X → Core k) (hf : Measurable f) (hHerm : ∀ x, (f x).IsHermitian) (j : Fin k) :
    Measurable (fun x => orderedEigenvalue (f x) (hHerm x) j) :=
  (orderedEigenvalue_measurable j).comp (hf.subtype_mk (h:=hHerm))

def krylovRitzObservable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (q : ℕ) (j : Fin k) :
    {T : Core k // T.IsHermitian} × Matrix (Fin k) (Fin r) ℝ → ℝ :=
  fun x => orderedEigenvalue (krylovRitzFixedMatrix kernels x.1.val q x.2)
    (krylovRitzFixedMatrix_isHermitian kernels x.1.val x.1.property q x.2) j

theorem krylovRitzValue_joint_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (q : ℕ) (j : Fin k) :
    Measurable (krylovRitzObservable (r:=r) kernels q j) := by
  have hp : Measurable (fun x : {T : Core k // T.IsHermitian} × Matrix (Fin k) (Fin r) ℝ =>
      (x.1.val,x.2)) := measurable_fst.subtype_coe.prodMk measurable_snd
  have hm : Measurable (fun x : {T : Core k // T.IsHermitian} × Matrix (Fin k) (Fin r) ℝ =>
      krylovRitzFixedMatrix kernels x.1.val q x.2) :=
    (krylovRitzFixedMatrix_measurable (k:=k) (r:=r) kernels q).comp hp
  exact orderedEigenvalue_measurable_comp
    (fun x : {T : Core k // T.IsHermitian} × Matrix (Fin k) (Fin r) ℝ =>
      krylovRitzFixedMatrix kernels x.1.val q x.2) hm
    (fun x => krylovRitzFixedMatrix_isHermitian kernels x.1.val x.1.property q x.2) j

end
end HierarchicalAbsoluteSpectral
