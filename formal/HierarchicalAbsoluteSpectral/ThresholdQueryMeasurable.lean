import HierarchicalAbsoluteSpectral.ThresholdKrylovJointMeasurable
import HierarchicalAbsoluteSpectral.ThresholdQueryProgram

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix WithLp MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k r : ℕ}
local instance queryMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance queryMatrixBorelInstance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩
attribute [local irreducible] krylovSpanProjector krylovRitzFixedMatrix

theorem columnsMatrix_continuous :
    Continuous (fun G : Fin r → Fin k → ℝ => columnsMatrix G) := by
  apply continuous_matrix
  intro i j
  exact (continuous_apply i).comp (continuous_apply j)

def gaussianRitzObservable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (q : ℕ) (j : Fin k) :
    ({T : Core k // T.IsHermitian} × Core k) × (Fin r → Fin k → ℝ) → ℝ :=
  fun x => krylovRitzObservable kernels q j (x.1.1,x.1.2ᵀ*columnsMatrix x.2)

theorem gaussianRitzObservable_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (q : ℕ) (j : Fin k) : Measurable (gaussianRitzObservable (r:=r) kernels q j) := by
  have ht : Measurable (fun x : ({T : Core k // T.IsHermitian} × Core k) × (Fin r → Fin k → ℝ) =>
      x.1.1) := measurable_fst.fst
  have hs : Measurable (fun x : ({T : Core k // T.IsHermitian} × Core k) × (Fin r → Fin k → ℝ) =>
      x.1.2ᵀ*columnsMatrix x.2) :=
    (continuous_fst.snd.matrix_transpose.matrix_mul (columnsMatrix_continuous.comp continuous_snd)).measurable
  exact (krylovRitzValue_joint_measurable (r:=r) kernels q j).comp (ht.prodMk hs)

theorem gaussianRitzObservable_eq_computed (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.IsHermitian) (actions : ∀ b, MatrixAction T b)
    (q : ℕ) (S : Core k) (G : Fin r → Fin k → ℝ) (j : Fin k) :
    gaussianRitzObservable kernels q j ((⟨T,hT⟩,S),G) =
      computedKrylovRitzValue kernels T hT actions q S G j :=
  (computedKrylovRitzValue_eq_fixed kernels T hT actions q S G j).symm

def ritzFailureSet (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (q : ℕ) (j : Fin k) (ε : ℝ) :
    Set (({T : Core k // T.IsHermitian} × Core k) × (Fin r → Fin k → ℝ)) :=
  {x | gaussianRitzObservable kernels q j x <
    (1-ε)*(orderedEigenvalue x.1.1.val x.1.1.property j)^2}

theorem ritzFailureSet_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (q : ℕ) (j : Fin k) (ε : ℝ) : MeasurableSet (ritzFailureSet (r:=r) kernels q j ε) := by
  have ht : Measurable (fun x : ({T : Core k // T.IsHermitian} × Core k) × (Fin r → Fin k → ℝ) =>
      orderedEigenvalue x.1.1.val x.1.1.property j) :=
    (orderedEigenvalue_measurable j).comp measurable_fst.fst
  exact measurableSet_lt (gaussianRitzObservable_measurable kernels q j) (measurable_const.mul (ht.pow_const 2))

theorem ritzFailureSet_fiber_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (hT : T.PosSemidef) (actions : ∀ b, MatrixAction T b)
    (S Sinv : Core k) (hSinv : Sinv*S = 1) (j : Fin k)
    (htarget : 0 < orderedEigenvalue T hT.isHermitian j)
    (a b U β ε : ℝ) (ha : 0 < a) (hInv : ‖Sinv‖ ≤ 1/a)
    (hS : ‖S‖ ≤ b) (hba : b/a ≤ U) (hU : 1 ≤ U)
    (hβ : 0 < β) (hβ' : β ≤ 1) (hε : 0 < ε) (hε' : ε ≤ 1) (q : ℕ)
    (hstop : 10*gaussianCaptureRadius k U β/ε ≤ strongFilterDenominator (ε/100) q) :
    (gaussianColumns k (j.val+1)).real {G |
      ((⟨T,hT.isHermitian⟩,S),G) ∈ ritzFailureSet kernels q j ε} ≤ β := by
  apply le_trans (measureReal_mono (s₂ := krylovCaptureBad T hT.isHermitian S j a β) ?_ (by finiteness))
    (krylovCaptureBad_probability T hT.isHermitian S Sinv hSinv j a β ha hInv hβ hβ')
  intro G hG
  by_contra hgood
  have hh := computedKrylovRitzValue_of_not_bad kernels T hT actions S j htarget
    a b U β ε ha hS hba hU hβ hβ' hε hε' q hstop G hgood
  have hbad : computedKrylovRitzValue kernels T hT.isHermitian actions q S G j <
      (1-ε)*(orderedEigenvalue T hT.isHermitian j)^2 := by
    simpa only [ritzFailureSet,Set.mem_setOf_eq,gaussianRitzObservable_eq_computed kernels T hT.isHermitian actions] using hG
  exact (not_lt_of_ge hh) hbad

end
end HierarchicalAbsoluteSpectral
