import HierarchicalAbsoluteSpectral.MainStrongProbabilityObservable
import HierarchicalAbsoluteSpectral.MainStrongProbability

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Polynomial
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}
local instance strongMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance strongMatrixBorelInstance (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

theorem mainStrongBase_inverse_continuous (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    Continuous (fun t : {t : ℝ // 0 < t} => (mainStrongBase kernels I S C t).inverseFactor) :=
  coarseBaseProgram_inverseFactor_continuous kernels C.rightGram C.rightGram_posSemidef
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))

theorem mainStrongBase_upper_continuous (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    Continuous (fun t : {t : ℝ // 0 < t} => (mainStrongBase kernels I S C t).metricFactor.upper) := by
  have hh := continuous_matrix_inverse _ (mainStrongBase_inverse_continuous kernels I S C)
    (fun t => isUnit_iff_ne_zero.mp (mainStrongBase kernels I S C t).inverseFactor_isUnit)
  have he : (fun t : {t : ℝ // 0 < t} => (mainStrongBase kernels I S C t).inverseFactor⁻¹) =
      (fun t => (mainStrongBase kernels I S C t).metricFactor.upper) := by
    funext t
    exact mainBase_inverse_eq_upper I S C t.val _
  rwa [he] at hh

theorem mainStrongRefinedFactor_continuous (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    Continuous (fun t : {t : ℝ // 0 < t} => mainRefinedFactor I S C t.val (mainStrongBase kernels I S C t)) := by
  unfold mainRefinedFactor
  apply hierarchicalInverseFactor_continuous _ _ _ (mainStrongBase_inverse_continuous kernels I S C)
  intro j
  change Continuous (fun t : {t : ℝ // 0 < t} =>
    t.val • constructedNeumannMass (mainFineGram S C (j+1)) (safeAccuracy I (j+1)/100) _-
      mainFineRightGram S C (j+1))
  exact (continuous_subtype_val.smul continuous_const).sub continuous_const

theorem mainStrongCarriedMatrix_continuous (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) :
    Continuous (fun t : {t : ℝ // 0 < t} => mainCarriedMatrix I S C t.val (mainStrongBase kernels I S C t)) := by
  have hR := mainStrongBase_inverse_continuous kernels I S C
  have hU := mainStrongBase_upper_continuous kernels I S C
  have hF := mainStrongRefinedFactor_continuous kernels I S C
  have hK : Continuous (fun t : {t : ℝ // 0 < t} => mainTruePencil I S C t.val) :=
    (continuous_subtype_val.smul continuous_const).sub continuous_const
  exact continuous_const.sub ((((hR.matrix_transpose.matrix_mul hK).matrix_mul hF).matrix_mul
    hF.matrix_transpose).matrix_mul hU.matrix_transpose)

theorem mainStrongPhysicalPolynomial_joint_continuous (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) :
    Continuous (fun x : {t : ℝ // 0 < t} × (Fin r → Fin C.pair.dimension → ℝ) =>
      mainStrongPhysicalPolynomial kernels I S C hk x.1 x.2) := by
  have hL : Continuous (fun t : {t : ℝ // 0 < t} =>
      supportLeftFactor I.A S.initialA C.pair*(mainStrongBase kernels I S C t).metricFactor.upperᵀ) :=
    continuous_const.matrix_mul (mainStrongBase_upper_continuous kernels I S C).matrix_transpose
  have hV := mainStrongCarriedMatrix_continuous kernels I S C
  let v := strongGaussianDegree C.pair.dimension (mainConditionBound I) I.singleFailure I.alpha hk
    (mainConditionBound_ge_one I) I.singleFailure_positive I.singleFailure_le_one I.alpha_positive I.alpha_le_one
  exact (hL.comp continuous_fst).matrix_mul
    (((strongFilterPolynomial I.alpha v).continuous_aeval.comp (hV.comp continuous_fst)).matrix_mul
      (columnsMatrix_continuous.comp continuous_snd))

theorem mainStrongProductObservable_joint_measurable (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) :
    Measurable (fun x : {t : ℝ // 0 < t} × (Fin r → Fin C.pair.dimension → ℝ) =>
      mainStrongProductObservable kernels I S C hk x.1 x.2) := by
  have hp := (orthogonalRangeProgram_projector_measurable (k:=n) (r:=r) kernels).comp
    (mainStrongPhysicalPolynomial_joint_continuous kernels I S C hk).measurable
  have hc : Continuous (fun P : Core n => P*(I.A*I.B)) := continuous_id.matrix_mul continuous_const
  exact hc.measurable.comp hp

theorem mainStrongThresholdProgram_error_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) :
    MeasurableSet {x : {t : ℝ // 0 < t} × (Fin r → Fin C.pair.dimension → ℝ) |
      ‖I.A*I.B-(mainStrongThresholdProgram kernels I S C hk x.1 x.2).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} := by
  simp only [mainStrongThresholdProgram_product_eq_observable]
  exact measurableSet_le (measurable_const.sub
    (mainStrongProductObservable_joint_measurable kernels I S C hk)).norm measurable_const

theorem mainStrongThresholdProgram_error_probability
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (hg : MainSketchGood I S)
    (C : MainSupportData S) (hr : r < C.pair.dimension) (hk : 1 ≤ C.pair.dimension)
    (t : {t : ℝ // 0 < t})
    (htarget : orderedEigenvalue (mainThresholdOperator I S C t.val (mainStrongBase kernels I S C t))
      (mainThresholdOperator_isHermitian I S C t.val _) ⟨r,hr⟩ ≤ 1+I.alpha)
    (htail : t.val ≤ ((1+I.nearTolerance)/(1-I.nearTolerance))*(1/(1-I.massAccuracy))*
      (tailSingularValue (I.A*I.B) r)^2) :
    (gaussianColumns C.pair.dimension r).real {G |
      ‖I.A*I.B-(mainStrongThresholdProgram kernels I S C hk t G).eval.product‖ ≤
        (1+I.theta)*tailSingularValue (I.A*I.B) r} ≥ 1-I.singleFailure := by
  obtain ⟨E,hEm,hEp,hE⟩ := mainStrongThresholdProgram_good_event kernels I S hg C hr hk t htarget htail
  exact hEp.trans (measureReal_mono (fun G hG => (hE G hG).2))

end
end HierarchicalAbsoluteSpectral
