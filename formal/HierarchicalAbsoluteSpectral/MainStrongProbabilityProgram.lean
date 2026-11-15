import HierarchicalAbsoluteSpectral.MainStrongProbabilityAlgebra

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Polynomial
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n m p r L : ℕ}

theorem FixedProblem.singleFailure_positive (I : FixedProblem n m p r L) : 0 < I.singleFailure :=
  div_pos I.delta_positive (by norm_num)

theorem FixedProblem.singleFailure_le_one (I : FixedProblem n m p r L) : I.singleFailure ≤ 1 := by
  unfold FixedProblem.singleFailure
  linarith [I.delta_lt_one]

theorem FixedProblem.alpha_le_one (I : FixedProblem n m p r L) : I.alpha ≤ 1 := by
  have hh := I.final_budget.alpha_small
  change I.alpha ≤ _ at hh
  linarith

abbrev mainStrongCoreProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :=
  let base := mainStrongBase kernels I S C t
  strongProjectionOutputProgram kernels I.A I.B
    (mainCarriedAction kernels I S C t.val base r) (mainPhysicalMapAction kernels I S C t.val base r)
    (mainConditionBound I) I.singleFailure I.alpha hk (mainConditionBound_ge_one I)
    I.singleFailure_positive I.singleFailure_le_one I.alpha_positive I.alpha_le_one (columnsMatrix G)

theorem mainStrongThresholdProgram_eval (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (mainStrongThresholdProgram kernels I S C hk t G).eval =
      (mainStrongCoreProgram kernels I S C hk t G).eval := by
  have hc : (mainConditionProgram I).certify.eval =
      ⟨mainConditionBound I,(mainConditionProgram_eval I).symm⟩ :=
    Subtype.ext ((certify_eval _).trans (mainConditionProgram_eval I))
  unfold mainStrongThresholdProgram
  simp only [eval_bind]
  erw [hc]

def mainStrongPhysicalPolynomial (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) : Matrix (Fin n) (Fin r) ℝ :=
  let base := mainStrongBase kernels I S C t
  let v := strongGaussianDegree C.pair.dimension (mainConditionBound I) I.singleFailure I.alpha hk
    (mainConditionBound_ge_one I) I.singleFailure_positive I.singleFailure_le_one I.alpha_positive I.alpha_le_one
  (supportLeftFactor I.A S.initialA C.pair*base.metricFactor.upperᵀ)*
    (aeval (mainCarriedMatrix I S C t.val base) (strongFilterPolynomial I.alpha v)*columnsMatrix G)

theorem mainStrongPhysicalPolynomial_eq_automatic
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    let base := mainStrongBase kernels I S C t
    mainStrongPhysicalPolynomial kernels I S C hk t G =
      (supportLeftFactor I.A S.initialA C.pair*base.metricFactor.upperᵀ)*
        (aeval (mainCarriedMatrix I S C t.val base) (strongFilterPolynomial I.alpha
          (automaticStrongPhysicalRangeProgram kernels (mainCarriedAction kernels I S C t.val base r)
            (mainPhysicalMapAction kernels I S C t.val base r) (mainConditionBound I)
            I.singleFailure I.alpha hk (mainConditionBound_ge_one I) I.singleFailure_positive
            I.singleFailure_le_one I.alpha_positive I.alpha_le_one (columnsMatrix G)).eval.1)*columnsMatrix G) := by
  dsimp only
  rw [automaticStrongPhysicalRangeProgram_degree]
  rfl

end
end HierarchicalAbsoluteSpectral
