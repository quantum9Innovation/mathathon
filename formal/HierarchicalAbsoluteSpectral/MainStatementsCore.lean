import HierarchicalAbsoluteSpectral.MainOperatorProgram
import HierarchicalAbsoluteSpectral.MainStatementsStrong
import HierarchicalAbsoluteSpectral.MainStatementsExact
import HierarchicalAbsoluteSpectral.ThresholdQueryAutomatic
import HierarchicalAbsoluteSpectral.BaseColumnBlocks

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L : ℕ}

def mainConditionBound (I : FixedProblem n m p r L) : ℝ :=
  (1+hierarchyUpper 0/(8*I.accuracy L))*(1+hierarchyUpper L/(8*I.accuracy 0))

theorem mainConditionBound_ge_one (I : FixedProblem n m p r L) : 1 ≤ mainConditionBound I := by
  have h0 := I.accuracy_positive 0 (by omega)
  have hL := I.accuracy_positive L le_rfl
  have hB0 := hierarchyUpper_nonneg 0
  have hBL := hierarchyUpper_nonneg L
  have ha : 0 ≤ hierarchyUpper 0/(8*I.accuracy L) := by positivity
  have hb : 0 ≤ hierarchyUpper L/(8*I.accuracy 0) := by positivity
  unfold mainConditionBound
  nlinarith [mul_nonneg ha hb]

def mainConditionProgram (I : FixedProblem n m p r L) : ArithmeticProgram ℝ := do
  let a ← mul 8 (I.accuracy L)
  let b ← div (hierarchyUpper 0) a
  let c ← add 1 b
  let d ← mul 8 (I.accuracy 0)
  let e ← div (hierarchyUpper L) d
  let f ← add 1 e
  mul c f

@[simp] theorem mainConditionProgram_eval (I : FixedProblem n m p r L) :
    (mainConditionProgram I).eval = mainConditionBound I := by simp [mainConditionProgram,mainConditionBound]

theorem mainConditionProgram_admissible (I : FixedProblem n m p r L) :
    (mainConditionProgram I).admissible := by
  have h0 := I.accuracy_positive 0 (by omega)
  have hL := I.accuracy_positive L le_rfl
  simp [mainConditionProgram,ne_of_gt h0,ne_of_gt hL]

def mainSupportAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ) :
    MatrixAction (supportLeftFactor I.A S.initialA C.pair) b :=
  ((kernels n m b).action I.A).comp ((kernels m C.pair.dimension b).action C.pair.leftInverseᵀ)

def mainSourceFactor (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) : Core C.pair.dimension :=
  base.metricFactor.upper*mainRefinedFactor I S C t base

theorem mainBase_inverse_eq_upper (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) :
    base.inverseFactor⁻¹=base.metricFactor.upper :=
  Matrix.inv_eq_right_inv base.metricFactor.left_inverse

theorem mainSourceFactor_eq (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) :
    mainSourceFactor I S C t base=base.inverseFactor⁻¹*mainRefinedFactor I S C t base := by
  rw [mainBase_inverse_eq_upper]
  rfl

def mainSourceAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    MatrixAction (mainSourceFactor I S C t base)ᵀ b :=
  ((mainFactorActions kernels I S C t base b).transpose.comp
    ((kernels _ _ b).action base.metricFactor.upperᵀ)).castMatrix (by
      simp only [mainSourceFactor,Matrix.transpose_mul])

def mainCarriedMatrix (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) : Core C.pair.dimension :=
  1-base.inverseFactorᵀ*mainTruePencil I S C t*mainRefinedFactor I S C t base*
    (mainRefinedFactor I S C t base)ᵀ*base.metricFactor.upperᵀ

theorem mainCarriedMatrix_eq (I : FixedProblem n m p r L) (S : StoredSketches n m p L)
    (C : MainSupportData S) (t : ℝ) (base : MainBaseData I S C t) :
    mainCarriedMatrix I S C t base =
      carriedOperator (base.inverseFactorᵀ*mainTruePencil I S C t*base.inverseFactor)
        (mainSourceFactor I S C t base) := by
  have hleft : base.inverseFactor*base.metricFactor.upper=1 := base.metricFactor.left_inverse
  have he : (base.inverseFactorᵀ*mainTruePencil I S C t*base.inverseFactor)*
      (base.metricFactor.upper*mainRefinedFactor I S C t base)*
      (base.metricFactor.upper*mainRefinedFactor I S C t base)ᵀ =
      base.inverseFactorᵀ*mainTruePencil I S C t*(base.inverseFactor*base.metricFactor.upper)*
        mainRefinedFactor I S C t base*(mainRefinedFactor I S C t base)ᵀ*base.metricFactor.upperᵀ := by
    simp only [Matrix.transpose_mul,Matrix.mul_assoc]
  simp only [mainCarriedMatrix,carriedOperator,mainSourceFactor,he,hleft,Matrix.mul_one]

def mainCarriedAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    MatrixAction (mainCarriedMatrix I S C t base) b :=
  let p₀ := (kernels _ _ b).action base.inverseFactorᵀ
  let p₁ := p₀.comp (mainTruePencilAction kernels I S C t b)
  let p₂ := p₁.comp (mainFactorActions kernels I S C t base b).forward
  let p₃ := p₂.comp (mainFactorActions kernels I S C t base b).transpose
  (MatrixAction.identity _ b).sub (p₃.comp ((kernels _ _ b).action base.metricFactor.upperᵀ))

def mainPhysicalMapAction (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (t : ℝ) (base : MainBaseData I S C t) (b : ℕ) :
    MatrixAction (supportLeftFactor I.A S.initialA C.pair*base.metricFactor.upperᵀ) b :=
  (mainSupportAction kernels I S C b).comp ((kernels _ _ b).action base.metricFactor.upperᵀ)

theorem mainTruePencil_isHermitian (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ) :
    (mainTruePencil I S C t).IsHermitian := by
  have hG : (mainTrueGram I S C).IsHermitian := by
    have hh := (Matrix.posSemidef_conjTranspose_mul_self (I.A*C.pair.leftInverseᵀ)).isHermitian
    simpa only [mainTrueGram,Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc] using hh
  have hQ : (mainTrueRightGram I S C).IsHermitian := by
    have hh := (Matrix.posSemidef_conjTranspose_mul_self (I.Bᵀ*C.pair.factor)).isHermitian
    simpa only [mainTrueRightGram,Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc] using hh
  exact ((constructedNeumannMass_posDef _ hG I.massAccuracy I.final_budget.mass_positive).isHermitian.smul
    (by simp : star t=t)).sub hQ

theorem mainThresholdOperator_isHermitian (I : FixedProblem n m p r L)
    (S : StoredSketches n m p L) (C : MainSupportData S) (t : ℝ)
    (base : MainBaseData I S C t) : (mainThresholdOperator I S C t base).IsHermitian :=
  Matrix.isHermitian_one.sub (normalized_isHermitian _ _ (mainTruePencil_isHermitian I S C t).eq)

def mainPositiveQueryProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    ArithmeticProgram ThresholdDecision := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  let ε ← (div I.alpha 100).certify
  have hε : ε.val=I.alpha/100 := ε.property
  let actions := fun b => (mainThresholdAction kernels I S C t.val base (r+1)).columnBlocks (by omega) b
  automaticKrylovQueryProgram kernels (mainThresholdOperator I S C t.val base)
    (mainThresholdOperator_isHermitian I S C t.val base) actions
    (mainSourceFactor I S C t.val base) (mainSourceAction kernels I S C t.val base (r+1))
    ⟨r,hr⟩ bound.val ε.val (by omega)
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (by rw [hε]; exact div_pos I.alpha_positive (by norm_num))
    (by rw [hε]; have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    I.repetitions G g

def mainStrongThresholdProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) : ArithmeticProgram (FixedRankOutput n p r) := do
  let base ← coarseBaseProgram kernels C.rightGram C.rightGram_posSemidef t.val t.property
    (I.accuracy 0) (I.accuracy_positive 0 (by omega))
  let bound ← (mainConditionProgram I).certify
  strongProjectionOutputProgram kernels I.A I.B
    (mainCarriedAction kernels I S C t.val base r) (mainPhysicalMapAction kernels I S C t.val base r)
    bound.val I.singleFailure I.alpha hk
    (by rw [bound.property,mainConditionProgram_eval]; exact mainConditionBound_ge_one I)
    (div_pos I.delta_positive (by norm_num)) (by have := I.delta_lt_one; dsimp [FixedProblem.singleFailure]; linarith)
    I.alpha_positive (by have := I.final_budget.alpha_small; change I.alpha ≤ _ at this; linarith)
    (columnsMatrix G)

theorem mainPositiveQueryProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin I.repetitions → Fin (r+1) → Fin C.pair.dimension → ℝ)
    (g : Fin I.repetitions → Fin 2 → Fin (C.pair.dimension*C.pair.dimension) → ℝ) :
    (mainPositiveQueryProgram kernels I S C hr t G g).admissible := by
  simp only [mainPositiveQueryProgram,admissible_bind,coarseBaseProgram_admissible,
    certify_admissible,mainConditionProgram_admissible,admissible_div,
    automaticKrylovQueryProgram_admissible,true_and]
  norm_num

theorem mainStrongThresholdProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) :
    (mainStrongThresholdProgram kernels I S C hk t G).admissible := by
  simp only [mainStrongThresholdProgram,admissible_bind,coarseBaseProgram_admissible,
    certify_admissible,mainConditionProgram_admissible,strongProjectionOutputProgram_admissible,and_self]

end
end HierarchicalAbsoluteSpectral
