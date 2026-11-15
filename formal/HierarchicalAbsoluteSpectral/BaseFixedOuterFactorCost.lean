import HierarchicalAbsoluteSpectral.BaseFixedFactorCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
variable {n m p r L : ℕ}

def fixedOuterAccuracyConstant (I : FixedProblem n m p r L) : ℝ :=
  200*fixedOuterLogBudget I*Real.sqrt (1000000*(hierarchyConstant L+1))+1

theorem fixedOuterAccuracyConstant_ge_one (I : FixedProblem n m p r L) :
    1 ≤ fixedOuterAccuracyConstant I := by
  have hlog := fixedOuterLogBudget_ge_one I
  have hroot := Real.sqrt_nonneg (1000000*(hierarchyConstant L+1))
  unfold fixedOuterAccuracyConstant
  nlinarith

theorem fixedOuterDegreeEnvelope_ge_one (I : FixedProblem n m p r L) :
    1 ≤ fixedOuterDegreeEnvelope I := by
  have hlog := fixedOuterLogBudget_ge_one I
  have hα := I.alpha_positive
  unfold fixedOuterDegreeEnvelope
  have hh : 0 ≤ 200*fixedOuterLogBudget I/Real.sqrt I.alpha := by positivity
  linarith

theorem fixedOuterDegreeEnvelope_le_accuracy_constant (I : FixedProblem n m p r L) :
    fixedOuterDegreeEnvelope I ≤ fixedOuterAccuracyConstant I*Real.sqrt (I.accuracy L/I.theta) := by
  have hratio : 1 ≤ I.accuracy L/I.theta :=
    (le_div_iff₀ I.theta_positive).mpr (by simpa only [one_mul] using I.theta_le_last)
  have hroot : 1 ≤ Real.sqrt (I.accuracy L/I.theta) := by
    simpa using Real.sqrt_le_sqrt hratio
  rw [fixedOuterDegreeEnvelope_accuracy]
  unfold fixedOuterAccuracyConstant
  nlinarith only [hroot]

theorem sqrt_ratio_div_left (H θ : ℝ) (hH : 0 < H) (hθ : 0 < θ) :
    Real.sqrt (H/θ)/H=1/Real.sqrt (H*θ) := by
  have hrootH : Real.sqrt H≠0 := (Real.sqrt_pos.mpr hH).ne'
  have hrootθ : Real.sqrt θ≠0 := (Real.sqrt_pos.mpr hθ).ne'
  rw [Real.sqrt_div hH.le,Real.sqrt_mul hH.le]
  field_simp
  nlinarith [Real.sq_sqrt hH.le]

/-- The polynomial degree times the *actual* recursively compiled factor
cost has exactly the fixed-depth fine-leaf weight `h_j/sqrt(h_L θ)`.
Its coefficient depends on depth and logarithms of supplied parameters. -/
theorem mainFactorActionCost_outer_degree_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ)
    (hA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1) :
    fixedOuterDegreeEnvelope I*(mainFactorActionCost K I S C b L:ℝ) ≤
      (42*fixedOuterAccuracyConstant I*fixedFineLog I*(fixedRefinementCostMultiplier I)^L/
        Real.sqrt (I.accuracy L*I.theta))*fixedFineProductSum K I S b := by
  have hfactor := mainFactorActionCost_fine_sum K I S C b hA hB
  have hH := I.accuracy_positive L le_rfl
  have hθ := I.theta_positive
  have hscale := fixedOuterAccuracyConstant_ge_one I
  have hfactor0 : (0:ℝ) ≤ mainFactorActionCost K I S C b L := Nat.cast_nonneg _
  have hdegree := mul_le_mul_of_nonneg_right (fixedOuterDegreeEnvelope_le_accuracy_constant I) hfactor0
  have hmul := mul_le_mul_of_nonneg_left hfactor
    (show 0≤fixedOuterAccuracyConstant I*Real.sqrt (I.accuracy L/I.theta)/I.accuracy L by positivity)
  calc
    _ ≤ fixedOuterAccuracyConstant I*Real.sqrt (I.accuracy L/I.theta)*
        (mainFactorActionCost K I S C b L:ℝ) := hdegree
    _ = (fixedOuterAccuracyConstant I*Real.sqrt (I.accuracy L/I.theta)/I.accuracy L)*
        (I.accuracy L*(mainFactorActionCost K I S C b L:ℝ)) := by field_simp
    _ ≤ (fixedOuterAccuracyConstant I*Real.sqrt (I.accuracy L/I.theta)/I.accuracy L)*
        (42*fixedFineLog I*(fixedRefinementCostMultiplier I)^L*fixedFineProductSum K I S b) := hmul
    _ = fixedOuterAccuracyConstant I*(Real.sqrt (I.accuracy L/I.theta)/I.accuracy L)*
        (42*fixedFineLog I*(fixedRefinementCostMultiplier I)^L*fixedFineProductSum K I S b) := by ring
    _ = _ := by rw [sqrt_ratio_div_left _ _ hH hθ]; ring

theorem mainActualFactorActionCost_outer_degree_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I)
    (C : MainSupportData (mainSketchProgram I g).eval) (b : ℕ) :
    fixedOuterDegreeEnvelope I*(mainFactorActionCost K I (mainSketchProgram I g).eval C b L:ℝ) ≤
      (42*fixedOuterAccuracyConstant I*fixedFineLog I*(fixedRefinementCostMultiplier I)^L/
        Real.sqrt (I.accuracy L*I.theta))*fixedFineProductSum K I (mainSketchProgram I g).eval b :=
  mainFactorActionCost_outer_degree_bound K I _ C b
    (fun j _ => mainSketchProgram_core_le_rowsA I g _) (fun j _ => mainSketchProgram_core_le_rowsB I g _)

end
end HierarchicalAbsoluteSpectral
