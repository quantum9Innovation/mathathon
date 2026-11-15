import HierarchicalAbsoluteSpectral.BaseFixedPaperBounds
import HierarchicalAbsoluteSpectral.BaseFixedQueryAggregationOutput
import HierarchicalAbsoluteSpectral.MainExplicitOutputCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
variable {n m p r L : ℕ}

/-- The original-input, prepared, finite randomized compiler satisfies
the paper's tradeoff with every fixed-depth logarithmic dependence shown.
This bound holds for every Gaussian tape, including every abort/zero branch. -/
theorem preparedFixedDepthTotalWork_paper_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (he : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (preparedFixedDepthTotalWork K I g:ℝ) ≤ fixedPaperPrefactor Ck I*fixedPaperMainTerm K exponent I := by
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram K S.initialA S.initialB).eval
  have hRowsA : ∀ j<L, m ≤ (S.levelA (safeSketchIndex L (j+1))).1 :=
    fun j _ => mainSketchProgram_core_le_rowsA I g _
  have hRowsB : ∀ j<L, m ≤ (S.levelB (safeSketchIndex L (j+1))).1 :=
    fun j _ => mainSketchProgram_core_le_rowsB I g _
  have hcore := fixedFlexibleCoreProgram_concrete_bound K hClassical Ck exponent hC he hK I S C hRowsA hRowsB g
  dsimp only [S,C] at hcore
  rw [mainActualActionBudget_static] at hcore
  change _ ≤ 11000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*
    (fixedPaperActionBudget K I+fixedPaperCoreBudget Ck exponent I+(matrixProductCost K n r p:ℝ)) at hcore
  have hpre := fixedPaperPreprocessWork_bound K Ck exponent hC he hK I g
  have hwork := fixedPaperActionCoreOutput_bound K Ck exponent hC.le I
  have hmul := mul_le_mul_of_nonneg_left hwork
    (show 0≤11000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1) by positivity)
  rw [preparedFixedDepthTotalWork_decompose]
  calc
    _ ≤ fixedPaperPreparationCoefficient Ck I*fixedPaperMainTerm K exponent I+
        11000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*
          (fixedPaperActionBudget K I+fixedPaperCoreBudget Ck exponent I+(matrixProductCost K n r p:ℝ)) :=
      add_le_add hpre hcore
    _ ≤ fixedPaperPreparationCoefficient Ck I*fixedPaperMainTerm K exponent I+
        11000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*
          (fixedPaperWorkCoefficient Ck I*fixedPaperMainTerm K exponent I) :=
      add_le_add (le_refl _) hmul
    _ = _ := by unfold fixedPaperPrefactor; ring

theorem fixedPaperMainTerm_narrow
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (exponent : ℝ) (I : FixedProblem n m p r L)
    (hwidth : fixedKrylovRawWidth I ≤ m) :
    fixedPaperMainTerm K exponent I=
      (m*(n+p):ℕ)+(fixedCoarseProductCost K I:ℝ)+(m:ℝ)^exponent+
        Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ)+
        fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta)+
        (n*p:ℕ)+(matrixProductCost K n r p:ℝ) := by
  simp only [fixedPaperMainTerm,fixedPaperWidePenalty,if_pos hwidth,add_zero]

theorem fixedPaperWidePenalty_le (I : FixedProblem n m p r L) :
    fixedPaperWidePenalty I ≤ (m:ℝ)*(fixedKrylovRawWidth I:ℝ)^2 := by
  unfold fixedPaperWidePenalty
  split_ifs
  · positivity
  · exact le_rfl

theorem preparedFixedDepthTotalWork_paper_narrow_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (he : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) (hwidth : fixedKrylovRawWidth I ≤ m) :
    (preparedFixedDepthTotalWork K I g:ℝ) ≤ fixedPaperPrefactor Ck I*
      ((m*(n+p):ℕ)+(fixedCoarseProductCost K I:ℝ)+(m:ℝ)^exponent+
        Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ)+
        fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta)+
        (n*p:ℕ)+(matrixProductCost K n r p:ℝ)) := by
  simpa only [fixedPaperMainTerm_narrow K exponent I hwidth] using
    preparedFixedDepthTotalWork_paper_bound K hClassical Ck exponent hC he hK I g

def fixedPaperExplicitPrefactor (Ck : ℝ) (I : FixedProblem n m p r L) : ℝ :=
  fixedPaperPrefactor Ck I+3

/-- The same tradeoff charges reading the original factors and writing
both returned factors and every entry of their explicit dense product. -/
theorem preparedFixedDepthExplicitWork_paper_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hClassical : ∀ a b c : ℕ, (K a b c).cost ≤ 2*a*b*c)
    (Ck exponent : ℝ) (hC : 0 < Ck) (he : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (preparedFixedDepthExplicitWork K I g:ℝ) ≤
      fixedPaperExplicitPrefactor Ck I*fixedPaperMainTerm K exponent I := by
  have hh := preparedFixedDepthTotalWork_paper_bound K hClassical Ck exponent hC he hK I g
  have hio := preparedFixedDepthExplicitWork_le K I g
  have hparts := fixedPaperMainTerm_components K exponent I
  have hnp : n*p ≤ matrixProductCost K n r p := by unfold matrixProductCost; nlinarith
  have hnpR : ((n*p:ℕ):ℝ) ≤ fixedPaperMainTerm K exponent I :=
    (Nat.cast_le.mpr hnp).trans hparts.2.2.2.2.2.2.1
  have hioN : preparedFixedDepthExplicitWork K I g ≤
      2*(m*(n+p))+n*p+preparedFixedDepthTotalWork K I g := by
    simpa only [Nat.mul_assoc] using hio
  have hioR : (preparedFixedDepthExplicitWork K I g:ℝ) ≤
      2*(m*(n+p):ℕ)+(n*p:ℕ)+(preparedFixedDepthTotalWork K I g:ℝ) := by exact_mod_cast hioN
  unfold fixedPaperExplicitPrefactor
  nlinarith only [hh,hioR,hnpR,hparts.2.1]

end
end HierarchicalAbsoluteSpectral
