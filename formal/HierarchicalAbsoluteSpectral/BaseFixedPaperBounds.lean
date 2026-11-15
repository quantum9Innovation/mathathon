import HierarchicalAbsoluteSpectral.BaseFixedPaperData

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped BigOperators
variable {n m p r L : ℕ}

theorem fixedPaperFineSum_nonneg (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (b : ℕ) : 0 ≤ fixedPaperFineSum K I b := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (I.accuracy_positive j (by have hh:=Finset.mem_range.mp hj; omega)).le (Nat.cast_nonneg _)

theorem fixedPaperCoefficient_nonneg (I : FixedProblem n m p r L) :
    0 ≤ fixedPaperFineCoefficient I ∧ 0 ≤ fixedPaperInputCoefficient I := by
  have hs:=fixedOuterAccuracyConstant_ge_one I
  have hf:=fixedFineLog_ge_one I
  have hr:=fixedRefinementCostMultiplier_ge_one I
  have ht:=fixedTrueNeumannLog_ge_one I
  constructor <;> dsimp [fixedPaperFineCoefficient,fixedPaperInputCoefficient] <;> positivity

theorem fixedPaperWidePenalty_nonneg (I : FixedProblem n m p r L) : 0 ≤ fixedPaperWidePenalty I := by
  unfold fixedPaperWidePenalty
  split_ifs <;> positivity

theorem fixedPaperMainTerm_components
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (exponent : ℝ) (I : FixedProblem n m p r L) :
    let T := fixedPaperMainTerm K exponent I
    0 ≤ T ∧ (m*(n+p):ℕ) ≤ T ∧ (fixedCoarseProductCost K I:ℝ) ≤ T ∧
      (m:ℝ)^exponent ≤ T ∧
      Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ) ≤ T ∧
      fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta) ≤ T ∧
      (matrixProductCost K n r p:ℝ) ≤ T ∧ fixedPaperWidePenalty I ≤ T := by
  intro T
  have hi : (0:ℝ)≤(m*(n+p):ℕ) := Nat.cast_nonneg _
  have hg : (0:ℝ)≤(fixedCoarseProductCost K I:ℝ) := Nat.cast_nonneg _
  have hc : (0:ℝ)≤(m:ℝ)^exponent := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ha : (0:ℝ)≤Real.sqrt (I.accuracy L/I.theta)*(mainInputProductCost K n m p (r+1):ℝ) := by positivity
  have hf : (0:ℝ)≤fixedPaperFineSum K I (r+1)/Real.sqrt (I.accuracy L*I.theta) :=
    div_nonneg (fixedPaperFineSum_nonneg K I _) (Real.sqrt_nonneg _)
  have hn : (0:ℝ)≤(n*p:ℕ) := Nat.cast_nonneg _
  have ho : (0:ℝ)≤(matrixProductCost K n r p:ℝ) := Nat.cast_nonneg _
  have hw := fixedPaperWidePenalty_nonneg I
  dsimp [T,fixedPaperMainTerm]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem fixedPaperCoreBudget_bound (Ck exponent : ℝ) (hC : 0 ≤ Ck) (I : FixedProblem n m p r L) :
    fixedPaperCoreBudget Ck exponent I ≤
      (311*(Ck+1)*baseFixedInitialLog I)*(m:ℝ)^exponent+22*fixedPaperWidePenalty I := by
  have hlog:=baseFixedInitialLog_ge_one I
  have hcore : 0 ≤ (Ck+1)*(m:ℝ)^exponent := by positivity
  have hm := mul_le_mul_of_nonneg_right hlog hcore
  unfold fixedPaperCoreBudget fixedQueryRangeBudget fixedPaperWidePenalty
  split_ifs <;> nlinarith

theorem fixedPaperActionCoreOutput_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (Ck exponent : ℝ) (hC : 0 ≤ Ck)
    (I : FixedProblem n m p r L) :
    fixedPaperActionBudget K I+fixedPaperCoreBudget Ck exponent I+(matrixProductCost K n r p:ℝ) ≤
      fixedPaperWorkCoefficient Ck I*fixedPaperMainTerm K exponent I := by
  let T := fixedPaperMainTerm K exponent I
  have hc:=fixedPaperMainTerm_components K exponent I
  have hfcoef: 0 ≤ fixedPaperFineCoefficient I := (fixedPaperCoefficient_nonneg I).1
  have hacoef: 0 ≤ fixedPaperInputCoefficient I := (fixedPaperCoefficient_nonneg I).2
  have hlog:=baseFixedInitialLog_ge_one I
  have hcc: 0 ≤ 311*(Ck+1)*baseFixedInitialLog I := by positivity
  have h1 := mul_le_mul_of_nonneg_left hc.2.2.2.2.2.1 hfcoef
  have h2 := mul_le_mul_of_nonneg_left hc.2.2.2.2.1 hacoef
  have h3 := mul_le_mul_of_nonneg_left hc.2.2.2.1 hcc
  have h4 := mul_le_mul_of_nonneg_left hc.2.2.2.2.2.2.2 (by norm_num : (0:ℝ)≤22)
  have h5 := hc.2.2.2.2.2.2.1
  have hB := fixedPaperCoreBudget_bound Ck exponent hC I
  unfold fixedPaperActionBudget fixedPaperWorkCoefficient
  change _ ≤ (fixedPaperFineCoefficient I+fixedPaperInputCoefficient I+
    311*(Ck+1)*baseFixedInitialLog I+23)*T
  nlinarith only [h1,h2,h3,h4,h5,hB]

def fixedPaperPreprocessWork (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) : ℝ :=
  (Fintype.card (MainGaussianIndex n m p r L I.queryCap I.repetitions):ℝ)+
    (4*(L:ℝ)+3*I.queryCap+2*I.repetitions+29)+(mainSketchProgram I g).work+
      (coarseSupportProgram K (mainSketchProgram I g).eval.initialA (mainSketchProgram I g).eval.initialB).work

theorem fixedPaperPreprocessWork_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (Ck exponent : ℝ) (hC : 0 < Ck) (he : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    fixedPaperPreprocessWork K I g ≤ fixedPaperPreparationCoefficient Ck I*fixedPaperMainTerm K exponent I := by
  let T := fixedPaperMainTerm K exponent I
  let P := (m:ℝ)^exponent
  let V : ℝ := m*(n+p)
  let D : ℝ := 2+4*(I.queryCap:ℝ)*I.repetitions
  let S : ℝ := 4*(L:ℝ)+3*I.queryCap+2*I.repetitions+29
  have hm : 1 ≤ m := I.rank_positive.trans I.rank_le_core
  have hpow : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hm) (by linarith)
  have hsquare : (m:ℝ)*m ≤ P := baseFixedCore_square_bound exponent he m m hm le_rfl
  have hc:=fixedPaperMainTerm_components K exponent I
  have hV : V ≤ T := by simpa only [V,Nat.cast_mul,Nat.cast_add] using hc.2.1
  have hP : P ≤ T := hc.2.2.2.1
  have hG : (fixedCoarseProductCost K I:ℝ) ≤ T := hc.2.2.1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hDraw : (Fintype.card (MainGaussianIndex n m p r L I.queryCap I.repetitions):ℝ) ≤
      6*(L+1:ℕ)*V+D*(m:ℝ)*m := by
    have hh := mainGaussianDrawCount_input_core_bound I
    dsimp [D,V]
    exact_mod_cast hh
  have hDrawCore := mul_le_mul_of_nonneg_left hsquare hD
  have hDrawR : (Fintype.card (MainGaussianIndex n m p r L I.queryCap I.repetitions):ℝ) ≤
      6*(L+1:ℕ)*V+D*P := by nlinarith only [hDraw,hDrawCore]
  have hSketch : ((mainSketchProgram I g).work:ℝ) ≤ (fixedSketchLogFactor I:ℝ)*V := by
    have hh:=mainSketchProgram_work_input_log_bound I g
    dsimp [V]
    exact_mod_cast hh
  have hSupport := mainCoarseSupportProgram_work_core_bound K Ck exponent hC he hK I (mainSketchProgram I g).eval
  have hGram := mainActualCoarseGramCost_le_static K I g
  have hSupport' : ((coarseSupportProgram K (mainSketchProgram I g).eval.initialA
      (mainSketchProgram I g).eval.initialB).work:ℝ) ≤ (fixedCoarseProductCost K I:ℝ)+11*(Ck+1)*P := by
    dsimp only [P]
    linarith
  have hDrawI := mul_le_mul_of_nonneg_left hV (show (0:ℝ)≤6*(L+1:ℕ) by positivity)
  have hDrawP := mul_le_mul_of_nonneg_left hP hD
  have hScalarP := mul_le_mul_of_nonneg_left hpow hS
  have hScalarT := mul_le_mul_of_nonneg_left hP hS
  have hSketchT := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg (fixedSketchLogFactor I))
  have hSupportT := mul_le_mul_of_nonneg_left hP (show 0≤11*(Ck+1) by positivity)
  unfold fixedPaperPreprocessWork fixedPaperPreparationCoefficient
  change _ ≤ (1+(fixedSketchLogFactor I:ℝ)+6*(L+1:ℕ)+D+S+11*(Ck+1))*T
  nlinarith only [hDrawR,hDrawI,hDrawP,hScalarP,hScalarT,hSketch,hSketchT,hSupport',hSupportT,hG]

theorem preparedFixedDepthTotalWork_decompose
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (I : FixedProblem n m p r L) (g : MainRandomTape I) :
    (preparedFixedDepthTotalWork K I g:ℝ)=fixedPaperPreprocessWork K I g+
      (mainCoreProgram K I (mainSketchProgram I g).eval
        (coarseSupportProgram K (mainSketchProgram I g).eval.initialA (mainSketchProgram I g).eval.initialB).eval g).work := by
  unfold preparedFixedDepthTotalWork mainRandomizedWork
  rw [preparedFixedDepthProgram_work]
  simp only [fixedDepthProgram,ArithmeticProgram.work_bind]
  unfold fixedPaperPreprocessWork
  push_cast
  ring

end
end HierarchicalAbsoluteSpectral
