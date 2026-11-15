import HierarchicalAbsoluteSpectral.BaseKernelCosts
import HierarchicalAbsoluteSpectral.BaseStoredActionCost
import HierarchicalAbsoluteSpectral.BaseFixedActionCost
import HierarchicalAbsoluteSpectral.MainSketchRows

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {n m p r L k b s t : ℕ}

theorem storedCongruenceGramAction_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (F : Matrix (Fin s) (Fin m) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (hk : k ≤ m) (hs : m ≤ s) :
    (storedCongruenceGramAction (b:=b) K F U).cost ≤ 4*matrixProductCost K s m b := by
  have h1 := kernel_cost_le_matrixProductCost K k m b s m b (hk.trans hs) le_rfl le_rfl
  have h2 := kernel_cost_le_matrixProductCost K m s b m s b le_rfl le_rfl le_rfl
  rw [←matrixProductCost_swap K s m b] at h2
  have h3 := kernel_cost_le_matrixProductCost K s m b s m b le_rfl le_rfl le_rfl
  have h4 := kernel_cost_le_matrixProductCost K m k b s m b hs hk le_rfl
  rw [storedCongruenceGramAction_cost]
  omega

theorem storedFinePencilAction_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (U V : Matrix (Fin m) (Fin k) ℝ) (t0 ε : ℝ) (hε : 0 < ε)
    (hk : k ≤ m) (hs : m ≤ s) (ht : m ≤ t) :
    (storedFinePencilAction (b:=b) K HA HB U V t0 ε hε).cost ≤
      40*neumannCount ε hε*(matrixProductCost K s m b+matrixProductCost K t m b) := by
  have h0 := storedFinePencilAction_cost_neumann_bound (b:=b) K HA HB U V t0 ε hε
  have h1 := storedCongruenceGramAction_product_bound (b:=b) K HA V hk hs
  have h2 := storedCongruenceGramAction_product_bound (b:=b) K HB U hk ht
  have hscalar : k*b+1 ≤ matrixProductCost K s m b :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right b hk) 1).trans (matrixProductCost_scalar_floor K s m b)
  have hinner : (storedCongruenceGramAction (b:=b) K HA V).cost+
      (storedCongruenceGramAction (b:=b) K HB U).cost+k*b+1 ≤
        5*(matrixProductCost K s m b+matrixProductCost K t m b) := by omega
  have hmul := Nat.mul_le_mul_left (8*neumannCount ε hε) hinner
  exact h0.trans (hmul.trans_eq (by ring))

theorem storedFinePencilAction_product_log_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (U V : Matrix (Fin m) (Fin k) ℝ) (t0 ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hk : k ≤ m) (hs : m ≤ s) (ht : m ≤ t) :
    ((storedFinePencilAction (b:=b) K HA HB U V t0 ε hε).cost:ℝ) ≤
      40*(1+4*Real.log (1/ε))*(matrixProductCost K s m b+matrixProductCost K t m b) := by
  have h0 : ((storedFinePencilAction (b:=b) K HA HB U V t0 ε hε).cost:ℝ) ≤
      40*(neumannCount ε hε:ℝ)*(matrixProductCost K s m b+matrixProductCost K t m b) := by
    exact_mod_cast storedFinePencilAction_product_bound (b:=b) K HA HB U V t0 ε hε hk hs ht
  exact h0.trans (by gcongr; exact neumannCount_bound ε hε hε1)

def mainFineProductCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : StoredSketches n m p L) (j b : ℕ) : ℕ :=
  matrixProductCost K (S.levelA (safeSketchIndex L (j+1))).1 m b+
    matrixProductCost K (S.levelB (safeSketchIndex L (j+1))).1 m b

def mainInputProductCost (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (n m p b : ℕ) : ℕ :=
  matrixProductCost K n m b+matrixProductCost K p m b

def mainFineNeumannLog (I : FixedProblem n m p r L) (j : ℕ) : ℝ :=
  1+4*Real.log (1/(safeAccuracy I (j+1)/100))

theorem mainFineNeumannLog_ge_one (I : FixedProblem n m p r L) (j : ℕ) :
    1 ≤ mainFineNeumannLog I j := by
  have hh := safeAccuracy_pos I (j+1)
  have hb := I.accuracy_bounded (min (j+1) L) (min_le_right _ _)
  change safeAccuracy I (j+1) ≤ _ at hb
  have hε : 0 < safeAccuracy I (j+1)/100 := by positivity
  have hInv : 1 ≤ 1/(safeAccuracy I (j+1)/100) :=
    (le_div_iff₀ hε).mpr (by linarith)
  have hlog := Real.log_nonneg hInv
  dsimp [mainFineNeumannLog]
  linarith

theorem mainFineActionCost_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (j b : ℕ)
    (hA : m ≤ (S.levelA (safeSketchIndex L (j+1))).1)
    (hB : m ≤ (S.levelB (safeSketchIndex L (j+1))).1) :
    (mainFineActionCost K I S C j b:ℝ) ≤ 40*mainFineNeumannLog I j*mainFineProductCost K S j b := by
  have hh := safeAccuracy_pos I (j+1)
  have hb := I.accuracy_bounded (min (j+1) L) (min_le_right _ _)
  change safeAccuracy I (j+1) ≤ _ at hb
  have hε : 0 < safeAccuracy I (j+1)/100 := by positivity
  have hε1 : safeAccuracy I (j+1)/100 < 1 := by linarith
  simpa only [mainFineActionCost,mainFinePencilAction,MatrixAction.castMatrix,mainFineNeumannLog,
    mainFineProductCost,Nat.cast_add] using
    storedFinePencilAction_product_log_bound (b:=b) K
      (S.levelA (safeSketchIndex L (j+1))).2 (S.levelB (safeSketchIndex L (j+1))).2
      C.pair.factor C.pair.leftInverseᵀ 0 _ hε hε1 C.pair.dimension_le_fin hA hB

theorem mainTrueActionCost_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S) (b : ℕ) :
    (mainTrueActionCost K I S C b:ℝ) ≤
      40*(1+4*Real.log (1/I.massAccuracy))*mainInputProductCost K n m p b := by
  have hε := I.final_budget.mass_positive
  have hε1 : I.massAccuracy < 1 := by
    have hh := I.final_budget.mass_floor
    change I.massAccuracy ≤ I.accuracy L/100 at hh
    have hb := I.accuracy_bounded L le_rfl
    linarith
  simpa only [mainTrueActionCost,mainTruePencilAction,MatrixAction.castMatrix,mainInputProductCost,FixedProblem.massAccuracy,
    Nat.cast_add] using storedFinePencilAction_product_log_bound (b:=b) K I.A I.Bᵀ C.pair.factor C.pair.leftInverseᵀ
      0 _ hε hε1 C.pair.dimension_le_fin I.core_le_rows I.core_le_cols

theorem mainActualFineActionCost_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (g : MainRandomTape I)
    (C : MainSupportData (mainSketchProgram I g).eval) (j b : ℕ) :
    (mainFineActionCost K I (mainSketchProgram I g).eval C j b:ℝ) ≤
      40*mainFineNeumannLog I j*mainFineProductCost K (mainSketchProgram I g).eval j b :=
  mainFineActionCost_product_bound K I _ C j b
    (mainSketchProgram_core_le_rowsA I g _) (mainSketchProgram_core_le_rowsB I g _)

end
end HierarchicalAbsoluteSpectral
