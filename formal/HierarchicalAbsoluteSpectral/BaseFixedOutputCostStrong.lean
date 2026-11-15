import HierarchicalAbsoluteSpectral.BaseFixedOutputCost
import HierarchicalAbsoluteSpectral.BaseCost

/-! The strong output degree multiplies action costs alone. Base/core
factorizations and dense output remain additive. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {n m p r L : ℕ}

def fixedOutputBaseLog (I : FixedProblem n m p r L) : ℝ :=
  1+4*Real.log (1/(4*I.accuracy 0))

theorem fixedOutputBaseLog_ge_one (I : FixedProblem n m p r L) :
    1 ≤ fixedOutputBaseLog I := by
  have hh := I.accuracy_positive 0 (by omega)
  have hinv : (1:ℝ) ≤ 1/(4*I.accuracy 0) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith [I.initial_accuracy_le])
  have hlog := Real.log_nonneg hinv
  dsimp [fixedOutputBaseLog]
  linarith

theorem fixedOutputCoreCost_ge_one (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (m : ℕ) (hm : 1 ≤ m) : 1 ≤ fixedOutputCoreCost Ck p0 m := by
  have hpow := Real.one_le_rpow (by exact_mod_cast hm : (1:ℝ) ≤ m) (by linarith : 0 ≤ p0)
  dsimp [fixedOutputCoreCost]
  nlinarith

theorem fixedOutputCoreCost_square (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (k m : ℕ) (hm : 1 ≤ m) (hkm : k ≤ m) :
    (k:ℝ)*k ≤ fixedOutputCoreCost Ck p0 m := by
  have hsq : (m:ℝ)^2 ≤ (m:ℝ)^p0 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm : (1:ℝ) ≤ m) hp
  have hkk : (k:ℝ)*k ≤ (m:ℝ)*m := by exact_mod_cast Nat.mul_le_mul hkm hkm
  have hpow : 0 ≤ (m:ℝ)^p0 := Real.rpow_nonneg (Nat.cast_nonneg _) _
  dsimp [fixedOutputCoreCost]
  nlinarith

theorem mainOutputCoreKernel_le_input
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (b : ℕ) (hb : b ≤ r+1) :
    (K C.pair.dimension C.pair.dimension b).cost ≤ fixedOutputInputCost K n m p r := by
  have hh := kernel_cost_le_matrixProductCost K C.pair.dimension C.pair.dimension b n m (r+1)
    (C.pair.dimension_le_fin.trans I.core_le_rows) C.pair.dimension_le_fin hb
  dsimp [fixedOutputInputCost]
  omega

theorem mainOutputSupportKernel_le_input
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (b : ℕ) (hb : b ≤ r+1) :
    (K m C.pair.dimension b).cost ≤ fixedOutputInputCost K n m p r := by
  have hh := kernel_cost_le_matrixProductCost K m C.pair.dimension b n m (r+1)
    I.core_le_rows C.pair.dimension_le_fin hb
  dsimp [fixedOutputInputCost]
  omega

theorem mainOutputPhysicalKernel_le_input
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n m p r b : ℕ) (hb : b ≤ r+1) :
    (K n m b).cost ≤ fixedOutputInputCost K n m p r := by
  have hh := kernel_cost_le_matrixProductCost K n m b n m (r+1) le_rfl le_rfl hb
  dsimp [fixedOutputInputCost]
  omega

theorem mainOutputBlock_le_input
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (S : StoredSketches n m p L) (C : MainSupportData S) (r b : ℕ) (hb : b ≤ r+1) :
    C.pair.dimension*b ≤ fixedOutputInputCost K n m p r := by
  have hh := fixedOutputInputCost_block_floor K n m p r
  have hmul := Nat.mul_le_mul C.pair.dimension_le_fin hb
  omega

theorem mainOutputBaseOverhead_numeric
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) :
    (baseConstructionCost K C.pair.dimension (I.accuracy 0)
      (I.accuracy_positive 0 (by omega)):ℝ)+2*(C.pair.dimension:ℝ)*C.pair.dimension+7 ≤
        49*fixedOutputBaseLog I*fixedOutputCoreCost Ck p0 m := by
  have hK' : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0 :=
    fun a b c N _ hN ha hb hc => hK a b c N hN ha hb hc
  have hb := baseConstructionCost_bound K Ck p0 hC hp hK' C.pair.dimension hk
    (I.accuracy 0) (I.accuracy_positive 0 (by omega)) I.initial_accuracy_le
  have hpow : (C.pair.dimension:ℝ)^p0 ≤ (m:ℝ)^p0 :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast C.pair.dimension_le_fin) (by linarith)
  have hlog := fixedOutputBaseLog_ge_one I
  have hbase : (baseConstructionCost K C.pair.dimension (I.accuracy 0)
      (I.accuracy_positive 0 (by omega)):ℝ) ≤
        40*fixedOutputBaseLog I*fixedOutputCoreCost Ck p0 m := by
    calc
      _ ≤ 40*(Ck+1)*(C.pair.dimension:ℝ)^p0*fixedOutputBaseLog I := hb
      _ ≤ 40*(Ck+1)*(m:ℝ)^p0*fixedOutputBaseLog I :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by linarith)
      _ = _ := by dsimp [fixedOutputCoreCost]; ring
  have hB := fixedOutputCoreCost_ge_one Ck p0 hC hp m (I.rank_positive.trans I.rank_le_core)
  have hsq := fixedOutputCoreCost_square Ck p0 hC hp C.pair.dimension m
    (I.rank_positive.trans I.rank_le_core) C.pair.dimension_le_fin
  have hBL := mul_le_mul_of_nonneg_right hlog (by linarith : 0 ≤ fixedOutputCoreCost Ck p0 m)
  nlinarith

theorem mainStrongOutputCap_numeric
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (F T : ℝ)
    (hF : (mainFactorActionCost K I S C r L:ℝ) ≤ F)
    (hT : (mainTrueActionCost K I S C r:ℝ) ≤ T) :
    (mainStrongOutputCap K I S C hk:ℝ) ≤
      ((mainStrongDegree I S C hk:ℝ)+1)*
        (2*F+T+40*(fixedOutputInputCost K n m p r:ℝ))+
          9*fixedOutputCoreCost Ck p0 m+(matrixProductCost K n r p:ℝ) := by
  let A : ℝ := fixedOutputInputCost K n m p r
  let B := fixedOutputCoreCost Ck p0 m
  let O : ℝ := matrixProductCost K n r p
  let v : ℝ := mainStrongDegree I S C hk
  have hA : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast fixedOutputInputCost_ge_one K n m p r
  have hv : 0 ≤ v := Nat.cast_nonneg _
  have hcore : ((K C.pair.dimension C.pair.dimension r).cost:ℝ) ≤ A := by
    dsimp [A]
    exact_mod_cast mainOutputCoreKernel_le_input K I S C r (by omega)
  have hsup : ((K m C.pair.dimension r).cost:ℝ) ≤ A := by
    dsimp [A]
    exact_mod_cast mainOutputSupportKernel_le_input K I S C r (by omega)
  have hphys : ((K n m r).cost:ℝ) ≤ A := by
    dsimp [A]
    exact_mod_cast mainOutputPhysicalKernel_le_input K n m p r r (by omega)
  have hblock : (C.pair.dimension:ℝ)*r ≤ A := by
    dsimp [A]
    exact_mod_cast mainOutputBlock_le_input K S C r r (by omega)
  have hcarried : (mainCarriedActionCost K I S C r:ℝ) ≤ 2*F+T+3*A := by
    unfold mainCarriedActionCost
    push_cast
    linarith
  have hprod := mul_le_mul_of_nonneg_left
    (show (mainCarriedActionCost K I S C r:ℝ)+6*(C.pair.dimension:ℝ)*r ≤ 2*F+T+9*A by
      linarith) (show 0 ≤ v+1 by linarith)
  have hX : (matrixProductCost K n m (r+1):ℝ) ≤ A := by
    dsimp [A]
    exact_mod_cast (show matrixProductCost K n m (r+1) ≤ fixedOutputInputCost K n m p r from by
      dsimp [fixedOutputInputCost]; omega)
  have hrange : (exactRangeWorkCap K n r:ℝ) ≤ 2*A+9*B := by
    have hh := exactRangeWorkCap_product_bound K Ck p0 hC hp hK n m r r I.rank_le_core le_rfl
    dsimp [B]
    linarith
  have hout : (projectionOutputWorkCap K n m p r:ℝ) ≤ A+O := by
    dsimp [A,O]
    exact_mod_cast projectionOutputWorkCap_product_bound K n m p r
  have hbudget : (mainStrongOutputCap K I S C hk:ℝ) ≤
      7*v+23+(v+1)*(2*F+T+9*A)+7*A+9*B+O := by
    dsimp only [mainStrongOutputCap]
    push_cast
    change 4*v+14+(9+3*v+(v+1)*((mainCarriedActionCost K I S C r:ℝ)+
      6*(C.pair.dimension:ℝ)*r)+(C.pair.dimension:ℝ)*r+
      (K n m r).cost+(K m C.pair.dimension r).cost+
      (K C.pair.dimension C.pair.dimension r).cost+exactRangeWorkCap K n r)+
      projectionOutputWorkCap K n m p r ≤ _
    linarith only [hprod,hblock,hphys,hsup,hcore,hrange,hout]
  have hvA : v ≤ v*A := by nlinarith [mul_le_mul_of_nonneg_left hA hv]
  change _ ≤ (v+1)*(2*F+T+40*A)+9*B+O
  nlinarith only [hbudget,hvA,hv,hA]

/-- Numeric strong bound with only intermediate factor/true-action bounds
as inputs. Core factorization and dense output are outside the degree. -/
theorem mainStrongWorkCap_numeric
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (F T : ℝ)
    (hF : (mainFactorActionCost K I S C r L:ℝ) ≤ F)
    (hT : (mainTrueActionCost K I S C r:ℝ) ≤ T) :
    (mainStrongWorkCap K I S C hk:ℝ) ≤
      ((mainStrongDegree I S C hk:ℝ)+1)*
        (2*F+T+40*(fixedOutputInputCost K n m p r:ℝ))+
          60*fixedOutputBaseLog I*fixedOutputCoreCost Ck p0 m+
            (matrixProductCost K n r p:ℝ) := by
  have hb := mainOutputBaseOverhead_numeric K Ck p0 hC hp hK I S C hk
  have hs := mainStrongOutputCap_numeric K Ck p0 hC hp hK I S C hk F T hF hT
  have hlog := fixedOutputBaseLog_ge_one I
  have hB := fixedOutputCoreCost_ge_one Ck p0 hC hp m (I.rank_positive.trans I.rank_le_core)
  have hBL := mul_le_mul_of_nonneg_right hlog (by linarith : 0 ≤ fixedOutputCoreCost Ck p0 m)
  unfold mainStrongWorkCap
  push_cast
  nlinarith only [hb,hs,hBL]

theorem mainStrongWorkCap_fixed_numeric
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (F T : ℝ)
    (hF : (mainFactorActionCost K I S C r L:ℝ) ≤ F)
    (hT : (mainTrueActionCost K I S C r:ℝ) ≤ T) :
    (mainStrongWorkCap K I S C hk:ℝ) ≤
      ((fixedOuterDegreeCap I:ℝ)+1)*(2*F+T+40*(fixedOutputInputCost K n m p r:ℝ))+
        60*fixedOutputBaseLog I*fixedOutputCoreCost Ck p0 m+(matrixProductCost K n r p:ℝ) := by
  have hh := mainStrongWorkCap_numeric K Ck p0 hC hp hK I S C hk F T hF hT
  have hv : (mainStrongDegree I S C hk:ℝ) ≤ fixedOuterDegreeCap I := by
    exact_mod_cast mainStrongDegree_le_fixed_cap I S C hk
  have hF0 : 0 ≤ F := (Nat.cast_nonneg _).trans hF
  have hT0 : 0 ≤ T := (Nat.cast_nonneg _).trans hT
  have hm := mul_le_mul_of_nonneg_right (add_le_add_right hv 1)
    (show 0 ≤ 2*F+T+40*(fixedOutputInputCost K n m p r:ℝ) by positivity)
  linarith

theorem mainStrongThresholdProgram_work_numeric
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((K a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hk : 1 ≤ C.pair.dimension) (t : {t : ℝ // 0 < t})
    (G : Fin r → Fin C.pair.dimension → ℝ) (F T : ℝ)
    (hF : (mainFactorActionCost K I S C r L:ℝ) ≤ F)
    (hT : (mainTrueActionCost K I S C r:ℝ) ≤ T) :
    ((mainStrongThresholdProgram K I S C hk t G).work:ℝ) ≤
      ((fixedOuterDegreeCap I:ℝ)+1)*(2*F+T+40*(fixedOutputInputCost K n m p r:ℝ))+
        60*fixedOutputBaseLog I*fixedOutputCoreCost Ck p0 m+(matrixProductCost K n r p:ℝ) := by
  have hh : ((mainStrongThresholdProgram K I S C hk t G).work:ℝ) ≤ mainStrongWorkCap K I S C hk := by
    exact_mod_cast mainStrongThresholdProgram_work_bound K I S C hk t G
  exact hh.trans (mainStrongWorkCap_fixed_numeric K Ck p0 hC hp hK I S C hk F T hF hT)

end
end HierarchicalAbsoluteSpectral
