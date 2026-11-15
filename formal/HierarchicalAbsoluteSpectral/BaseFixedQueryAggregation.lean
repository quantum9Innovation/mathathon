import HierarchicalAbsoluteSpectral.BaseMainFlexibleTotalCost
import HierarchicalAbsoluteSpectral.BaseFixedRangeCost
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeBudget

/-! Numerical aggregation for the executed query and finite core. The
outer degree weights only the recursive matrix actions. Core factorizations,
exact tests, range algebra and output formation remain additive. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
variable {n m p r L : ℕ}

/-- Intermediate numerical bounds on actual count formulas. The action
budget is already multiplied by the real outer-degree envelope E; this
preserves the weighted refinement telescoping estimate. -/
structure FixedFlexibleQueryEnvelope
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck exponent E A B : ℝ) : Prop where
  degree_positive : 1 ≤ E
  action_degree : E ≤ A
  core_positive : 1 ≤ B
  factor : E*(mainFactorActionCost kernels I S C (r+1) L:ℝ) ≤ A
  true_action : E*(mainTrueActionCost kernels I S C (r+1):ℝ) ≤ A
  core_kernel : E*((kernels C.pair.dimension C.pair.dimension (r+1)).cost:ℝ) ≤ A
  block_entries : E*(C.pair.dimension:ℝ)*(r+1:ℕ) ≤ A
  base : (baseConstructionCost kernels C.pair.dimension (I.accuracy 0)
    (I.accuracy_positive 0 (by omega)):ℝ) ≤ B
  core_envelope : (kernelEnvelope kernels C.pair.dimension:ℝ) ≤ B
  square_entries : (C.pair.dimension:ℝ)*C.pair.dimension ≤ B
  query_range : ∀ hr : r < C.pair.dimension,
    (R C.pair.dimension ((mainQueryDegree I S C hr+1)*(r+1)):ℝ) ≤ B
  test : (⌈212*(Ck+1)*(C.pair.dimension:ℝ)^exponent⌉₊:ℝ) ≤ B
  query_degree : ∀ hr : r < C.pair.dimension, (mainQueryDegree I S C hr:ℝ) ≤ E

theorem FixedFlexibleQueryEnvelope.action_positive
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck exponent E A B : ℝ)
    (h : FixedFlexibleQueryEnvelope kernels R I S C Ck exponent E A B) : 1 ≤ A :=
  h.degree_positive.trans h.action_degree

theorem FixedFlexibleQueryEnvelope.threshold_action
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck exponent E A B : ℝ)
    (h : FixedFlexibleQueryEnvelope kernels R I S C Ck exponent E A B) :
    E*(mainThresholdActionCost kernels I S C (r+1):ℝ) ≤ 4*A := by
  have hf := h.factor
  have ht := h.true_action
  have hb := h.block_entries
  unfold mainThresholdActionCost
  push_cast at hb
  push_cast
  nlinarith

theorem FixedFlexibleQueryEnvelope.trial_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck exponent E A B : ℝ)
    (h : FixedFlexibleQueryEnvelope kernels R I S C Ck exponent E A B)
    (hr : r < C.pair.dimension) :
    (mainFlexibleQueryTrialCap kernels R I S C hr Ck exponent:ℝ) ≤ 22*A+5*B := by
  have hE := h.degree_positive
  have hq := h.query_degree hr
  have hf := (le_mul_of_one_le_left (Nat.cast_nonneg
    (mainFactorActionCost kernels I S C (r+1) L)) hE).trans h.factor
  have hk := (le_mul_of_one_le_left (Nat.cast_nonneg
    (kernels C.pair.dimension C.pair.dimension (r+1)).cost) hE).trans h.core_kernel
  have hT := h.threshold_action kernels R I S C Ck exponent E A B
  have hcoef : 3*(mainQueryDegree I S C hr:ℝ)+2 ≤ 5*E := by linarith
  have hm := mul_le_mul_of_nonneg_right hcoef
    (Nat.cast_nonneg (mainThresholdActionCost kernels I S C (r+1)))
  have hpower : (3*(mainQueryDegree I S C hr:ℝ)+2)*
      (mainThresholdActionCost kernels I S C (r+1):ℝ) ≤ 20*A := by nlinarith
  have hR := h.query_range hr
  have henv := h.core_envelope
  have htest := h.test
  unfold mainFlexibleQueryTrialCap
  push_cast
  linarith

/-- The degree does not multiply the core/range/test term B. -/
theorem FixedFlexibleQueryEnvelope.query_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck exponent E A B : ℝ)
    (h : FixedFlexibleQueryEnvelope kernels R I S C Ck exponent E A B)
    (hr : r < C.pair.dimension) :
    (mainFlexibleQueryWorkCap kernels R I S C hr Ck exponent:ℝ) ≤
      80*((I.repetitions:ℝ)+1)*(A+B) := by
  have ht := h.trial_work kernels R I S C Ck exponent E A B hr
  have hmul := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg I.repetitions)
  have hb := h.base
  have hs := h.square_entries
  have hq := (h.query_degree hr).trans h.action_degree
  have hA := h.action_positive kernels R I S C Ck exponent E A B
  have hB := h.core_positive
  have hrep := Nat.cast_nonneg (α:=ℝ) I.repetitions
  unfold mainFlexibleQueryWorkCap
  push_cast
  nlinarith

/-- Aggregation of the literal initialized core and capped search. The
extra output and strong-program bounds are numerical caller lemmas, which
are discharged from the concrete output compiler in the final theorem. -/
theorem fixedFlexibleCoreWorkCap_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (Ck exponent E A B O : ℝ)
    (h : FixedFlexibleQueryEnvelope kernels R I S C Ck exponent E A B)
    (hO : 0 ≤ O)
    (hpsd : (psdGramCost kernels r:ℝ) ≤ B)
    (hdimension : (C.pair.dimension:ℝ) ≤ B)
    (hexact : (mainExactOutputWorkCap kernels I S C:ℝ) ≤ O)
    (hstrong : ∀ hk : 1 ≤ C.pair.dimension,
      (mainStrongWorkCap kernels I S C hk:ℝ) ≤ 100*(A+B+O)) :
    (mainCoreWorkCapWithQuery kernels I S C
      (fun hr => mainFlexibleQueryWorkCap kernels R I S C hr Ck exponent):ℝ) ≤
        1000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*(A+B+O) := by
  have hA := h.action_positive kernels R I S C Ck exponent E A B
  have hB := h.core_positive
  have hW : 1 ≤ A+B+O := by linarith
  have hrep : 1 ≤ (I.repetitions:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) I.repetitions; linarith
  have hcap : 1 ≤ (I.queryCap:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) I.queryCap; linarith
  have hrepW := mul_le_mul_of_nonneg_right hrep (by linarith : 0 ≤ A+B+O)
  have hcapW := mul_le_mul_of_nonneg_left hrepW (Nat.cast_nonneg I.queryCap)
  by_cases hr : C.pair.dimension ≤ r
  · simp only [mainCoreWorkCapWithQuery,dif_pos hr]
    calc
      _ ≤ O := hexact
      _ ≤ _ := by
        have hbig := mul_le_mul_of_nonneg_left hrepW (by linarith : 0 ≤ (I.queryCap:ℝ)+1)
        nlinarith
  · have hrl : r < C.pair.dimension := Nat.lt_of_not_ge hr
    have hk : 1 ≤ C.pair.dimension := by omega
    have hq := h.query_work kernels R I S C Ck exponent E A B hrl
    have hq' : (mainFlexibleQueryWorkCap kernels R I S C hrl Ck exponent:ℝ) ≤
        80*((I.repetitions:ℝ)+1)*(A+B+O) :=
      hq.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have hquery := mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg I.queryCap)
    have hs := hstrong hk
    have henv := h.core_envelope
    have hsq := h.square_entries
    have hi : ((5*kernelEnvelope kernels C.pair.dimension+psdGramCost kernels r+
        3*C.pair.dimension*C.pair.dimension+C.pair.dimension+10:ℕ):ℝ) ≤ 20*B := by
      push_cast
      linarith
    simp only [mainCoreWorkCapWithQuery,dif_neg hr]
    push_cast at hi ⊢
    nlinarith

/-- The same aggregation bounds the actual executed core on every tape. -/
theorem fixedFlexibleCoreProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (hR : ∀ a b (Y : Matrix (Fin a) (Fin b) ℝ), 1 ≤ a →
      (orthogonalRangeProgram kernels Y).work ≤ R a b)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (g : MainRandomTape I) (E A B O : ℝ)
    (h : FixedFlexibleQueryEnvelope kernels R I S C Ck exponent E A B)
    (hO : 0 ≤ O) (hpsd : (psdGramCost kernels r:ℝ) ≤ B)
    (hdimension : (C.pair.dimension:ℝ) ≤ B)
    (hexact : (mainExactOutputWorkCap kernels I S C:ℝ) ≤ O)
    (hstrong : ∀ hk : 1 ≤ C.pair.dimension,
      (mainStrongWorkCap kernels I S C hk:ℝ) ≤ 100*(A+B+O)) :
    ((mainCoreProgram kernels I S C g).work:ℝ) ≤
      1000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*(A+B+O) := by
  have hc := mainCoreProgram_work_bound_of_query kernels I S C g
    (fun hr => mainFlexibleQueryWorkCap kernels R I S C hr Ck exponent)
    (fun hr number t => mainPositiveQueryProgram_work_bound_flexible kernels R hR Ck exponent hC hexponent hK
      I S C hr t (mainQueryArray I S C g number) (mainInertiaArray I S C g number))
  exact (Nat.cast_le.mpr hc).trans
    (fixedFlexibleCoreWorkCap_bound kernels R I S C Ck exponent E A B O h hO hpsd hdimension hexact hstrong)

end
end HierarchicalAbsoluteSpectral
