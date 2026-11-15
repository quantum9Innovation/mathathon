import HierarchicalAbsoluteSpectral.BaseFixedQueryAggregation

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
variable {n m p r L : ℕ}

/-- The actual positive-initializer branch has only logarithmic search and
repetition multipliers on core algebra and dense output. The polynomial
degree has already been absorbed solely into the weighted action budget A. -/
theorem fixedFlexibleBracketProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (R : ℕ → ℕ → ℕ)
    (hR : ∀ a b (Y : Matrix (Fin a) (Fin b) ℝ), 1 ≤ a →
      (orthogonalRangeProgram kernels Y).work ≤ R a b)
    (Ck exponent : ℝ) (hC : 0 < Ck) (hexponent : 2 ≤ exponent)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^exponent)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (g : MainRandomTape I) (lower upper E A B O : ℝ)
    (h : FixedFlexibleQueryEnvelope kernels R I S C Ck exponent E A B)
    (hO : 0 ≤ O)
    (hstrong : (mainStrongWorkCap kernels I S C (by omega):ℝ) ≤ 100*(A+B+O)) :
    ((mainBracketProgram kernels I S C hr g lower upper).work:ℝ) ≤
      1000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*(A+B+O) := by
  have hb := mainBracketProgram_work_bound_of_query kernels I S C hr g lower upper
    (mainFlexibleQueryWorkCap kernels R I S C hr Ck exponent)
    (fun number t => mainPositiveQueryProgram_work_bound_flexible kernels R hR Ck exponent hC hexponent hK
      I S C hr t (mainQueryArray I S C g number) (mainInertiaArray I S C g number))
  have hbR : ((mainBracketProgram kernels I S C hr g lower upper).work:ℝ) ≤
      12+(I.queryCap:ℝ)*(8+(mainFlexibleQueryWorkCap kernels R I S C hr Ck exponent:ℝ))+
        (mainStrongWorkCap kernels I S C (by omega):ℝ) := by exact_mod_cast hb
  have hq := h.query_work kernels R I S C Ck exponent E A B hr
  have hq' : (mainFlexibleQueryWorkCap kernels R I S C hr Ck exponent:ℝ) ≤
      80*((I.repetitions:ℝ)+1)*(A+B+O) :=
    hq.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hquery := mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg I.queryCap)
  have hA := h.action_positive kernels R I S C Ck exponent E A B
  have hB := h.core_positive
  have hW : 1 ≤ A+B+O := by linarith
  have hrep : 1 ≤ (I.repetitions:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) I.repetitions; linarith
  have hrepW := mul_le_mul_of_nonneg_right hrep (by linarith : 0 ≤ A+B+O)
  have hcapW := mul_le_mul_of_nonneg_left hrepW (Nat.cast_nonneg I.queryCap)
  nlinarith

end
end HierarchicalAbsoluteSpectral
