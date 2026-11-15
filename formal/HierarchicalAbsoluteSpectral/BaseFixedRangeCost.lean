import HierarchicalAbsoluteSpectral.BaseFixedDegreeCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
variable {n m p r L : ℕ}

theorem algebraRangeWorkCap_bound_size
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (a b N : ℕ) (hN : 1 ≤ N) (ha : a ≤ N) (hb : b ≤ N) (hmax : 1 ≤ max a b) :
    (algebraRangeWorkCap kernels a b:ℝ) ≤ 11*(Ck+1)*(N:ℝ)^p0 := by
  have hK' : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0 := fun a b c N _ hN ha hb hc => hK a b c N hN ha hb hc
  have henv := kernelEnvelope_bound kernels Ck p0 hC hK' (max a b) hmax
  have hpow : ((max a b:ℕ):ℝ)^p0 ≤ (N:ℝ)^p0 :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast max_le ha hb) (by linarith)
  have henv' : (kernelEnvelope kernels (max a b):ℝ) ≤ Ck*(N:ℝ)^p0 :=
    henv.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  have hpsd : (psdGramCost kernels b:ℝ) ≤ 9*(Ck+1)*(N:ℝ)^p0 := by
    by_cases hb1 : 1 ≤ b
    · apply (psdGramCost_bound kernels Ck p0 hC hp hK' b hb1).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hb) (by linarith)
    · have hb0 : b=0 := by omega
      rw [hb0,psdGramCost]
      simp only [Nat.cast_zero]
      positivity
  have hnp : 0 ≤ (N:ℝ)^p0 := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold algebraRangeWorkCap
  push_cast
  nlinarith

theorem rangeDeflationWorkCap_bound_narrow
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (a b N : ℕ) (hN : 1 ≤ N) (ha : a ≤ N) (hb : b ≤ N) (hmax : 1 ≤ max a b) :
    (rangeDeflationWorkCap kernels a b:ℝ) ≤ 11*(Ck+1)*(N:ℝ)^p0 := by
  exact (Nat.cast_le.mpr (min_le_left _ _)).trans
    (algebraRangeWorkCap_bound_size kernels Ck p0 hC hp hK a b N hN ha hb hmax)

theorem rangeDeflationWorkCap_bound_wide
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b N W : ℕ) (ha : a ≤ N) (hb : b ≤ W) :
    rangeDeflationWorkCap kernels a b ≤ 22*N*W*W := by
  apply (min_le_right _ _).trans
  gcongr

theorem mainQueryRangeCap_bound_narrow
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Ck p0 : ℝ) (hC : 0 < Ck) (hp : 2 ≤ p0)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ Ck*(N:ℝ)^p0)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) (hwidth : fixedKrylovRawWidth I ≤ m) :
    (rangeDeflationWorkCap kernels C.pair.dimension ((mainQueryDegree I S C hr+1)*(r+1)):ℝ) ≤
      11*(Ck+1)*(m:ℝ)^p0 :=
  rangeDeflationWorkCap_bound_narrow kernels Ck p0 hC hp hK _ _ m
    (I.rank_positive.trans I.rank_le_core) C.pair.dimension_le_fin
    ((mainKrylovRawWidth_le_fixed I S C hr).trans hwidth) (by omega)

theorem mainQueryRangeCap_bound_wide
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem n m p r L) (S : StoredSketches n m p L) (C : MainSupportData S)
    (hr : r < C.pair.dimension) :
    rangeDeflationWorkCap kernels C.pair.dimension ((mainQueryDegree I S C hr+1)*(r+1)) ≤
      22*m*fixedKrylovRawWidth I*fixedKrylovRawWidth I :=
  rangeDeflationWorkCap_bound_wide kernels _ _ _ _ C.pair.dimension_le_fin
    (mainKrylovRawWidth_le_fixed I S C hr)

end
end HierarchicalAbsoluteSpectral
