import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSupport

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem exactGramAppendixSupportCompressionProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    (k m : ℕ) (D : Core k) (hD : Dᵀ = D) (hm : 1 ≤ m) (hkm : k ≤ m) :
    ((exactGramAppendixSupportCompressionProgram kernels k D hD).work:ℝ) ≤
      26*(C+1)*(m:ℝ)^q := by
  cases k with
  | zero => simp only [exactGramAppendixSupportCompressionProgram, work_pure, Nat.cast_zero]; positivity
  | succ k =>
      apply (inertiaSupportProgram_work_bound kernels C q hC hq hK D hD (by omega)).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkm) (by linarith)

/-- Only the true two Gram products involve the physical dimensions. All
remaining support algebra is bounded by the fast core cost, including
deficient factors and the zero product. -/
theorem exactGramAppendixSupportProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q)
    {n m p : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (hm : 1 ≤ m) :
    ((exactGramAppendixSupportProgram kernels A B).work:ℝ) ≤
      ((kernels m n m).cost:ℝ)+((kernels m p m).cost:ℝ)+40*(C+1)*(m:ℝ)^q := by
  have hk' : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N →
      a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^q :=
    fun a b c N _ => hK a b c N
  have hpsd (D : Core m) (hD : D.PosSemidef) :
      ((psdGramProgram kernels m D hD).work:ℝ) ≤ 9*(C+1)*(m:ℝ)^q := by
    apply le_trans _ (psdGramCost_bound kernels C q hC hq hk' m hm)
    exact_mod_cast psdGramProgram_work_le kernels m D hD
  have hsmall (a b c : ℕ) (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m) :
      ((kernels a b c).cost:ℝ) ≤ C*(m:ℝ)^q := hK a b c m hm ha hb hc
  have hcomp (k : ℕ) (D : Core k) (hD : Dᵀ = D) (hk : k ≤ m) :=
    exactGramAppendixSupportCompressionProgram_work_bound kernels C q hC hq hK k m D hD hm hk
  simp only [exactGramAppendixSupportProgram, work_bind, certify_work,
    ArithmeticKernel.program_work, work_pure, Nat.cast_add, Nat.cast_zero]
  calc
    _ ≤ ((kernels m n m).cost:ℝ)+(9*(C+1)*(m:ℝ)^q+
        (((kernels m p m).cost:ℝ)+(C*(m:ℝ)^q+(C*(m:ℝ)^q+
          (26*(C+1)*(m:ℝ)^q+(C*(m:ℝ)^q+(C*(m:ℝ)^q+0))))))) := by
      gcongr
      all_goals first | exact hpsd _ _ | apply hcomp | apply hsmall
      all_goals first | rfl | exact PSDGramPair.dimension_le_fin _ |
        exact (InertiaSupport.dimension_le _).trans (PSDGramPair.dimension_le_fin _)
    _ ≤ _ := by
      have hpow := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ m) q
      nlinarith

end
end HierarchicalAbsoluteSpectral
