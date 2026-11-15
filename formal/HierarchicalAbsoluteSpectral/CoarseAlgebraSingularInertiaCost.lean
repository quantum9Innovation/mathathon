import HierarchicalAbsoluteSpectral.CoarseAlgebraSingularInertia

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n : ℕ}

theorem inertiaSupportProgram_work_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (D : Core n) (hD : Dᵀ = D) (hn : 1 ≤ n) :
    ((inertiaSupportProgram kernels D hD).work:ℝ) ≤ 26*(C+1)*(n:ℝ)^p := by
  have hk' : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p := fun a b c N _ => hK a b c N
  have hs := psdGramCost_bound kernels C p hC hp hk' n hn
  have he := kernelEnvelope_bound kernels C p hC hk' n hn
  have hsq : (n:ℝ)*(n:ℝ) ≤ (n:ℝ)^p := by
    simpa only [Real.rpow_two,pow_two] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n) hp
  have hb : ((inertiaSupportProgram kernels D hD).work:ℝ) ≤
      2*(psdGramCost kernels n:ℝ)+7*(kernelEnvelope kernels n:ℝ)+(n:ℝ)*(n:ℝ) := by
    exact_mod_cast inertiaSupportProgram_work_le kernels D hD hn
  have hnp := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ n) p
  nlinarith

theorem gaussianReducedInertiaProgram_work_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {D : Core n} (support : InertiaSupport D) (hD : Dᵀ = D) (hn : 1 ≤ n) (g : Fin (n*n) → ℝ) :
    ((gaussianReducedInertiaProgram kernels support hD g).work:ℝ) ≤ 24*(C+1)*(n:ℝ)^p := by
  have hk' : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p := fun a b c N _ => hK a b c N
  have ht : (fastLDLCost kernels support.dimension:ℝ) ≤ 18*(C+1)*(n:ℝ)^p := by
    by_cases hr : 1 ≤ support.dimension
    · apply (fastLDLCost_bound kernels C p hC hp hk' support.dimension hr).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast support.dimension_le) (by linarith)
    · have hz : support.dimension = 0 := by omega
      rw [hz,fastLDLCost]
      simp only [Nat.cast_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hk := hK support.dimension support.dimension support.dimension n hn
    support.dimension_le support.dimension_le support.dimension_le
  have hsq : (n:ℝ)*(n:ℝ) ≤ (n:ℝ)^p := by
    simpa only [Real.rpow_two,pow_two] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n) hp
  have hr : (support.dimension:ℝ) ≤ (n:ℝ)^p := by
    have hdim : (support.dimension:ℝ) ≤ n := by exact_mod_cast support.dimension_le
    have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hb : ((gaussianReducedInertiaProgram kernels support hD g).work:ℝ) ≤
      (fastLDLCost kernels support.dimension:ℝ)+5*((kernels support.dimension support.dimension support.dimension).cost:ℝ)+support.dimension := by
    exact_mod_cast congruenceInertiaProgram_work_le kernels support.compressed
      (support.compressed_transpose hD) ((gaussianSquareMatrix n g).submatrix
        (Fin.castLEEmb support.dimension_le) (Fin.castLEEmb support.dimension_le))
  have hnp := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ n) p
  nlinarith

theorem singularInertiaProgram_work_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N → ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (D : Core n) (hD : Dᵀ = D) (hn : 1 ≤ n) (g : Fin (n*n) → ℝ) :
    ((singularInertiaProgram kernels n D hD g).work:ℝ) ≤ 100*(C+1)*(n:ℝ)^p := by
  let support := (inertiaSupportProgram kernels D hD).eval
  have hs := inertiaSupportProgram_work_bound kernels C p hC hp hK D hD hn
  have hg := gaussianReducedInertiaProgram_work_bound kernels C p hC hp hK support hD hn g
  have hk := hK n n n n hn le_rfl le_rfl le_rfl
  have hnp := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ n) p
  simp only [singularInertiaProgram,work_bind,Nat.cast_add]
  split
  · simp only [work_pure,Nat.cast_zero]
    nlinarith
  · simp only [work_bind,inertiaLiftProgram_work,work_pure,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_zero]
    nlinarith

theorem exists_full_shape_arithmetic_kernels (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
        ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^(9/4+ζ) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_padded_arithmetic_kernels ζ hζ
  let B := C+((kernels 0 0 0).cost:ℝ)+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨kernels,B,hB,?_⟩
  intro a b c N hN ha hb hc
  have hPow : 1 ≤ (N:ℝ)^(9/4+ζ) := Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  have hcost0 : (0:ℝ) ≤ ((kernels 0 0 0).cost:ℝ) := Nat.cast_nonneg _
  have hCB : C ≤ B := by dsimp [B]; linarith
  by_cases hm : 1 ≤ max a (max b c)
  · have hbase : max (a:ℝ) (max (b:ℝ) (c:ℝ)) ≤ (N:ℝ) := by
      exact_mod_cast max_le ha (max_le hb hc)
    have hmono := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ max (a:ℝ) (max (b:ℝ) (c:ℝ)))
      hbase (show (0:ℝ) ≤ 9/4+ζ by linarith)
    have hfirst : ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^(9/4+ζ) :=
      (hK a b c hm).trans (mul_le_mul_of_nonneg_left hmono hC.le)
    exact hfirst.trans (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (by positivity) _))
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    subst a; subst b; subst c
    have hk0 : ((kernels 0 0 0).cost:ℝ) ≤ B := by dsimp [B]; linarith
    exact hk0.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hPow hB.le)

/-- Complete fast exact inertia for every symmetric matrix, including
zero and repeated eigenvalues. Every returned certificate is exact; failure
has probability zero, and every Gaussian outcome obeys the arithmetic cap. -/
theorem exists_fast_singular_inertia_program (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (D : Core n) (hD : Dᵀ = D), 1 ≤ n →
        (∀ g : Fin (n*n) → ℝ, (singularInertiaProgram kernels n D hD g).admissible ∧
          ((singularInertiaProgram kernels n D hD g).work:ℝ) ≤ C*(n:ℝ)^(9/4+ζ)) ∧
        (∀ᵐ g ∂gaussianVector (n*n), ∃ out, (singularInertiaProgram kernels n D hD g).eval = some out) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_full_shape_arithmetic_kernels ζ hζ
  refine ⟨kernels,100*(C+1),by positivity,?_⟩
  intro n D hD hn
  refine ⟨?_,singularInertiaProgram_success_ae kernels n D hD⟩
  intro g
  exact ⟨singularInertiaProgram_admissible kernels n D hD g,
    singularInertiaProgram_work_bound kernels C (9/4+ζ) hC (by linarith) hK D hD hn g⟩

end
end HierarchicalAbsoluteSpectral
