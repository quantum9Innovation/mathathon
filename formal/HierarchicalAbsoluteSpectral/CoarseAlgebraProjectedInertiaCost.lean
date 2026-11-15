import HierarchicalAbsoluteSpectral.CoarseAlgebraProjectedInertia

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
variable {n : ℕ}

theorem projectedReducedInertiaProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    {D : Core n} (support : InertiaSupport D) (hD : Dᵀ = D) (hn : 1 ≤ n)
    (g : Fin (n*n) → ℝ) :
    ((projectedReducedInertiaProgram kernels support hD g).work:ℝ) ≤
      25*(C+1)*(n:ℝ)^p := by
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
  have hproj := hK support.dimension n support.dimension n hn support.dimension_le le_rfl support.dimension_le
  have hsq : (n:ℝ)*(n:ℝ) ≤ (n:ℝ)^p := by
    simpa only [Real.rpow_two,pow_two] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ n) hp
  have hr : (support.dimension:ℝ) ≤ (n:ℝ)^p := by
    have hdim : (support.dimension:ℝ) ≤ n := by exact_mod_cast support.dimension_le
    have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hb : ((projectedReducedInertiaProgram kernels support hD g).work:ℝ) ≤
      ((kernels support.dimension n support.dimension).cost:ℝ)+
      ((fastLDLCost kernels support.dimension:ℝ)+
        5*((kernels support.dimension support.dimension support.dimension).cost:ℝ)+support.dimension) := by
    simp only [projectedReducedInertiaProgram,work_bind,ArithmeticKernel.program_work,Nat.cast_add]
    gcongr
    exact_mod_cast congruenceInertiaProgram_work_le kernels support.compressed
      (support.compressed_transpose hD) _
  have hnp := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ n) p
  nlinarith

theorem projectedSingularInertiaProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (D : Core n) (hD : Dᵀ = D) (hn : 1 ≤ n) (g : Fin (n*n) → ℝ) :
    ((projectedSingularInertiaProgram kernels n D hD g).work:ℝ) ≤ 100*(C+1)*(n:ℝ)^p := by
  let support := (inertiaSupportProgram kernels D hD).eval
  have hs := inertiaSupportProgram_work_bound kernels C p hC hp hK D hD hn
  have hg := projectedReducedInertiaProgram_work_bound kernels C p hC hp hK support hD hn g
  have hk := hK n n n n hn le_rfl le_rfl le_rfl
  have hnp := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ n) p
  simp only [projectedSingularInertiaProgram,work_bind,Nat.cast_add]
  split
  · simp only [work_pure,Nat.cast_zero]
    nlinarith
  · simp only [work_bind,inertiaLiftProgram_work,work_pure,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat,Nat.cast_zero]
    nlinarith

theorem exists_fast_projected_singular_inertia_program (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (D : Core n) (hD : Dᵀ = D), 1 ≤ n →
        (∀ g : Fin (n*n) → ℝ, (projectedSingularInertiaProgram kernels n D hD g).admissible ∧
          ((projectedSingularInertiaProgram kernels n D hD g).work:ℝ) ≤ C*(n:ℝ)^(9/4+ζ)) ∧
        (∀ᵐ g ∂gaussianVector (n*n),
          ∃ out, (projectedSingularInertiaProgram kernels n D hD g).eval = some out) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_full_shape_arithmetic_kernels ζ hζ
  refine ⟨kernels,100*(C+1),by positivity,?_⟩
  intro n D hD hn
  refine ⟨?_,projectedSingularInertiaProgram_success_ae kernels n D hD⟩
  intro g
  exact ⟨projectedSingularInertiaProgram_admissible kernels n D hD g,
    projectedSingularInertiaProgram_work_bound kernels C (9/4+ζ) hC (by linarith) hK D hD hn g⟩

end
end HierarchicalAbsoluteSpectral
