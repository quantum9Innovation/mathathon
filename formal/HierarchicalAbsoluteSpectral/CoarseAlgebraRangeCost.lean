import HierarchicalAbsoluteSpectral.CoarseAlgebraRangeProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraPSDCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open ArithmeticProgram hiding pure
variable {m w : ℕ}

theorem orthogonalRangeProgram_work_le_size (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Y : Matrix (Fin m) (Fin w) ℝ) (N : ℕ) (hN : 1 ≤ N) (hm : m ≤ N) (hw : w ≤ N)
    (hmax : 1 ≤ max m w) :
    (orthogonalRangeProgram kernels Y).work ≤
      2*kernelEnvelope kernels N+psdGramCost kernels w := by
  simp only [orthogonalRangeProgram, work_bind, certify_work, ArithmeticKernel.program_work,
    work_pure, add_zero]
  calc
    _ ≤ kernelEnvelope kernels N+(psdGramCost kernels w+kernelEnvelope kernels N) := by
      gcongr
      · exact kernelEnvelope_le kernels N w m w hw hm hw (by omega)
      · exact psdGramProgram_work_le kernels _ _ _
      · apply kernelEnvelope_le
        · exact hm
        · exact hw
        · exact (PSDGramPair.dimension_le_fin _).trans hw
        · omega
    _ = _ := by omega

theorem orthogonalRangeProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Y : Matrix (Fin m) (Fin w) ℝ) (hm : 1 ≤ m) (hw : w ≤ m) :
    (orthogonalRangeProgram kernels Y).work ≤
      2*kernelEnvelope kernels m+psdGramCost kernels w := by
  simp only [orthogonalRangeProgram, work_bind, certify_work, ArithmeticKernel.program_work,
    work_pure, add_zero]
  calc
    _ ≤ kernelEnvelope kernels m+(psdGramCost kernels w+kernelEnvelope kernels m) := by
      gcongr
      · exact kernelEnvelope_le kernels m w m w hw le_rfl hw (by omega)
      · exact psdGramProgram_work_le kernels _ _ _
      · apply kernelEnvelope_le
        · rfl
        · exact hw
        · exact (PSDGramPair.dimension_le_fin _).trans hw
        · omega
    _ = _ := by omega

theorem orthogonalRangeProgram_work_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (Y : Matrix (Fin m) (Fin w) ℝ) (hm : 1 ≤ m) (hw : w ≤ m) :
    ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ 11*(C+1)*(m:ℝ)^p := by
  have he := kernelEnvelope_bound kernels C p hC hK m hm
  have ht : (psdGramCost kernels w:ℝ) ≤ 9*(C+1)*(m:ℝ)^p := by
    by_cases hw1 : 1 ≤ w
    · apply (psdGramCost_bound kernels C p hC hp hK w hw1).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hw) (by linarith)
    · have hw0 : w = 0 := by omega
      rw [hw0, psdGramCost]
      simp only [Nat.cast_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hb : ((orthogonalRangeProgram kernels Y).work:ℝ) ≤
      2*(kernelEnvelope kernels m:ℝ)+(psdGramCost kernels w:ℝ) := by
    exact_mod_cast orthogonalRangeProgram_work_le kernels Y hm hw
  have hpow := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ m) p
  nlinarith

theorem orthogonalRangeProgram_work_bound_size (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p)
    (Y : Matrix (Fin m) (Fin w) ℝ) (N : ℕ) (hN : 1 ≤ N) (hm : m ≤ N) (hw : w ≤ N)
    (hmax : 1 ≤ max m w) :
    ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ 11*(C+1)*(N:ℝ)^p := by
  have he := kernelEnvelope_bound kernels C p hC hK N hN
  have ht : (psdGramCost kernels w:ℝ) ≤ 9*(C+1)*(N:ℝ)^p := by
    by_cases hw1 : 1 ≤ w
    · apply (psdGramCost_bound kernels C p hC hp hK w hw1).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hw) (by linarith)
    · have hw0 : w = 0 := by omega
      rw [hw0, psdGramCost]
      simp only [Nat.cast_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hb : ((orthogonalRangeProgram kernels Y).work:ℝ) ≤
      2*(kernelEnvelope kernels N:ℝ)+(psdGramCost kernels w:ℝ) := by
    exact_mod_cast orthogonalRangeProgram_work_le_size kernels Y N hN hm hw hmax
  have hpow := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ N) p
  nlinarith

/-- Exact rank and orthonormal range extraction in one fast core cost,
including zero and repeated pivots. The width can reach the row dimension. -/
theorem exists_fast_orthogonal_range_program (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (m w : ℕ) (Y : Matrix (Fin m) (Fin w) ℝ), 1 ≤ m → w ≤ m →
        (orthogonalRangeProgram kernels Y).admissible ∧
        ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ C*(m:ℝ)^(9/4+ζ) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_padded_arithmetic_kernels ζ hζ
  refine ⟨kernels,11*(C+1),by positivity,?_⟩
  intro m w Y hm hw
  refine ⟨orthogonalRangeProgram_admissible kernels Y,?_⟩
  apply orthogonalRangeProgram_work_bound kernels C (9/4+ζ) hC (by linarith) _ Y hm hw
  intro a b c N hmax _hN ha hb hc
  apply (hK a b c hmax).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast max_le ha (max_le hb hc)) (by linarith)

theorem exists_fast_orthogonal_range_program_max (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (m w : ℕ) (Y : Matrix (Fin m) (Fin w) ℝ), 1 ≤ max m w →
        (orthogonalRangeProgram kernels Y).admissible ∧
        ((orthogonalRangeProgram kernels Y).work:ℝ) ≤ C*(max m w:ℝ)^(9/4+ζ) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_padded_arithmetic_kernels ζ hζ
  refine ⟨kernels,11*(C+1),by positivity,?_⟩
  intro m w Y hm
  refine ⟨orthogonalRangeProgram_admissible kernels Y,?_⟩
  rw [← Nat.cast_max]
  apply orthogonalRangeProgram_work_bound_size kernels C (9/4+ζ) hC (by linarith) _ Y
    (max m w) hm (le_max_left _ _) (le_max_right _ _) hm
  intro a b c N hmax _hN ha hb hc
  apply (hK a b c hmax).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast max_le ha (max_le hb hc)) (by linarith)

end
end HierarchicalAbsoluteSpectral
