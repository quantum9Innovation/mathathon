import HierarchicalAbsoluteSpectral.SupportProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraKernelSelection

/-! The comparator's two true Gram products are charged separately from
support rank revelation.  The bound includes zero and deficient supports. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {m s t : ℕ}

def comparatorSupportWorkCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (s t m : ℕ) : ℕ :=
  (kernels m s m).cost+(kernels m t m).cost+
    psdGramCost kernels m+2*kernelEnvelope kernels m

theorem coarseSupportProgram_comparator_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (H : Matrix (Fin s) (Fin m) ℝ) (J : Matrix (Fin t) (Fin m) ℝ) (hm : 1 ≤ m) :
    (coarseSupportProgram kernels H J).work ≤ comparatorSupportWorkCap kernels s t m := by
  simp only [coarseSupportProgram,work_bind,certify_work,ArithmeticKernel.program_work,
    work_pure,add_zero]
  calc
    _ ≤ (kernels m s m).cost+(psdGramCost kernels m+
        ((kernels m t m).cost+(kernelEnvelope kernels m+kernelEnvelope kernels m))) := by
      gcongr
      · exact psdGramProgram_work_le kernels _ _ _
      · apply kernelEnvelope_le
        · exact PSDGramPair.dimension_le_fin _
        · exact le_rfl
        · exact le_rfl
        · omega
      · apply kernelEnvelope_le
        · exact PSDGramPair.dimension_le_fin _
        · exact le_rfl
        · exact PSDGramPair.dimension_le_fin _
        · omega
    _ = _ := by unfold comparatorSupportWorkCap; omega

theorem coarseSupportProgram_comparator_work_real
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C E G : ℝ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^E)
    (H : Matrix (Fin s) (Fin m) ℝ) (J : Matrix (Fin t) (Fin m) ℝ)
    (hm : 1 ≤ m) (hGA : ((kernels m s m).cost:ℝ) ≤ G)
    (hGB : ((kernels m t m).cost:ℝ) ≤ G) :
    ((coarseSupportProgram kernels H J).work:ℝ) ≤ 2*G+11*(C+1)*(m:ℝ)^E := by
  have henv := kernelEnvelope_bound kernels C E hC (fun a b c N _ => hK a b c N) m hm
  have hpsd := psdGramCost_bound kernels C E hC hE (fun a b c N _ => hK a b c N) m hm
  have hb : ((coarseSupportProgram kernels H J).work:ℝ) ≤
      (kernels m s m).cost+(kernels m t m).cost+
        (psdGramCost kernels m:ℝ)+2*(kernelEnvelope kernels m:ℝ) := by
    exact_mod_cast coarseSupportProgram_comparator_work_bound kernels H J hm
  have hp : 0 ≤ (m:ℝ)^E := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith

end
end HierarchicalAbsoluteSpectral
