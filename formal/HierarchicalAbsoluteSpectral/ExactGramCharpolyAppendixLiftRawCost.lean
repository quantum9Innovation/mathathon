import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftCost

/-! A shape-sensitive operation bound without a restriction on the rank. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

def exactGramAppendixRectCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b c : ℕ) : ℕ :=
  Finset.univ.sup (fun ijl : Fin (a+1) × Fin (b+1) × Fin (c+1) =>
    (kernels ijl.1.val ijl.2.1.val ijl.2.2.val).cost)

theorem exactGramAppendixRectCost_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (a b c i j l : ℕ) (hi : i ≤ a) (hj : j ≤ b) (hl : l ≤ c) :
    (kernels i j l).cost ≤ exactGramAppendixRectCost kernels a b c := by
  let ijl : Fin (a+1) × Fin (b+1) × Fin (c+1) :=
    (⟨i,by omega⟩,⟨j,by omega⟩,⟨l,by omega⟩)
  exact Finset.le_sup (f:=fun ijl : Fin (a+1) × Fin (b+1) × Fin (c+1) =>
    (kernels ijl.1.val ijl.2.1.val ijl.2.2.val).cost) (Finset.mem_univ ijl)

def exactGramAppendixRangeCoreCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (r : ℕ) : ℕ :=
  Finset.univ.sup (fun i : Fin (r+1) => psdGramCost kernels i.val)

theorem exactGramAppendixRangeCoreCost_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (r w : ℕ) (hw : w ≤ r) : psdGramCost kernels w ≤ exactGramAppendixRangeCoreCost kernels r :=
  Finset.le_sup (f:=fun i : Fin (r+1) => psdGramCost kernels i.val) (Finset.mem_univ ⟨w,by omega⟩)

def exactGramAppendixLiftRawCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n m p k r : ℕ) : ℕ :=
  k+exactGramAppendixRectCost kernels m k r+exactGramAppendixRectCost kernels n m r+
    exactGramAppendixRectCost kernels r n r+exactGramAppendixRangeCoreCost kernels r+
    exactGramAppendixRectCost kernels n r r+exactGramAppendixRectCost kernels r n m+
    exactGramAppendixRectCost kernels r m p+exactGramAppendixRectCost kernels n r p

theorem exactGramAppendixLiftProgram_work_le_raw
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K)
    (hr : out.negativeCount ≤ r) :
    (exactGramAppendixLiftProgram kernels A B T out hr).work ≤
      exactGramAppendixLiftRawCost kernels n m p k r := by
  have hsr (s : ExactGramNegativeSelection out.diagonal) : s.width ≤ r := by
    calc s.width = out.negativeCount := s.width_eq
         _ ≤ r := hr
  have hRange (s : ExactGramNegativeSelection out.diagonal)
      (Y : Matrix (Fin n) (Fin s.width) ℝ) :
      (orthogonalRangeProgram kernels Y).work ≤ exactGramAppendixRectCost kernels r n r+
        exactGramAppendixRangeCoreCost kernels r+exactGramAppendixRectCost kernels n r r := by
    simp only [orthogonalRangeProgram, work_bind, certify_work, ArithmeticKernel.program_work,
      work_pure, add_zero]
    calc
      _ ≤ exactGramAppendixRectCost kernels r n r+
          (exactGramAppendixRangeCoreCost kernels r+exactGramAppendixRectCost kernels n r r) := by
        gcongr
        · exact exactGramAppendixRectCost_le kernels r n r _ _ _ (hsr s) le_rfl (hsr s)
        · apply (psdGramProgram_work_le kernels _ _ _).trans
          exact exactGramAppendixRangeCoreCost_le kernels r _ (hsr s)
        · exact exactGramAppendixRectCost_le kernels n r r _ _ _ le_rfl (hsr s)
            ((PSDGramPair.dimension_le_fin _).trans (hsr s))
      _ = _ := by omega
  have hprojection (s : ExactGramNegativeSelection out.diagonal)
      (Y : Matrix (Fin n) (Fin s.width) ℝ) (qr : OrthogonalRange Y) (hqr : qr.dimension ≤ r) :
      (projectionOutputProgram kernels A B qr.basis hqr).work ≤
        exactGramAppendixRectCost kernels r n m+exactGramAppendixRectCost kernels r m p+
          exactGramAppendixRectCost kernels n r p := by
    rw [projectionOutputProgram_work]
    gcongr
    · exact exactGramAppendixRectCost_le kernels r n m _ _ _ hqr le_rfl le_rfl
    · exact exactGramAppendixRectCost_le kernels r m p _ _ _ hqr le_rfl le_rfl
    · exact exactGramAppendixRectCost_le kernels n r p _ _ _ le_rfl hqr le_rfl
  rw [exactGramAppendixLiftProgram_work]
  simp only [exactGramAppendixLiftDataProgram, work_bind, certify_work,
    exactGramNegativeSelectionProgram_work, ArithmeticKernel.program_work, work_pure]
  calc
    _ ≤ k+(exactGramAppendixRectCost kernels m k r+(exactGramAppendixRectCost kernels n m r+
        ((exactGramAppendixRectCost kernels r n r+exactGramAppendixRangeCoreCost kernels r+
          exactGramAppendixRectCost kernels n r r)+
          ((exactGramAppendixRectCost kernels r n m+exactGramAppendixRectCost kernels r m p+
            exactGramAppendixRectCost kernels n r p)+0)))) := by
      gcongr
      · exact exactGramAppendixRectCost_le kernels m k r _ _ _ le_rfl le_rfl (hsr _)
      · exact exactGramAppendixRectCost_le kernels n m r _ _ _ le_rfl le_rfl (hsr _)
      · exact hRange _ _
      · exact hprojection _ _ _ _
    _ = _ := by unfold exactGramAppendixLiftRawCost; omega

end
end HierarchicalAbsoluteSpectral
