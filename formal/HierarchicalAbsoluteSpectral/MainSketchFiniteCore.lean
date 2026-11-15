import HierarchicalAbsoluteSpectral.MainSketchSingle

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix SRHT
open ArithmeticProgram hiding pure

abbrev SketchFiniteSample (k M : ℕ) := SignAssignment k × (SignAssignment k × RowSet k M)

def sampledStoredSketchFactor {n m : ℕ} (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (M : ℕ) (hMn : M ≤ n) (z : SketchFiniteSample k M) :
    StoredSketchFactor n m where
  rows := Fintype.card z.2.2.val
  rows_le := by
    have hh : Fintype.card z.2.2.val = M := by simpa using z.2.2.property
    rw [hh]
    exact hMn
  value := rowFinMatrix (sampledFrame (walshPaddedMatrix hn A) z.1 z.2.1 z.2.2.val)

def boundedSketchFromSample {n m : ℕ} (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ)
    (z : SketchFiniteSample k (embeddingComputedRowCount (2^k) m ε δ)) : StoredSketchFactor n m :=
  if h : n ≤ embeddingComputedRowCount (2^k) m ε δ then ⟨n,le_rfl,A⟩
  else sampledStoredSketchFactor k hn A _ (le_of_lt (lt_of_not_ge h)) z

theorem boundedSketchCoreProgram_eval {n m : ℕ} (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (g : SketchGaussianInput k) :
    (boundedSketchCoreProgram k hn A ε δ hε hδ g).eval =
      boundedSketchFromSample k hn A ε δ
        (gaussianSRHTSample k (embeddingComputedRowCount (2^k) m ε δ) (min_le_left _ _) g) := by
  have hMe := (embeddingRowCountProgram_specification (2^k) m ε δ hε hδ).1
  have hMc := certifiedValue_eq _ _ hMe
  have hcc := certifiedValue_eq _ _ (scalarNatProgram_specification (embeddingComputedRowCount (2^k) m ε δ)).1
  simp only [boundedSketchCoreProgram,eval_bind]
  erw [hMc,hcc]
  unfold boundedSketchFromSample
  by_cases hc : n ≤ embeddingComputedRowCount (2^k) m ε δ
  · have hcR : (n : ℝ) ≤ (embeddingComputedRowCount (2^k) m ε δ : ℝ) := by exact_mod_cast hc
    simp only [ArithmeticProgram.eval,dif_pos hcR,dif_pos hc]
  · have hcR : ¬(n : ℝ) ≤ (embeddingComputedRowCount (2^k) m ε δ : ℝ) := by exact_mod_cast hc
    simp only [ArithmeticProgram.eval,dif_neg hcR,dif_neg hc,eval_bind,eval_pure,embeddingProgram_eval]
    change sampledStoredSketchFactor k hn A (embeddingComputedRowCount (2^k) m ε δ)
      (le_of_lt (lt_of_not_ge hc))
      (gaussianSRHTSampleProgram k (embeddingComputedRowCount (2^k) m ε δ) (min_le_left _ _) g).eval = _
    exact congrArg (sampledStoredSketchFactor k hn A (embeddingComputedRowCount (2^k) m ε δ)
      (le_of_lt (lt_of_not_ge hc)))
      (gaussianSRHTSampleProgram_eval k (embeddingComputedRowCount (2^k) m ε δ) (min_le_left _ _) g)

theorem boundedSketchProgram_eval {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (g : SketchGaussianInput (dyadicPaddingLevel n)) :
    (boundedSketchProgram A ε δ hε hδ g).eval =
      boundedSketchFromSample (dyadicPaddingLevel n) (dyadicPaddingLevel_ge n) A ε δ
        (gaussianSRHTSample (dyadicPaddingLevel n)
          (embeddingComputedRowCount (2^dyadicPaddingLevel n) m ε δ) (min_le_left _ _) g) := by
  have hkc := certifiedValue_eq _ _ (dyadicPaddingProgram_specification n).1
  simp only [boundedSketchProgram,eval_bind,boundedSketchCoreProgram_eval]
  erw [hkc]
  rfl

end
end HierarchicalAbsoluteSpectral
