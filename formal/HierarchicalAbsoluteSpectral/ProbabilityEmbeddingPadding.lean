import HierarchicalAbsoluteSpectral.ProbabilityEmbeddingParameters

/-! Dyadic padding preserves the input Gram matrix exactly. The padding
operator is only an indexed copy with zero fill, never a dense product. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix WithLp SparseFock SRHT
open scoped MatrixOrder Matrix.Norms.L2Operator

def dyadicPaddingLevel (n : ℕ) : ℕ := leastHalvings (n : ℝ) 1 (by norm_num)

theorem dyadicPaddingLevel_ge (n : ℕ) : n ≤ 2^dyadicPaddingLevel n := by
  have hs := leastHalvings_spec (n : ℝ) 1 (by norm_num)
  have hh : (n : ℝ) ≤ (2 : ℝ)^dyadicPaddingLevel n := by
    simpa only [one_mul,dyadicPaddingLevel] using (div_le_iff₀ (by positivity)).mp hs
  exact_mod_cast hh

theorem dyadicPaddingLevel_lt_two (n : ℕ) (hn : 0 < n) :
    2^dyadicPaddingLevel n < 2*n := by
  cases he : dyadicPaddingLevel n with
  | zero => simp only [pow_zero]; omega
  | succ j =>
    have hm : ¬ (n : ℝ)/(2 : ℝ)^j ≤ 1 :=
      Nat.find_min (exists_halving_bound (n : ℝ) 1 (by norm_num))
        (show j < dyadicPaddingLevel n by omega)
    have hh := (lt_div_iff₀ (by positivity)).mp (lt_of_not_ge hm)
    have hr : (2 : ℝ)^(j+1) < 2*(n : ℝ) := by rw [pow_succ]; nlinarith
    exact_mod_cast hr

def dyadicPaddingProgram (n : ℕ) : ArithmeticProgram ℕ := scalarHalving (n : ℝ) 1 (by norm_num)

theorem dyadicPaddingProgram_specification (n : ℕ) :
    (dyadicPaddingProgram n).eval = dyadicPaddingLevel n ∧
    (dyadicPaddingProgram n).work = 2*dyadicPaddingLevel n+1 ∧
    (dyadicPaddingProgram n).admissible := scalarHalving_checked _ _ _

def walshPaddingMatrix {n k : ℕ} (hn : n ≤ 2^k) : Matrix (WalshIndex k) (Fin n) ℝ :=
  (columnEmbedding (Fin.castLEEmb hn)).submatrix (gaussianWalshEquiv k) id

theorem walshPaddingMatrix_gram {n k : ℕ} (hn : n ≤ 2^k) :
    (walshPaddingMatrix hn)ᵀ*walshPaddingMatrix hn = 1 := by
  ext i j
  change (∑ a : WalshIndex k,
    columnEmbedding (Fin.castLEEmb hn) (gaussianWalshEquiv k a) i *
      columnEmbedding (Fin.castLEEmb hn) (gaussianWalshEquiv k a) j) = (1 : Core n) i j
  exact (Fintype.sum_equiv (gaussianWalshEquiv k) _ _ (fun _ => rfl)).trans
    (congrArg (fun M : Core n => M i j) (columnEmbedding_gram (Fin.castLEEmb hn)))

def walshPaddedMatrix {n m k : ℕ} (hn : n ≤ 2^k) (A : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (WalshIndex k) (Fin m) ℝ := walshPaddingMatrix hn*A

theorem walshPaddedMatrix_gram {n m k : ℕ} (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) :
    (walshPaddedMatrix hn A)ᵀ*walshPaddedMatrix hn A = Aᵀ*A := by
  unfold walshPaddedMatrix
  rw [Matrix.transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (walshPaddingMatrix hn)ᵀ,
    walshPaddingMatrix_gram,Matrix.one_mul]

theorem walshPaddedMatrix_lookup {n m k : ℕ} (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (i : WalshIndex k) (j : Fin m) :
    walshPaddedMatrix hn A i j =
      if h : (gaussianWalshEquiv k i).val < n then A ⟨(gaussianWalshEquiv k i).val,h⟩ j else 0 := by
  classical
  by_cases h : (gaussianWalshEquiv k i).val < n
  · let a : Fin n := ⟨(gaussianWalshEquiv k i).val,h⟩
    have he : ∀ b : Fin n, gaussianWalshEquiv k i = Fin.castLE hn b ↔ b = a := by
      intro b
      constructor
      · intro hb
        apply Fin.ext
        exact (congrArg Fin.val hb).symm
      · rintro rfl
        apply Fin.ext
        rfl
    simp [walshPaddedMatrix,walshPaddingMatrix,columnEmbedding,Matrix.mul_apply,
      Matrix.one_apply,he,h,a]
  · have he : ∀ b : Fin n, gaussianWalshEquiv k i ≠ Fin.castLE hn b := by
      intro b hb
      apply h
      simpa only [hb,Fin.val_castLE] using b.isLt
    simp [walshPaddedMatrix,walshPaddingMatrix,columnEmbedding,Matrix.mul_apply,
      Matrix.one_apply,he,h]

/-- The literal fast embedding output preserves the Gram matrix of every
input matrix, with no full-rank or nonzero-column hypothesis. -/
theorem gaussian_embedding_padded_matrix_good_event {n m k : ℕ}
    (hn : n ≤ 2^k) (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    let M := embeddingComputedRowCount (2^k) m ε δ
    ∃ E : Set ((Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))),
      MeasurableSet E ∧ (gaussianSRHTInputLaw k).real E ≥ 1-δ ∧
      ∀ g ∈ E, let z := (gaussianSRHTSampleProgram k M
        (embeddingComputedRowCount_specification (2^k) m ε δ (by positivity) hε).2.1 g).eval
        let B := (embeddingProgram z.1 z.2.1 z.2.2.val (walshPaddedMatrix hn A)).eval
        (1-ε) • (Aᵀ*A) ≤ Bᵀ*B ∧ Bᵀ*B ≤ (1+ε) • (Aᵀ*A) := by
  let M := embeddingComputedRowCount (2^k) m ε δ
  have hM := embeddingComputedRowCount_specification (2^k) m ε δ (by positivity) hε
  obtain ⟨E,hEm,hEp,hE⟩ := gaussian_embedding_arbitrary_matrix_prescribed
    (walshPaddedMatrix hn A) hM.2.1 hM.1 (embeddingMomentOrder_positive m δ)
    ε δ hε hε1 (embeddingMomentOrder_failure m δ hδ) hM.2.2
  refine ⟨E,hEm,hEp,?_⟩
  intro g hg
  have hh := hE g hg
  dsimp only at hh ⊢
  simp only [embeddingProgram_eval]
  simpa only [IsRelativeEmbedding,walshPaddedMatrix_gram] using hh

end
end HierarchicalAbsoluteSpectral
