import HierarchicalAbsoluteSpectral.MainSketchData
import HierarchicalAbsoluteSpectral.ProbabilityEmbeddingPadding

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix SRHT MeasureTheory
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator

abbrev SketchGaussianInput (k : ℕ) :=
  (Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))

structure StoredSketchFactor (n m : ℕ) where
  rows : ℕ
  rows_le : rows ≤ n
  value : Matrix (Fin rows) (Fin m) ℝ

def StoredSketchFactor.gram {n m : ℕ} (S : StoredSketchFactor n m) : Core m := S.valueᵀ*S.value

def rowFinMatrix {ι : Type*} [Fintype ι] {m : ℕ} (B : Matrix ι (Fin m) ℝ) :
    Matrix (Fin (Fintype.card ι)) (Fin m) ℝ := B.submatrix (Fintype.equivFin ι).symm id

theorem rowFinMatrix_gram {ι : Type*} [Fintype ι] {m : ℕ} (B : Matrix ι (Fin m) ℝ) :
    (rowFinMatrix B)ᵀ*rowFinMatrix B = Bᵀ*B := by
  ext i j
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun _ => rfl)

theorem certifiedValue_eq {α : Type} (p : ArithmeticProgram α) (a : α) (ha : p.eval = a) :
    p.certify.eval = ⟨a,ha.symm⟩ := Subtype.ext ((certify_eval p).trans ha)

def boundedSketchCoreProgram {n m : ℕ} (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (g : SketchGaussianInput k) : ArithmeticProgram (StoredSketchFactor n m) := do
  let M ← (embeddingRowCountProgram (2^k) m ε δ).certify
  have hMeq : M.val = embeddingComputedRowCount (2^k) m ε δ :=
    M.property.trans (embeddingRowCountProgram_specification _ _ _ _ hε hδ).1
  have hM : M.val ≤ 2^k := by
    rw [hMeq]
    exact (embeddingComputedRowCount_specification _ _ _ _ (by positivity) hε).2.1
  have hM0 : 0 < M.val := by
    rw [hMeq]
    exact (embeddingComputedRowCount_specification _ _ _ _ (by positivity) hε).1
  let c ← (scalarNatProgram M.val).certify
  have hc : c.val = (M.val : ℝ) := c.property.trans (scalarNatProgram_specification _).1
  .branch (n : ℝ) c.val
    (fun _ => ArithmeticProgram.pure ⟨n,le_rfl,A⟩)
    (fun hproper => do
      let z ← gaussianSRHTSampleProgram k M.val hM g
      let B ← embeddingProgram z.1 z.2.1 z.2.2.val (walshPaddedMatrix hn A)
      have hcard : Fintype.card z.2.2.val = M.val := by simpa using z.2.2.property
      have hMn : M.val < n := by
        have hh : ¬(n : ℝ) ≤ (M.val : ℝ) := by simpa only [hc] using hproper
        exact_mod_cast (lt_of_not_ge hh)
      ArithmeticProgram.pure
        { rows := Fintype.card z.2.2.val
          rows_le := by rw [hcard]; exact hMn.le
          value := rowFinMatrix B })

def castSketchGaussian {k l : ℕ} (h : k = l) (g : SketchGaussianInput l) : SketchGaussianInput k := h.symm ▸ g

def boundedSketchProgram {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (g : SketchGaussianInput (dyadicPaddingLevel n)) :
    ArithmeticProgram (StoredSketchFactor n m) := do
  let k ← (dyadicPaddingProgram n).certify
  have hk : k.val = dyadicPaddingLevel n := k.property.trans (dyadicPaddingProgram_specification n).1
  boundedSketchCoreProgram k.val (by rw [hk]; exact dyadicPaddingLevel_ge n) A ε δ hε hδ
    (castSketchGaussian hk g)

theorem boundedSketchCoreProgram_admissible {n m : ℕ} (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (g : SketchGaussianInput k) : (boundedSketchCoreProgram k hn A ε δ hε hδ g).admissible := by
  have hMe := (embeddingRowCountProgram_specification (2^k) m ε δ hε hδ).1
  have hMc := certifiedValue_eq _ _ hMe
  have hcc := certifiedValue_eq _ _ (scalarNatProgram_specification (embeddingComputedRowCount (2^k) m ε δ)).1
  unfold boundedSketchCoreProgram
  simp only [admissible_bind,certify_admissible,
    (embeddingRowCountProgram_specification _ _ _ _ hε hδ).2.2,
    (scalarNatProgram_specification _).2.2,true_and,ArithmeticProgram.admissible,hMc,hcc]
  erw [hMc]
  split
  · trivial
  · simp only [admissible_bind,gaussianSRHTSampleProgram_admissible,true_and,admissible_pure,and_true,hMc,hcc]
    apply embeddingProgram_admissible
    exact lt_of_lt_of_eq (embeddingComputedRowCount_specification (2^k) m ε δ (by positivity) hε).1
      (gaussianSRHTSampleProgram k (embeddingComputedRowCount (2^k) m ε δ) (min_le_left _ _) g).eval.2.2.property.symm

theorem boundedSketchProgram_admissible {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (g : SketchGaussianInput (dyadicPaddingLevel n)) :
    (boundedSketchProgram A ε δ hε hδ g).admissible := by
  simp only [boundedSketchProgram,admissible_bind,certify_admissible,
    (dyadicPaddingProgram_specification n).2.2,boundedSketchCoreProgram_admissible,and_self]

def boundedSketchReferenceGram {n m : ℕ} (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ) (g : SketchGaussianInput k) : Core m :=
  let M := embeddingComputedRowCount (2^k) m ε δ
  let z := gaussianSRHTSample k M (min_le_left _ _) g
  if n ≤ M then Aᵀ*A else sampledGram (walshPaddedMatrix hn A) z.1 z.2.1 z.2.2.val

theorem boundedSketchCoreProgram_gram {n m : ℕ} (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (g : SketchGaussianInput k) :
    (boundedSketchCoreProgram k hn A ε δ hε hδ g).eval.gram =
      boundedSketchReferenceGram k hn A ε δ g := by
  have hMe := (embeddingRowCountProgram_specification (2^k) m ε δ hε hδ).1
  have hMc := certifiedValue_eq _ _ hMe
  have hcc := certifiedValue_eq _ _ (scalarNatProgram_specification (embeddingComputedRowCount (2^k) m ε δ)).1
  simp only [boundedSketchCoreProgram,eval_bind,hMc,hcc]
  erw [hMc,hcc]
  unfold boundedSketchReferenceGram
  by_cases hc : n ≤ embeddingComputedRowCount (2^k) m ε δ
  · have hcR : (n : ℝ) ≤ (embeddingComputedRowCount (2^k) m ε δ : ℝ) := by exact_mod_cast hc
    simp only [ArithmeticProgram.eval,hMc,hcc,dif_pos hcR,if_pos hc]
    rfl
  · have hcR : ¬(n : ℝ) ≤ (embeddingComputedRowCount (2^k) m ε δ : ℝ) := by exact_mod_cast hc
    simp only [ArithmeticProgram.eval,hMc,hcc,dif_neg hcR,if_neg hc,eval_bind,eval_pure,
      embeddingProgram_eval]
    let z : SignAssignment k × (SignAssignment k × RowSet k (embeddingComputedRowCount (2^k) m ε δ)) :=
      (gaussianSRHTSampleProgram k (embeddingComputedRowCount (2^k) m ε δ) (min_le_left _ _) g).eval
    change (rowFinMatrix (sampledFrame (walshPaddedMatrix hn A) z.1 z.2.1 z.2.2.val))ᵀ*
      rowFinMatrix (sampledFrame (walshPaddedMatrix hn A) z.1 z.2.1 z.2.2.val) = _
    rw [rowFinMatrix_gram,sampledFrame_gram]
    exact congrArg (fun zz : SignAssignment k × (SignAssignment k × RowSet k (embeddingComputedRowCount (2^k) m ε δ)) =>
      sampledGram (walshPaddedMatrix hn A) zz.1 zz.2.1 zz.2.2.val)
      (gaussianSRHTSampleProgram_eval k (embeddingComputedRowCount (2^k) m ε δ) (min_le_left _ _) g)

theorem boundedSketchProgram_gram {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (g : SketchGaussianInput (dyadicPaddingLevel n)) :
    (boundedSketchProgram A ε δ hε hδ g).eval.gram =
      boundedSketchReferenceGram (dyadicPaddingLevel n) (dyadicPaddingLevel_ge n) A ε δ g := by
  have hkc := certifiedValue_eq _ _ (dyadicPaddingProgram_specification n).1
  simp only [boundedSketchProgram,eval_bind,hkc,boundedSketchCoreProgram_gram,castSketchGaussian]
  erw [hkc]

end
end HierarchicalAbsoluteSpectral
