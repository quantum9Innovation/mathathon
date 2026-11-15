import HierarchicalAbsoluteSpectral.EmbeddingProgram
import HierarchicalAbsoluteSpectral.ProbabilitySRHTSampler

/-! Gaussian-only realization of the fast embedding. Sampling costs are the
real sign comparisons and the proved O(n log n) priority sort, with three
independent length-n Gaussian arrays charged separately as n samples each. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open SRHT Matrix
open ArithmeticProgram hiding pure

def gaussianSignBitProgram (g : ℝ) : ArithmeticProgram (ZMod 2) :=
  .compare g 0 (fun b => .pure (if b then 0 else 1))

@[simp] theorem gaussianSignBitProgram_eval (g : ℝ) :
    (gaussianSignBitProgram g).eval=gaussianSignBit g := by
  simp [gaussianSignBitProgram, ArithmeticProgram.eval, gaussianSignBit]
@[simp] theorem gaussianSignBitProgram_work (g : ℝ) :
    (gaussianSignBitProgram g).work=1 := rfl
theorem gaussianSignBitProgram_admissible (g : ℝ) :
    (gaussianSignBitProgram g).admissible := by
  simp [gaussianSignBitProgram, ArithmeticProgram.admissible]

def gaussianSignsProgram (k : ℕ) (g : Fin (2^k) → ℝ) : ArithmeticProgram (SignAssignment k) :=
  finiteTabulateProgram (fun i => gaussianSignBitProgram (g (gaussianWalshEquiv k i)))

@[simp] theorem gaussianSignsProgram_eval (k : ℕ) (g : Fin (2^k) → ℝ) :
    (gaussianSignsProgram k g).eval=gaussianSRHTSigns k g := by
  simp only [gaussianSignsProgram, finiteTabulateProgram_eval, gaussianSignBitProgram_eval]
  rfl
@[simp] theorem gaussianSignsProgram_work (k : ℕ) (g : Fin (2^k) → ℝ) :
    (gaussianSignsProgram k g).work=2^k := by simp [gaussianSignsProgram]
theorem gaussianSignsProgram_admissible (k : ℕ) (g : Fin (2^k) → ℝ) :
    (gaussianSignsProgram k g).admissible := by
  simp [gaussianSignsProgram, gaussianSignBitProgram_admissible]

def gaussianRowsProgram (k M : ℕ) (hM : M≤2^k) (g : Fin (2^k) → ℝ) :
    ArithmeticProgram (RowSet k M) := do
  let s ← (priorityRowsProgram (2^k) M g).certify
  have hs : s.val.card=M := by
    rw [s.property, priorityRowsProgram_eval]
    exact priorityRows_card _ _ hM g
  ArithmeticProgram.pure (gaussianRowSetEquiv k M ⟨s.val,hs⟩)

@[simp] theorem gaussianRowsProgram_eval (k M : ℕ) (hM : M≤2^k) (g : Fin (2^k) → ℝ) :
    (gaussianRowsProgram k M hM g).eval=gaussianSRHTRows k M hM g := by
  simp only [gaussianRowsProgram, eval_bind, eval_pure, certify_eval, priorityRowsProgram_eval]
  rfl
theorem gaussianRowsProgram_work (k M : ℕ) (hM : M≤2^k) (g : Fin (2^k) → ℝ) :
    (gaussianRowsProgram k M hM g).work≤k*2^k := by
  simp only [gaussianRowsProgram, work_bind, work_pure, add_zero, certify_work]
  exact priorityRowsProgram_work k M g
theorem gaussianRowsProgram_admissible (k M : ℕ) (hM : M≤2^k) (g : Fin (2^k) → ℝ) :
    (gaussianRowsProgram k M hM g).admissible := by
  simp [gaussianRowsProgram, priorityRowsProgram_admissible]

def gaussianSRHTSampleProgram (k M : ℕ) (hM : M≤2^k)
    (g : (Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))) :
    ArithmeticProgram (SignAssignment k × (SignAssignment k × RowSet k M)) := do
  let x ← gaussianSignsProgram k g.1
  let y ← gaussianSignsProgram k g.2.1
  let T ← gaussianRowsProgram k M hM g.2.2
  ArithmeticProgram.pure (x,(y,T))

@[simp] theorem gaussianSRHTSampleProgram_eval (k M : ℕ) (hM : M≤2^k)
    (g : (Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))) :
    (gaussianSRHTSampleProgram k M hM g).eval=gaussianSRHTSample k M hM g := by
  simp [gaussianSRHTSampleProgram, gaussianSRHTSample]

theorem gaussianSRHTSampleProgram_work (k M : ℕ) (hM : M≤2^k)
    (g : (Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))) :
    (gaussianSRHTSampleProgram k M hM g).work≤(k+2)*2^k := by
  simp only [gaussianSRHTSampleProgram, work_bind, work_pure, add_zero, gaussianSignsProgram_work]
  have h := gaussianRowsProgram_work k M hM g.2.2
  nlinarith

theorem gaussianSRHTSampleProgram_admissible (k M : ℕ) (hM : M≤2^k)
    (g : (Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))) :
    (gaussianSRHTSampleProgram k M hM g).admissible := by
  simp [gaussianSRHTSampleProgram, gaussianSignsProgram_admissible, gaussianRowsProgram_admissible]

/-- The probability statement refers to the literal output of the counted
Gaussian sampler, rather than an assumed primitive finite-law draw. -/
theorem gaussian_program_embedding_success (k d : ℕ)
    (U : Matrix (WalshIndex k) (Fin d) ℝ) (hU : Uᵀ*U=1) (hd : 1≤d) (hdn : d≤2^k)
    (ε δ : ℝ) (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1/2) :
    1-δ ≤ (gaussianSRHTInputLaw k).real
      {g | let z := (gaussianSRHTSampleProgram k (rowCount (2^k) d ε δ)
        (rowCount_le _ _ _ _) g).eval
        FixedSizeTail.IsOSE U z.1 z.2.1 z.2.2.val ε} := by
  simp only [gaussianSRHTSampleProgram_eval]
  change 1-δ ≤ (gaussianSRHTInputLaw k).real
    (gaussianSRHTSample k (rowCount (2^k) d ε δ) (rowCount_le _ _ _ _) ⁻¹'
      {z | FixedSizeTail.IsOSE U z.1 z.2.1 z.2.2.val ε})
  rw [gaussian_srht_sampling_probability]
  exact two_round_srht_ose_independent U hU hd hdn ε δ hε hε1 hδ hδ1

end
end HierarchicalAbsoluteSpectral
