import HierarchicalAbsoluteSpectral.MainSketchProgram
import HierarchicalAbsoluteSpectral.MainSketchGood

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory SRHT Set
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem sketchGramApprox_identity {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) : SketchGramApprox A ε (Aᵀ*A) := by
  have hp : (Aᵀ*A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self A
  constructor
  · simpa only [one_smul] using
      smul_le_smul_of_nonneg_right (show 1-ε ≤ (1 : ℝ) by linarith) hp.nonneg
  · simpa only [one_smul] using
      smul_le_smul_of_nonneg_right (show (1 : ℝ) ≤ 1+ε by linarith) hp.nonneg

theorem boundedSketchProgram_good_event {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    ∃ E : Set (SketchGaussianInput (dyadicPaddingLevel n)), MeasurableSet E ∧
      (gaussianSRHTInputLaw (dyadicPaddingLevel n)).real E ≥ 1-δ ∧
        ∀ g ∈ E, SketchGramApprox A ε (boundedSketchProgram A ε δ hε hδ g).eval.gram := by
  let k := dyadicPaddingLevel n
  let M := embeddingComputedRowCount (2^k) m ε δ
  by_cases hfull : n ≤ M
  · refine ⟨Set.univ,MeasurableSet.univ,?_,?_⟩
    · simp only [probReal_univ]
      linarith
    · intro g _
      change n ≤ embeddingComputedRowCount (2^dyadicPaddingLevel n) m ε δ at hfull
      rw [boundedSketchProgram_gram]
      simp [boundedSketchReferenceGram,hfull]
      exact sketchGramApprox_identity A ε hε.le
  · obtain ⟨E,hEm,hEp,hE⟩ := gaussian_embedding_padded_matrix_good_event
      (dyadicPaddingLevel_ge n) A ε δ hε hε1 hδ
    refine ⟨E,hEm,hEp,?_⟩
    intro g hg
    change ¬ n ≤ embeddingComputedRowCount (2^dyadicPaddingLevel n) m ε δ at hfull
    have hh := hE g hg
    dsimp only at hh
    simp only [embeddingProgram_eval,sampledFrame_gram,gaussianSRHTSampleProgram_eval] at hh
    rw [boundedSketchProgram_gram]
    simpa [SketchGramApprox,boundedSketchReferenceGram,hfull] using hh

theorem mainSketchAccuracy_le_one {n m p r L : ℕ} (I : FixedProblem n m p r L)
    (j : ℕ) (hj : j ≤ L) : I.accuracy j ≤ 1 := by
  have hb : ∀ j ≤ L, I.accuracy j ≤ I.accuracy 0 := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      have hp := I.accuracy_positive j (by omega)
      have hr := (div_le_iff₀ hp).mp (I.refinement_ratio j (by omega))
      have hprev := ih (by omega)
      nlinarith
  have hh := hb j hj
  linarith [I.initial_accuracy_le]

end
end HierarchicalAbsoluteSpectral
