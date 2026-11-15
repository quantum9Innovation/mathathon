import HierarchicalAbsoluteSpectral.MainSketchFiniteCore
import HierarchicalAbsoluteSpectral.MainSketchProgram
import HierarchicalAbsoluteSpectral.MainSketchProbability

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
variable {n m p r L : ℕ}

theorem boundedSketchFromSample_rows (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ)
    (z : SketchFiniteSample k (embeddingComputedRowCount (2^k) m ε δ)) :
    (boundedSketchFromSample k hn A ε δ z).rows = min n (embeddingComputedRowCount (2^k) m ε δ) := by
  classical
  unfold boundedSketchFromSample
  split_ifs with h
  · exact (min_eq_left h).symm
  · change Fintype.card z.2.2.val = _
    have hc : Fintype.card z.2.2.val = embeddingComputedRowCount (2^k) m ε δ := by
      simpa using z.2.2.property
    rw [hc,min_eq_right (le_of_lt (lt_of_not_ge h))]

theorem boundedSketchProgram_rows (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (g : SketchGaussianInput (dyadicPaddingLevel n)) :
    (boundedSketchProgram A ε δ hε hδ g).eval.rows =
      min n (embeddingComputedRowCount (2^dyadicPaddingLevel n) m ε δ) := by
  rw [boundedSketchProgram_eval]
  exact boundedSketchFromSample_rows _ _ _ _ _ _

theorem mainSketchProgram_rowsA (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    ((mainSketchProgram I g).eval.levelA j).1 =
      min n (embeddingComputedRowCount (2^dyadicPaddingLevel n) m (I.accuracy j.val) I.sketchFailure) := by
  rw [mainSketchProgram_eval]
  exact boundedSketchProgram_rows _ _ _ _ _ _

theorem mainSketchProgram_rowsB (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    ((mainSketchProgram I g).eval.levelB j).1 =
      min p (embeddingComputedRowCount (2^dyadicPaddingLevel p) m (I.accuracy j.val) I.sketchFailure) := by
  rw [mainSketchProgram_eval]
  exact boundedSketchProgram_rows _ _ _ _ _ _

theorem embeddingComputedRowCount_core_le (N m : ℕ) (ε δ : ℝ)
    (hmN : m ≤ N) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    m ≤ embeddingComputedRowCount N m ε δ := by
  have hD : m ≤ SRHT.effectiveDimension m (embeddingMomentOrder m δ) := by
    unfold SRHT.effectiveDimension
    omega
  have hDR : (m : ℝ) ≤ SRHT.effectiveDimension m (embeddingMomentOrder m δ) := by exact_mod_cast hD
  have hε2 : ε^2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hε2 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hx : (m : ℝ) ≤ embeddingRowTarget m (embeddingMomentOrder m δ) ε := by
    unfold embeddingRowTarget
    apply (le_div_iff₀ (pow_pos hε 2)).mpr
    nlinarith
  have hceil : m ≤ ⌈embeddingRowTarget m (embeddingMomentOrder m δ) ε⌉₊ := by
    exact_mod_cast hx.trans (Nat.le_ceil _)
  exact le_min hmN hceil

theorem mainSketchProgram_core_le_rowsA (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    m ≤ ((mainSketchProgram I g).eval.levelA j).1 := by
  rw [mainSketchProgram_rowsA]
  exact le_min I.core_le_rows (embeddingComputedRowCount_core_le _ _ _ _
    (I.core_le_rows.trans (dyadicPaddingLevel_ge n))
    (I.accuracy_positive j.val (by omega)) (mainSketchAccuracy_le_one I j.val (by omega)))

theorem mainSketchProgram_core_le_rowsB (I : FixedProblem n m p r L) (g : MainRandomTape I) (j : Fin (L+1)) :
    m ≤ ((mainSketchProgram I g).eval.levelB j).1 := by
  rw [mainSketchProgram_rowsB]
  exact le_min I.core_le_cols (embeddingComputedRowCount_core_le _ _ _ _
    (I.core_le_cols.trans (dyadicPaddingLevel_ge p))
    (I.accuracy_positive j.val (by omega)) (mainSketchAccuracy_le_one I j.val (by omega)))

end
end HierarchicalAbsoluteSpectral
