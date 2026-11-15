import HierarchicalAbsoluteSpectral.MainFamilyProgramBudgets
import HierarchicalAbsoluteSpectral.MainSketchProgram

/-! Row bounds for the sketches actually returned by the executed program.
The identity fallback retains all original rows only when those rows already
fit below the computed compressed-row cap. No good-sketch event is needed. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {n m p r L N : ℕ}

theorem boundedSketchCoreProgram_rows_computed (k : ℕ) (hn : n ≤ 2^k)
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (g : SketchGaussianInput k) :
    (boundedSketchCoreProgram k hn A ε δ hε hδ g).eval.rows ≤ embeddingComputedRowCount (2^k) m ε δ := by
  let M := embeddingComputedRowCount (2^k) m ε δ
  have hMe := (embeddingRowCountProgram_specification (2^k) m ε δ hε hδ).1
  have hMc := certifiedValue_eq _ _ hMe
  have hcc := certifiedValue_eq _ _ (scalarNatProgram_specification M).1
  unfold boundedSketchCoreProgram
  simp only [eval_bind]
  erw [hMc,hcc]
  by_cases hc : n ≤ M
  · have hcR : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hc
    simp only [ArithmeticProgram.eval,dif_pos hcR]
    exact hc
  · have hcR : ¬(n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hc
    simp only [ArithmeticProgram.eval,dif_neg hcR,eval_bind,eval_pure]
    have hrow : Fintype.card (gaussianSRHTSampleProgram k M (min_le_left _ _) g).eval.2.2.val = M := by
      simpa using (gaussianSRHTSampleProgram k M (min_le_left _ _) g).eval.2.2.property
    exact hrow.le

theorem boundedSketchProgram_rows_computed
    (A : Matrix (Fin n) (Fin m) ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (g : SketchGaussianInput (dyadicPaddingLevel n)) :
    (boundedSketchProgram A ε δ hε hδ g).eval.rows ≤
      embeddingComputedRowCount (2^dyadicPaddingLevel n) m ε δ := by
  have hkc := certifiedValue_eq _ _ (dyadicPaddingProgram_specification n).1
  simp only [boundedSketchProgram,eval_bind]
  erw [hkc]
  exact boundedSketchCoreProgram_rows_computed _ _ _ _ _ _ _ _

theorem mainSketchProgram_rowsA_computed (I : FixedProblem n m p r L) (g : MainRandomTape I)
    (j : Fin (L+1)) :
    ((mainSketchProgram I g).eval.levelA j).1 ≤
      embeddingComputedRowCount (2^dyadicPaddingLevel n) m (I.accuracy j.val) I.sketchFailure := by
  rw [mainSketchProgram_eval]
  exact boundedSketchProgram_rows_computed _ _ _ _ _ _

theorem mainSketchProgram_rowsB_computed (I : FixedProblem n m p r L) (g : MainRandomTape I)
    (j : Fin (L+1)) :
    ((mainSketchProgram I g).eval.levelB j).1 ≤
      embeddingComputedRowCount (2^dyadicPaddingLevel p) m (I.accuracy j.val) I.sketchFailure := by
  rw [mainSketchProgram_eval]
  exact boundedSketchProgram_rows_computed _ _ _ _ _ _

theorem PreparedFamilyProblem.actual_sketch_rows_bound (I : FamilyProblem N m r)
    (P : PreparedFamilyProblem I) (hL : P.scalars.schedule.depth ≠ 0)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m)
    (hmLog : Real.log 2 ≤ Real.log (m : ℝ))
    (hscale : Real.log (1/Real.sqrt (m/N : ℝ)) ≤ D*Real.log (m : ℝ))
    (hδ : (m : ℝ)^(-c) ≤ I.delta) (g : MainRandomTape P.fixed) (j : Fin (P.depth+1)) :
    let bound := 1+8192*((m : ℝ)+27*(((c+2*D+10)/Real.log 2)*Real.log (m : ℝ))^3)/(P.fixed.accuracy j.val)^2
    (((mainSketchProgram P.fixed g).eval.levelA j).1 : ℝ) ≤ bound ∧
      (((mainSketchProgram P.fixed g).eval.levelB j).1 : ℝ) ≤ bound := by
  intro bound
  have hb := P.embedding_rows_bound I hL D c hD hc hm hmLog hscale hδ
    (2^dyadicPaddingLevel N) j.val (by omega)
  exact ⟨(Nat.cast_le.mpr (mainSketchProgram_rowsA_computed P.fixed g j)).trans hb,
    (Nat.cast_le.mpr (mainSketchProgram_rowsB_computed P.fixed g j)).trans hb⟩

end
end HierarchicalAbsoluteSpectral
