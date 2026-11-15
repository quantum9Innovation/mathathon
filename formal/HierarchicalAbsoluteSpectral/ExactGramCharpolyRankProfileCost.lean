import HierarchicalAbsoluteSpectral.ExactGramCharpolyRankProfileProgram

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem FieldOrderedPSDPrincipalData.dimension_le_fin {w : ℕ} {D : Core w}
    (p : FieldOrderedPSDPrincipalData D) : p.dimension ≤ w := by
  simpa only [Fintype.card_fin] using p.dimension_le

theorem fieldPrincipalProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (w : ℕ) (D : Core w) (hD : D.PosSemidef) :
    (fieldPrincipalProgram kernels w D hD).work ≤ fastLDLCost kernels w := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    rcases w with _ | _ | w
    · rw [fieldPrincipalProgram, fastLDLCost]; rfl
    · rw [fieldPrincipalProgram, fastLDLCost]; exact fieldPrincipalSingleProgram_work D hD
    · let l := (w+2)/2
      let r := w+2-l
      have hl : l < w+2 := by dsimp [l]; omega
      have hr : r < w+2 := by dsimp [r,l]; omega
      have he : l+r = w+2 := by dsimp [l,r]; omega
      have ihl := ih l hl
      have ihr := ih r hr
      have hassem {A : Core l} {S : Core r} (p : FieldOrderedPSDPrincipalData A)
          (B : Matrix (Fin l) (Fin r) ℝ) (C : Core r)
          (hblock : (Matrix.fromBlocks A B Bᵀ C).PosSemidef)
          (q : FieldOrderedPSDPrincipalData S) (hS : S = p.schur B C)
          (H : Matrix (Fin p.dimension) (Fin r) ℝ)
          (hH : H = p.inverse * B.submatrix p.selected id) :
          (fieldPrincipalAssembleProgram kernels p B C hblock q hS H hH).work ≤
            3 * kernelEnvelope kernels (w+2) + l*r := by
        have hp := p.dimension_le_fin
        have hq := q.dimension_le_fin
        apply (fieldPrincipalAssembleProgram_work_le kernels p B C hblock q hS H hH).trans
        rw [he]
        gcongr
      rw [fieldPrincipalProgram, fastLDLCost]
      simp only [work_bind, certify_work, blockSubProgram_work, work_pure]
      change _ ≤ fastLDLCost kernels l + fastLDLCost kernels r +
        6 * kernelEnvelope kernels (w+2) + 2*(w+2)*(w+2)
      calc
        _ ≤ fastLDLCost kernels l + (kernelEnvelope kernels (w+2) +
            (kernelEnvelope kernels (w+2) + (r*r + (fastLDLCost kernels r +
              ((3 * kernelEnvelope kernels (w+2) + l*r) + 0))))) := by
          gcongr
          all_goals first | exact ihl _ _ | exact ihr _ _ | exact hassem _ _ _ _ _ _ _ _ |
            apply rankProfileMulProgram_work_le
          all_goals first | omega |
            exact (FieldOrderedPSDPrincipalData.dimension_le_fin _).trans (by omega)
        _ ≤ _ := by nlinarith

theorem fieldColumnRankProfileProgram_work_le
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ)
    (N : ℕ) (hn : n ≤ N) (hw : w ≤ N) :
    (fieldColumnRankProfileProgram kernels V).work ≤
      fastLDLCost kernels w + 2 * kernelEnvelope kernels N := by
  simp only [fieldColumnRankProfileProgram, work_bind, certify_work, work_pure]
  calc
    _ ≤ kernelEnvelope kernels N + (fastLDLCost kernels w + (kernelEnvelope kernels N + 0)) := by
      gcongr
      · exact rankProfileMulProgram_work_le kernels _ _ N hw hn hw
      · exact fieldPrincipalProgram_work_le kernels _ _ _
      · apply rankProfileMulProgram_work_le
        all_goals first | exact hn |
          exact (FieldOrderedPSDPrincipalData.dimension_le_fin _).trans hw
    _ = _ := by omega

theorem fieldColumnRankProfileProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N:ℝ)^p)
    {n w : ℕ} (V : Matrix (Fin n) (Fin w) ℝ)
    (N : ℕ) (hN : 1 ≤ N) (hn : n ≤ N) (hw : w ≤ N) :
    ((fieldColumnRankProfileProgram kernels V).work : ℝ) ≤
      20*(C+1)*(N:ℝ)^p := by
  have hE := kernelEnvelope_bound kernels C p hC hK N hN
  have hcost : (fastLDLCost kernels w : ℝ) ≤ 18*(C+1)*(N:ℝ)^p := by
    by_cases hw0 : w = 0
    · subst w
      simp only [fastLDLCost, Nat.cast_zero]
      positivity
    · apply (fastLDLCost_bound kernels C p hC hp hK w (by omega)).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hw) (by linarith)
  have hr : ((fieldColumnRankProfileProgram kernels V).work : ℝ) ≤
      (fastLDLCost kernels w : ℝ) + 2*(kernelEnvelope kernels N : ℝ) := by
    exact_mod_cast fieldColumnRankProfileProgram_work_le kernels V N hn hw
  have hpow : 0 ≤ (N:ℝ)^p := Real.rpow_nonneg (by positivity) _
  nlinarith

theorem exists_fast_field_column_rank_profile_program (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (n w N : ℕ) (V : Matrix (Fin n) (Fin w) ℝ), 1 ≤ N → n ≤ N → w ≤ N →
        (fieldColumnRankProfileProgram kernels V).admissible ∧
        ((fieldColumnRankProfileProgram kernels V).work : ℝ) ≤ C*(N:ℝ)^(9/4+ζ) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_padded_arithmetic_kernels ζ hζ
  refine ⟨kernels,20*(C+1),by positivity,?_⟩
  intro n w N V hN hn hw
  refine ⟨fieldColumnRankProfileProgram_admissible kernels V, ?_⟩
  apply fieldColumnRankProfileProgram_work_bound kernels C (9/4+ζ) hC (by linarith) _ V N hN hn hw
  intro a b c M hmax _hM ha hb hc
  apply (hK a b c hmax).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast max_le ha (max_le hb hc)) (by linarith)

end
end HierarchicalAbsoluteSpectral
