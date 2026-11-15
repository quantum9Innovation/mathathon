import HierarchicalAbsoluteSpectral.CoarseAlgebraFastLDLProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraPSDCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

def fastLDLCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n+2 => fastLDLCost kernels ((n+2)/2)+fastLDLCost kernels (n+2-(n+2)/2)+
      6*kernelEnvelope kernels (n+2)+2*(n+2)*(n+2)
termination_by n => n
decreasing_by all_goals omega

theorem fastInertiaProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : Dᵀ = D) :
    (fastInertiaProgram kernels n D hD).work ≤ fastLDLCost kernels n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [fastInertiaProgram, fastLDLCost]; rfl
    · rw [fastInertiaProgram, fastLDLCost]; exact regularSingleProgram_work D
    · let l := (n+2)/2
      let r := n+2-l
      have hl : l < n+2 := by dsimp [l]; omega
      have hr : r < n+2 := by dsimp [r,l]; omega
      have hl1 : 1 ≤ l := by dsimp [l]; omega
      have hr1 : 1 ≤ r := by dsimp [r,l]; omega
      have he : l+r = n+2 := by dsimp [l,r]; omega
      have ihl := ih l hl
      have ihr := ih r hr
      have hquad : l+r*r+l*r ≤ 2*(n+2)*(n+2) := by nlinarith
      rw [fastInertiaProgram, fastLDLCost]
      simp only [work_bind]
      change _ ≤ fastLDLCost kernels l+fastLDLCost kernels r+
        6*kernelEnvelope kernels (n+2)+2*(n+2)*(n+2)
      split
      · simp only [work_pure,add_zero]
        calc
          _ ≤ fastLDLCost kernels l := ihl _ _
          _ ≤ _ := by omega
      · simp only [work_bind, certify_work, diagonalInverseProgram_work,
          ArithmeticKernel.program_work, blockSubProgram_work]
        split
        · simp only [work_pure]
          calc
            _ ≤ fastLDLCost kernels l+(l+(kernelEnvelope kernels (n+2)+
                (kernelEnvelope kernels (n+2)+(kernelEnvelope kernels (n+2)+
                  (kernelEnvelope kernels (n+2)+(r*r+(fastLDLCost kernels r+0))))))) := by
              gcongr
              all_goals first | exact ihl _ _ | exact ihr _ _ | apply kernelEnvelope_le
              all_goals omega
            _ ≤ _ := by nlinarith

        · simp only [work_bind, certify_work, ArithmeticKernel.program_work,
            blockScaleProgram_work, work_pure]
          calc
            _ ≤ fastLDLCost kernels l+(l+(kernelEnvelope kernels (n+2)+
                (kernelEnvelope kernels (n+2)+(kernelEnvelope kernels (n+2)+
                  (kernelEnvelope kernels (n+2)+(r*r+(fastLDLCost kernels r+
                    (kernelEnvelope kernels (n+2)+(l*r+(kernelEnvelope kernels (n+2)+0)))))))))) := by
              gcongr
              all_goals first | exact ihl _ _ | exact ihr _ _ | apply kernelEnvelope_le
              all_goals omega
            _ ≤ _ := by nlinarith

theorem fastLDLCost_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p) (n : ℕ) (hn : 1 ≤ n) :
    (fastLDLCost kernels n:ℝ) ≤ 18*(C+1)*(n:ℝ)^p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · omega
    · rw [fastLDLCost]; norm_num; linarith
    · let l := (n+2)/2
      let r := n+2-l
      have hl : l < n+2 := by dsimp [l]; omega
      have hr : r < n+2 := by dsimp [r,l]; omega
      have hl1 : 1 ≤ l := by dsimp [l]; omega
      have hr1 : 1 ≤ r := by dsimp [r,l]; omega
      have hn1 : 1 ≤ n+2 := by omega
      have hnreal : (1:ℝ) ≤ n+2 := by exact_mod_cast hn1
      have hnp : 0 ≤ (n+2:ℝ)^p := Real.rpow_nonneg (by positivity) _
      have ihl := ih l hl hl1
      have ihr := ih r hr hr1
      have hs := balanced_rpow_split (n+2) (by omega) p hp
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at hs
      change (l:ℝ)^p+(r:ℝ)^p ≤ (5/9:ℝ)*(n+2:ℝ)^p at hs
      have hrec : (fastLDLCost kernels l:ℝ)+(fastLDLCost kernels r:ℝ) ≤
          (18*(C+1))*((5/9:ℝ)*(n+2:ℝ)^p) := by
        calc
          _ ≤ 18*(C+1)*(l:ℝ)^p+18*(C+1)*(r:ℝ)^p := add_le_add ihl ihr
          _ = 18*(C+1)*((l:ℝ)^p+(r:ℝ)^p) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      have hk := kernelEnvelope_bound kernels C p hC hK (n+2) hn1
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at hk
      have hquadratic : (n+2:ℝ)*(n+2:ℝ) ≤ (n+2:ℝ)^p := by
        simpa only [Real.rpow_two, pow_two] using Real.rpow_le_rpow_of_exponent_le hnreal hp
      rw [fastLDLCost]
      change ((fastLDLCost kernels l+fastLDLCost kernels r+
        6*kernelEnvelope kernels (n+2)+2*(n+2)*(n+2):ℕ):ℝ) ≤ _
      push_cast
      rw [show (n:ℝ)+1+1 = n+2 by ring]
      nlinarith

theorem exists_fast_inertia_diagonal_program (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (D : Core n) (hD : Dᵀ = D), 1 ≤ n →
        (fastInertiaDiagonalProgram kernels n D hD).admissible ∧
        ((fastInertiaDiagonalProgram kernels n D hD).work:ℝ) ≤ C*(n:ℝ)^(9/4+ζ) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_padded_arithmetic_kernels ζ hζ
  refine ⟨kernels,18*(C+1),by positivity,?_⟩
  intro n D hD hn
  refine ⟨fastInertiaDiagonalProgram_admissible kernels n D hD,?_⟩
  rw [fastInertiaDiagonalProgram_work]
  apply (show ((fastInertiaProgram kernels n D hD).work:ℝ) ≤ (fastLDLCost kernels n:ℝ)
    by exact_mod_cast fastInertiaProgram_work_le kernels n D hD).trans
  apply fastLDLCost_bound kernels C (9/4+ζ) hC (by linarith) _ n hn
  intro a b c N hmax _hN ha hb hc
  apply (hK a b c hmax).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast max_le ha (max_le hb hc)) (by linarith)
end
end HierarchicalAbsoluteSpectral
