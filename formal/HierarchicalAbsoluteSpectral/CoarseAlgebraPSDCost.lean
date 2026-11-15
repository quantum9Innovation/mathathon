import HierarchicalAbsoluteSpectral.CoarseAlgebraPSDProgram
import HierarchicalAbsoluteSpectral.CholeskyCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open ArithmeticProgram hiding pure

def kernelEnvelopeEntry (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (N : ℕ)
    (i : Fin (N+1) × Fin (N+1) × Fin (N+1)) : ℕ :=
  if max i.1.val (max i.2.1.val i.2.2.val) = 0 then 0
  else (kernels i.1.val i.2.1.val i.2.2.val).cost

def kernelEnvelope (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (N : ℕ) : ℕ :=
  Finset.univ.sup (kernelEnvelopeEntry kernels N)

theorem kernelEnvelope_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (N a b c : ℕ) (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N)
    (hm : 1 ≤ max a (max b c)) : (kernels a b c).cost ≤ kernelEnvelope kernels N := by
  let i : Fin (N+1) × Fin (N+1) × Fin (N+1) :=
    (⟨a,by omega⟩,⟨b,by omega⟩,⟨c,by omega⟩)
  have he := Finset.le_sup (f := kernelEnvelopeEntry kernels N) (Finset.mem_univ i)
  simpa only [kernelEnvelope, kernelEnvelopeEntry, i, if_neg (show max a (max b c) ≠ 0 by omega)] using he

theorem kernelEnvelope_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p) (N : ℕ) (hN : 1 ≤ N) :
    (kernelEnvelope kernels N:ℝ) ≤ C*(N:ℝ)^p := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset
    (Fin (N+1) × Fin (N+1) × Fin (N+1))) Finset.univ_nonempty (kernelEnvelopeEntry kernels N)
  change ((Finset.univ.sup (kernelEnvelopeEntry kernels N):ℕ):ℝ) ≤ _
  rw [hi]
  unfold kernelEnvelopeEntry
  split_ifs with hz
  · simp only [Nat.cast_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  · exact hK _ _ _ N (by omega) hN (by omega) (by omega) (by omega)

def psdGramCost (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | n+2 => psdGramCost kernels ((n+2)/2)+psdGramCost kernels (n+2-(n+2)/2)+
      4*kernelEnvelope kernels (n+2)+(n+2)*(n+2)
termination_by n => n
decreasing_by all_goals omega

theorem PSDGramPair.dimension_le_fin {a : ℕ} {D : Core a} (p : PSDGramPair D) : p.dimension ≤ a := by
  simpa only [Fintype.card_fin] using p.dimension_le

theorem psdGramProgram_work_le (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (n : ℕ) (D : Core n) (hD : D.PosSemidef) :
    (psdGramProgram kernels n D hD).work ≤ psdGramCost kernels n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [psdGramProgram, psdGramCost]; rfl
    · rw [psdGramProgram, psdGramCost]; exact psdSingleProgram_work D hD
    · let l := (n+2)/2
      let r := n+2-l
      have hl : l < n+2 := by dsimp [l]; omega
      have hr : r < n+2 := by dsimp [r, l]; omega
      have hl1 : 1 ≤ l := by dsimp [l]; omega
      have hr1 : 1 ≤ r := by dsimp [r, l]; omega
      have he : l+r = n+2 := by dsimp [l, r]; omega
      have ihl := ih l hl
      have ihr := ih r hr
      rw [psdGramProgram, psdGramCost]
      simp only [work_bind, certify_work, ArithmeticKernel.program_work,
        blockSubProgram_work, blockScaleProgram_work, work_pure]
      change _ ≤ psdGramCost kernels l+psdGramCost kernels r+
        4*kernelEnvelope kernels (n+2)+(n+2)*(n+2)
      calc
        _ ≤ psdGramCost kernels l+(kernelEnvelope kernels (n+2)+
            (kernelEnvelope kernels (n+2)+(r*r+(psdGramCost kernels r+
              (kernelEnvelope kernels (n+2)+(kernelEnvelope kernels (n+2)+(r*l+0))))))) := by
          gcongr
          all_goals first | exact ihl _ _ | exact ihr _ _ | apply kernelEnvelope_le | skip
          all_goals first | omega | exact Nat.le_trans (PSDGramPair.dimension_le_fin _) (by omega)
        _ ≤ _ := by nlinarith

theorem psdGramCost_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p) (n : ℕ) (hn : 1 ≤ n) :
    (psdGramCost kernels n:ℝ) ≤ 9*(C+1)*(n:ℝ)^p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · omega
    · rw [psdGramCost]; norm_num; linarith
    · let l := (n+2)/2
      let r := n+2-l
      have hl : l < n+2 := by dsimp [l]; omega
      have hr : r < n+2 := by dsimp [r, l]; omega
      have hl1 : 1 ≤ l := by dsimp [l]; omega
      have hr1 : 1 ≤ r := by dsimp [r, l]; omega
      have hn1 : 1 ≤ n+2 := by omega
      have hnreal : (1:ℝ) ≤ n+2 := by exact_mod_cast hn1
      have hnp : 0 ≤ (n+2:ℝ)^p := Real.rpow_nonneg (by positivity) _
      have ihl := ih l hl hl1
      have ihr := ih r hr hr1
      have hs := balanced_rpow_split (n+2) (by omega) p hp
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at hs
      change (l:ℝ)^p+(r:ℝ)^p ≤ (5/9:ℝ)*(n+2:ℝ)^p at hs
      have hrec : (psdGramCost kernels l:ℝ)+(psdGramCost kernels r:ℝ) ≤
          (9*(C+1))*((5/9:ℝ)*(n+2:ℝ)^p) := by
        calc
          _ ≤ 9*(C+1)*(l:ℝ)^p+9*(C+1)*(r:ℝ)^p := add_le_add ihl ihr
          _ = 9*(C+1)*((l:ℝ)^p+(r:ℝ)^p) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      have hk := kernelEnvelope_bound kernels C p hC hK (n+2) hn1
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at hk
      have hquadratic : (n+2:ℝ)*(n+2:ℝ) ≤ (n+2:ℝ)^p := by
        simpa only [Real.rpow_two, pow_two] using Real.rpow_le_rpow_of_exponent_le hnreal hp
      rw [psdGramCost]
      change ((psdGramCost kernels l+psdGramCost kernels r+
        4*kernelEnvelope kernels (n+2)+(n+2)*(n+2):ℕ):ℝ) ≤ _
      push_cast
      rw [show (n:ℝ)+1+1 = n+2 by ring]
      nlinarith

end
end HierarchicalAbsoluteSpectral
