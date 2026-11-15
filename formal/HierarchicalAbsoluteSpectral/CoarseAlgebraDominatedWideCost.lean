import HierarchicalAbsoluteSpectral.CoarseAlgebraWideCost
import HierarchicalAbsoluteSpectral.CoarseAlgebraKernelSelection

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem dominated_psdGramProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hK : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    (cap : ℕ) (hc : 1 ≤ cap)
    (n : ℕ) (D : Core n) (hD : D.PosSemidef) (hRank : D.rank ≤ cap) :
    (psdGramProgram kernels n D hD).work ≤ 18*cap*n*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [psdGramProgram]; simp
    · rw [psdGramProgram]
      apply (psdSingleProgram_work D hD).trans
      nlinarith
    · let l := (n+2)/2
      let r := n+2-l
      have hl : l < n+2 := by dsimp [l]; omega
      have hr : r < n+2 := by dsimp [r,l]; omega
      have he : l+r=n+2 := by dsimp [l,r]; omega
      let e : Fin l ⊕ Fin r ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr he)
      let D' := D.submatrix e e
      have hp : D'.PosSemidef := hD.submatrix e
      have hb := hermitian_block_decomposition D' hp.isHermitian
      have hfull : D'.rank ≤ cap := by rw [Matrix.rank_submatrix]; exact hRank
      have hA : D'.toBlocks₁₁.PosSemidef := hp.submatrix Sum.inl
      have hArank : D'.toBlocks₁₁.rank ≤ cap :=
        (Matrix.rank_submatrix_le D' Sum.inl Sum.inl).trans hfull
      let p := (psdGramProgram kernels l D'.toBlocks₁₁ hA).eval
      let T := psdSchur p D'.toBlocks₁₂ D'.toBlocks₂₂
      have hTpos : T.PosSemidef := psdSchur_posSemidef p _ _ (hb.symm ▸ hp)
      have hTrank : T.rank ≤ cap := by
        apply (psdSchur_rank_le p _ _ (hb.symm ▸ hp)).trans
        rw [hb]
        exact hfull
      let Hraw := (certify ((kernels p.dimension l r).program p.leftInverse D'.toBlocks₁₂)).eval
      let Rraw := (certify ((kernels r p.dimension r).program Hraw.valᵀ Hraw.val)).eval
      let Traw := (certify (blockSubProgram D'.toBlocks₂₂ Rraw.val)).eval
      have hTraw : Traw.val=T := by
        dsimp [Traw,Rraw,Hraw]
        simp only [certify_eval,blockSubProgram_eval,ArithmeticKernel.program_eval,T,psdSchur]
      have hTrawpos : Traw.val.PosSemidef := hTraw.symm ▸ hTpos
      have hTrawrank : Traw.val.rank ≤ cap := by rw [hTraw]; exact hTrank
      let q := (psdGramProgram kernels r Traw.val hTrawpos).eval
      have hpcap : p.dimension ≤ cap := p.dimension_eq_rank.trans_le hArank
      have hpdim : p.dimension ≤ l := p.dimension_le_fin
      have hqcap : q.dimension ≤ cap := q.dimension_eq_rank.trans_le hTrawrank
      have hqdim : q.dimension ≤ r := q.dimension_le_fin
      have ihl := ih l hl _ hA hArank
      have ihr := ih r hr _ hTrawpos hTrawrank
      have hK1 := hK p.dimension l r
      have hK2 := hK r p.dimension r
      have hK3 := hK q.dimension r p.dimension
      have hK4 := hK q.dimension p.dimension l
      rw [psdGramProgram]
      simp only [work_bind,certify_work,ArithmeticKernel.program_work,
        blockSubProgram_work,blockScaleProgram_work,work_pure]
      change (psdGramProgram kernels l D'.toBlocks₁₁ hA).work+
        ((kernels p.dimension l r).cost+((kernels r p.dimension r).cost+(r*r+
          ((psdGramProgram kernels r Traw.val hTrawpos).work+
            ((kernels q.dimension r p.dimension).cost+((kernels q.dimension p.dimension l).cost+
              (q.dimension*l+0))))))) ≤ _
      calc
        _ ≤ 18*cap*l*l+(2*p.dimension*l*r+(2*r*p.dimension*r+(r*r+
            (18*cap*r*r+(2*q.dimension*r*p.dimension+(2*q.dimension*p.dimension*l+(q.dimension*l+0))))))) := by omega
        _ ≤ 18*cap*l*l+(2*cap*l*r+(2*r*cap*r+(r*r+
            (18*cap*r*r+(2*cap*r*l+(2*cap*l*l+(r*l+0))))))) := by gcongr
        _ ≤ 18*cap*(n+2)*(n+2) := by
          have hs := balanced_rpow_split (n+2) (by omega) (2:ℝ) le_rfl
          norm_num only [Real.rpow_two,Nat.cast_add,Nat.cast_ofNat] at hs
          change (l:ℝ)^2+(r:ℝ)^2 ≤ (5/9:ℝ)*(n+2:ℝ)^2 at hs
          have hbal : 9*(l*l+r*r) ≤ 5*(n+2)*(n+2) := by
            exact_mod_cast (show 9*((l:ℝ)*(l:ℝ)+(r:ℝ)*(r:ℝ)) ≤ 5*(n+2:ℝ)*(n+2:ℝ) by nlinarith)
          have hbcap := Nat.mul_le_mul_left (2*cap) hbal
          have he2 : l*l+2*l*r+r*r=(n+2)*(n+2) := by rw [←he]; ring
          have hecap := congrArg (fun x : ℕ => 2*cap*x) he2
          have hsmall : r*r+r*l ≤ (n+2)*(n+2) := by nlinarith
          have hcap := Nat.mul_le_mul_right ((n+2)*(n+2)) hc
          nlinarith

/-- Any kernel family offered the classical circuit as a cheaper alternative
retains the rank-sensitive all-outcome wide-block bound. -/
theorem dominated_orthogonalRangeProgram_work
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (hK : ∀ a b c : ℕ, (kernels a b c).cost ≤ 2*a*b*c)
    {m w : ℕ} (Y : Matrix (Fin m) (Fin w) ℝ) (hm : 1 ≤ m) :
    (orthogonalRangeProgram kernels Y).work ≤ 22*m*w*w := by
  let G := (certify ((kernels w m w).program Yᵀ Y)).eval
  have hG : G.val=Yᵀ*Y := by dsimp [G]; simp only [certify_eval,ArithmeticKernel.program_eval]
  have hGpos : G.val.PosSemidef := by
    rw [hG]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self Y
  have hRank : G.val.rank ≤ m := by
    rw [hG,Matrix.rank_transpose_mul_self]
    simpa only [Fintype.card_fin] using Matrix.rank_le_card_height Y
  let p := (psdGramProgram kernels w G.val hGpos).eval
  have hdim : p.dimension ≤ w := p.dimension_le_fin
  have hpwork := dominated_psdGramProgram_work kernels hK m hm w G.val hGpos hRank
  have hK1 := hK w m w
  have hK2 := hK m w p.dimension
  simp only [orthogonalRangeProgram,work_bind,certify_work,ArithmeticKernel.program_work,work_pure,add_zero]
  change (kernels w m w).cost+((psdGramProgram kernels w G.val hGpos).work+
    (kernels m w p.dimension).cost) ≤ _
  have hlast : 2*m*w*p.dimension ≤ 2*m*w*w := Nat.mul_le_mul_left _ hdim
  nlinarith

def classicallyDominatedKernels (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    ∀ a b c : ℕ, ArithmeticKernel a b c :=
  fun a b c => (kernels a b c).cheaper (classicalArithmeticKernels a b c)

theorem classicallyDominatedKernels_cost_le
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) :
    (classicallyDominatedKernels kernels a b c).cost ≤ (kernels a b c).cost :=
  ArithmeticKernel.cheaper_cost_le_left _ _

theorem classicallyDominatedKernels_cost_classical
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ) :
    (classicallyDominatedKernels kernels a b c).cost ≤ 2*a*b*c := by
  exact (ArithmeticKernel.cheaper_cost_le_right _ _).trans_eq (classicalArithmeticKernels_cost a b c)

end
end HierarchicalAbsoluteSpectral
