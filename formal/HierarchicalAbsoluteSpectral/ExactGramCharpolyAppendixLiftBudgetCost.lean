import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftCost

/-! Arbitrary-rank rectangular budgets for the literal physical lift. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem exactGramAppendixLiftProgram_work_bound_rectangular
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C exponent leftCost rightCost outputCost : ℝ) (hC : 0 < C) (hexponent : 2 ≤ exponent)
    (hcore : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N:ℝ)^exponent)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K)
    (hr : out.negativeCount ≤ r) (hm : 1 ≤ m) (hk : k ≤ m)
    (hforward : ∀ w : ℕ, w ≤ r → ((kernels n m w).cost : ℝ) ≤ leftCost)
    (hgram : ∀ w : ℕ, w ≤ r → w ≤ m → ((kernels w n w).cost : ℝ) ≤ leftCost)
    (hbasis : ∀ w v : ℕ, w ≤ r → w ≤ m → v ≤ w → ((kernels n w v).cost : ℝ) ≤ leftCost)
    (hleft : ∀ v : ℕ, v ≤ r → ((kernels v n m).cost : ℝ) ≤ leftCost)
    (hright : ∀ v : ℕ, v ≤ r → ((kernels v m p).cost : ℝ) ≤ rightCost)
    (houtput : ∀ v : ℕ, v ≤ r → ((kernels n v p).cost : ℝ) ≤ outputCost) :
    ((exactGramAppendixLiftProgram kernels A B T out hr).work : ℝ) ≤
      10*(C+1)*(m:ℝ)^exponent+4*leftCost+rightCost+outputCost := by
  have hsr (s : ExactGramNegativeSelection out.diagonal) : s.width ≤ r := by
    calc s.width = out.negativeCount := s.width_eq
         _ ≤ r := hr
  have hsmall (s : ExactGramNegativeSelection out.diagonal) :
      ((kernels m k s.width).cost : ℝ) ≤ C*(m:ℝ)^exponent :=
    hcore m k s.width m hm le_rfl hk (s.width_le.trans hk)
  have hforward' (s : ExactGramNegativeSelection out.diagonal) :
      ((kernels n m s.width).cost : ℝ) ≤ leftCost := hforward _ (hsr s)
  have hRange (s : ExactGramNegativeSelection out.diagonal)
      (Y : Matrix (Fin n) (Fin s.width) ℝ) :
      ((orthogonalRangeProgram kernels Y).work : ℝ) ≤ 9*(C+1)*(m:ℝ)^exponent+2*leftCost := by
    apply exactGramAppendixLift_range_work_bound kernels C exponent leftCost hC hexponent
      hcore Y m hm (s.width_le.trans hk) (hgram _ (hsr s) (s.width_le.trans hk))
    intro v hv
    exact hbasis _ _ (hsr s) (s.width_le.trans hk) hv
  have hprojection (s : ExactGramNegativeSelection out.diagonal)
      (Y : Matrix (Fin n) (Fin s.width) ℝ) (qr : OrthogonalRange Y) (hqr : qr.dimension ≤ r) :
      ((projectionOutputProgram kernels A B qr.basis hqr).work : ℝ) ≤ leftCost+rightCost+outputCost := by
    have hl := hleft _ hqr
    have hb := hright _ hqr
    have ho := houtput _ hqr
    rw [projectionOutputProgram_work]
    push_cast
    linarith
  have hkpow : (k:ℝ) ≤ (m:ℝ)^exponent := by
    calc
      _ ≤ (m:ℝ) := by exact_mod_cast hk
      _ = (m:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  rw [exactGramAppendixLiftProgram_work]
  simp only [exactGramAppendixLiftDataProgram, work_bind, certify_work,
    exactGramNegativeSelectionProgram_work, ArithmeticKernel.program_work, work_pure,
    Nat.cast_add, Nat.cast_zero]
  calc
    _ ≤ (k:ℝ)+(C*(m:ℝ)^exponent+(leftCost+
        ((9*(C+1)*(m:ℝ)^exponent+2*leftCost)+((leftCost+rightCost+outputCost)+0)))) := by
      gcongr
      · exact hsmall _
      · exact hforward' _
      · exact hRange _ _
      · exact hprojection _ _ _ _
    _ ≤ _ := by nlinarith

end
end HierarchicalAbsoluteSpectral
