import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixSupportSpectral
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftBudgetCost
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftRawBound

/-! The literal whole-support output branch, with the same rectangular
budgets as the negative-diagonal lift branch. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem exactGramAppendixExactOutputProgram_work_bound_rectangular
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C exponent leftCost rightCost outputCost : ℝ) (hC : 0 < C) (hexponent : 2 ≤ exponent)
    (hcore : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N:ℝ)^exponent)
    {n m p r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (support : ExactGramAppendixSupport A B) (hfull : support.dimension ≤ r) (hm : 1 ≤ m)
    (hforward : ∀ w : ℕ, w ≤ r → ((kernels n m w).cost : ℝ) ≤ leftCost)
    (hgram : ∀ w : ℕ, w ≤ r → w ≤ m → ((kernels w n w).cost : ℝ) ≤ leftCost)
    (hbasis : ∀ w v : ℕ, w ≤ r → w ≤ m → v ≤ w → ((kernels n w v).cost : ℝ) ≤ leftCost)
    (hleft : ∀ v : ℕ, v ≤ r → ((kernels v n m).cost : ℝ) ≤ leftCost)
    (hright : ∀ v : ℕ, v ≤ r → ((kernels v m p).cost : ℝ) ≤ rightCost)
    (houtput : ∀ v : ℕ, v ≤ r → ((kernels n v p).cost : ℝ) ≤ outputCost) :
    ((support.exactOutputProgram kernels r hfull).work : ℝ) ≤
      10*(C+1)*(m:ℝ)^exponent+4*leftCost+rightCost+outputCost := by
  have hk := support.dimension_le
  have hsmall := hcore m support.dimension support.dimension m hm le_rfl hk hk
  have hforward' := hforward support.dimension hfull
  have haction : ((support.action kernels support.dimension).cost : ℝ) ≤
      C*(m:ℝ)^exponent+leftCost := by
    change (((kernels n m support.dimension).cost+
      (kernels m support.dimension support.dimension).cost : ℕ) : ℝ) ≤ _
    push_cast
    linarith
  have hactionWork : (((support.action kernels support.dimension).program
      (1 : Core support.dimension)).work : ℝ) ≤ C*(m:ℝ)^exponent+leftCost := by
    apply le_trans _ haction
    exact_mod_cast (support.action kernels support.dimension).work_le (1 : Core support.dimension)
  have hRange (Y : Matrix (Fin n) (Fin support.dimension) ℝ) :
      ((orthogonalRangeProgram kernels Y).work : ℝ) ≤
        9*(C+1)*(m:ℝ)^exponent+2*leftCost := by
    apply exactGramAppendixLift_range_work_bound kernels C exponent leftCost hC hexponent
      hcore Y m hm hk (hgram _ hfull hk)
    intro v hv
    exact hbasis _ _ hfull hk hv
  have hphysical : ((physicalRangeProgram kernels (support.action kernels support.dimension)
      (1 : Core support.dimension)).work : ℝ) ≤
      (C*(m:ℝ)^exponent+leftCost)+(9*(C+1)*(m:ℝ)^exponent+2*leftCost) := by
    simp only [physicalRangeProgram, work_bind, certify_work, work_pure, add_zero, Nat.cast_add]
    exact add_le_add hactionWork (hRange _)
  have hprojection (Y : Matrix (Fin n) (Fin support.dimension) ℝ)
      (qr : OrthogonalRange Y) (hqr : qr.dimension ≤ r) :
      ((projectionOutputProgram kernels A B qr.basis hqr).work : ℝ) ≤ leftCost+rightCost+outputCost := by
    have hl := hleft _ hqr
    have hb := hright _ hqr
    have ho := houtput _ hqr
    rw [projectionOutputProgram_work]
    push_cast
    linarith
  simp only [ExactGramAppendixSupport.exactOutputProgram, supportExactOutputProgram,
    exactPhysicalOutputProgram, work_bind, Nat.cast_add]
  calc
    _ ≤ ((C*(m:ℝ)^exponent+leftCost)+(9*(C+1)*(m:ℝ)^exponent+2*leftCost))+
        (leftCost+rightCost+outputCost) := add_le_add hphysical (hprojection _ _ _)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (Nat.cast_nonneg m) exponent]

end
end HierarchicalAbsoluteSpectral
