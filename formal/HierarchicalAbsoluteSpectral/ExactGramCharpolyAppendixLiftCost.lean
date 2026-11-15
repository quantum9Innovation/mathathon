import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftProgram
import HierarchicalAbsoluteSpectral.CoarseAlgebraOutputCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem exactGramAppendixLift_range_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C exponent a : ℝ) (hC : 0 < C) (hexponent : 2 ≤ exponent)
    (hcore : ∀ i j l N : ℕ, 1 ≤ N → i ≤ N → j ≤ N → l ≤ N →
      ((kernels i j l).cost : ℝ) ≤ C*(N:ℝ)^exponent)
    {n w : ℕ} (Y : Matrix (Fin n) (Fin w) ℝ)
    (m : ℕ) (hm : 1 ≤ m) (hw : w ≤ m)
    (hgram : ((kernels w n w).cost : ℝ) ≤ a)
    (hbasis : ∀ v : ℕ, v ≤ w → ((kernels n w v).cost : ℝ) ≤ a) :
    ((orthogonalRangeProgram kernels Y).work : ℝ) ≤ 9*(C+1)*(m:ℝ)^exponent+2*a := by
  have hcost : (psdGramCost kernels w : ℝ) ≤ 9*(C+1)*(m:ℝ)^exponent := by
    by_cases hw1 : 1 ≤ w
    · apply (psdGramCost_bound kernels C exponent hC hexponent
        (fun i j l N _ => hcore i j l N) w hw1).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hw) (by linarith)
    · have hw0 : w = 0 := by omega
      rw [hw0, psdGramCost]
      simp only [Nat.cast_zero]
      positivity
  have hr : ((orthogonalRangeProgram kernels Y).work : ℝ) ≤
      a+((psdGramCost kernels w : ℝ)+a) := by
    simp only [orthogonalRangeProgram, work_bind, certify_work, ArithmeticKernel.program_work,
      work_pure, Nat.cast_add, Nat.cast_zero, add_zero]
    gcongr
    · exact_mod_cast psdGramProgram_work_le kernels _ _ _
    · exact hbasis _ (PSDGramPair.dimension_le_fin _)
  linarith

theorem exactGramAppendixLiftProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η ζ C : ℝ) (hκ : 1/2 ≤ κ) (hζ : 0 ≤ ζ) (hC : 0 < C)
    {N n m p k r : ℕ} (hEnv : HierarchyKernelEnvelopes κ η ζ N m kernels C)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) {K : Core k} (out : FiniteCongruenceDiagonal K)
    (hr : out.negativeCount ≤ r) (hm : 1 ≤ m) (hNm : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hk : k ≤ m) (hwr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    ((exactGramAppendixLiftProgram kernels A B T out hr).work : ℝ) ≤
      10*(C+1)*(m:ℝ)^(9/4+ζ) + 5*C*(N:ℝ)*(m:ℝ)^(1+η) + C*(N:ℝ)^(2+ζ) := by
  have hsr (s : ExactGramNegativeSelection out.diagonal) : s.width ≤ r := by
    calc s.width = out.negativeCount := s.width_eq
         _ ≤ r := hr
  have hrw := sqrt_rank_fits_outer_width κ hκ m m r hm le_rfl hwr
  have hrN := sqrt_rank_fits_outer_width (1/2) le_rfl m N r hm hNm hwr
  have hsmall (s : ExactGramNegativeSelection out.diagonal) :
      ((kernels m k s.width).cost : ℝ) ≤ C*(m:ℝ)^(9/4+ζ) :=
    hEnv.core m k s.width m hm le_rfl hk (s.width_le.trans hk)
  have hforward (s : ExactGramNegativeSelection out.diagonal) :
      ((kernels n m s.width).cost : ℝ) ≤ C*(N:ℝ)*(m:ℝ)^(1+η) :=
    hEnv.forward n m s.width hn le_rfl ((hsr s).trans hrw)
  have hRange (s : ExactGramNegativeSelection out.diagonal)
      (Y : Matrix (Fin n) (Fin s.width) ℝ) : ((orthogonalRangeProgram kernels Y).work : ℝ) ≤
      9*(C+1)*(m:ℝ)^(9/4+ζ)+2*(C*(N:ℝ)*(m:ℝ)^(1+η)) := by
    have hsm := s.width_le.trans hk
    have hsw := (hsr s).trans hrw
    have hg := hEnv.adjoint s.width n s.width hsm hn hsw
    apply exactGramAppendixLift_range_work_bound kernels C (9/4+ζ)
      (C*(N:ℝ)*(m:ℝ)^(1+η)) hC (by linarith) hEnv.core Y m hm hsm hg
    intro v hv
    exact hEnv.forward n s.width v hn hsm (hv.trans hsw)
  have hprojection (s : ExactGramNegativeSelection out.diagonal)
      (Y : Matrix (Fin n) (Fin s.width) ℝ) (qr : OrthogonalRange Y) (hqr : qr.dimension ≤ r) :
      ((projectionOutputProgram kernels A B qr.basis hqr).work : ℝ) ≤
        2*(C*(N:ℝ)*(m:ℝ)^(1+η))+C*(N:ℝ)^(2+ζ) := by
    have hqw := hqr.trans hrw
    have hqN := hqr.trans hrN
    have hl := hEnv.transpose_adjoint qr.dimension n m hqw hn le_rfl
    have hb := hEnv.transpose_forward qr.dimension m p hqw le_rfl hp
    have ho := hEnv.dense_output n qr.dimension p hn hqN hp
    rw [projectionOutputProgram_work]
    push_cast
    linarith
  have hkpow : (k:ℝ) ≤ (m:ℝ)^(9/4+ζ) := by
    have hmreal : (1:ℝ) ≤ m := by exact_mod_cast hm
    calc
      _ ≤ (m:ℝ) := by exact_mod_cast hk
      _ = (m:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hmreal (by linarith)
  rw [exactGramAppendixLiftProgram_work]
  simp only [exactGramAppendixLiftDataProgram, work_bind, certify_work,
    exactGramNegativeSelectionProgram_work, ArithmeticKernel.program_work, work_pure,
    Nat.cast_add, Nat.cast_zero]
  calc
    _ ≤ (k:ℝ)+(C*(m:ℝ)^(9/4+ζ)+(C*(N:ℝ)*(m:ℝ)^(1+η)+
        ((9*(C+1)*(m:ℝ)^(9/4+ζ)+2*(C*(N:ℝ)*(m:ℝ)^(1+η)))+
          ((2*(C*(N:ℝ)*(m:ℝ)^(1+η))+C*(N:ℝ)^(2+ζ))+0)))) := by
      gcongr
      · exact hsmall _
      · exact hforward _
      · exact hRange _ _
      · exact hprojection _ _ _ _
    _ ≤ _ := by nlinarith

end
end HierarchicalAbsoluteSpectral
