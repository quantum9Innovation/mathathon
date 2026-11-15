import HierarchicalAbsoluteSpectral.BaseKernelCosts
import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedCyclicRowFamily

/-! Bounds for the manuscript's actual symmetric, monotone product cost.
Every rectangular downset and all six tensor-leg permutations are included. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matmul.RectangularPrograms

theorem rectangularKernelCost_real_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (A B C : ℕ)
    (R : ℝ) (hR : 0 ≤ R)
    (hK : ∀ a b c : ℕ, a ≤ A → b ≤ B → c ≤ C → ((K a b c).cost:ℝ) ≤ R) :
    (rectangularKernelCost K A B C:ℝ) ≤ R := by
  have hh : rectangularKernelCost K A B C ≤ ⌊R⌋₊ := by
    apply Finset.sup_le
    intro i _
    apply Finset.sup_le
    intro j _
    apply Finset.sup_le
    intro k _
    exact Nat.le_floor (hK i.val j.val k.val (by omega) (by omega) (by omega))
  exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hR)

theorem symmetricKernelCost_real_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (a b c : ℕ)
    (R : ℝ) (hR : 0 ≤ R)
    (h1 : (rectangularKernelCost K a b c:ℝ) ≤ R)
    (h2 : (rectangularKernelCost K a c b:ℝ) ≤ R)
    (h3 : (rectangularKernelCost K b a c:ℝ) ≤ R)
    (h4 : (rectangularKernelCost K b c a:ℝ) ≤ R)
    (h5 : (rectangularKernelCost K c a b:ℝ) ≤ R)
    (h6 : (rectangularKernelCost K c b a:ℝ) ≤ R) :
    (symmetricKernelCost K a b c:ℝ) ≤ R := by
  have hh : symmetricKernelCost K a b c ≤ ⌊R⌋₊ := by
    unfold symmetricKernelCost
    exact max_le (Nat.le_floor h1) (max_le (Nat.le_floor h2)
      (max_le (Nat.le_floor h3) (max_le (Nat.le_floor h4)
        (max_le (Nat.le_floor h5) (Nat.le_floor h6)))))
  exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hR)

theorem symmetricKernelCost_fixed_six_row_bound {m : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 0 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (s b : ℕ) (hb : b ≤ 2*width (1/2) m) :
    (symmetricKernelCost K s m b:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) := by
  let R : ℝ := 8*χ*(s+m:ℕ)*(m:ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hgrow (a : ℕ) (ha : a ≤ s) : 8*χ*(a+m:ℕ)*(m:ℝ) ≤ R := by
    dsimp only [R]
    gcongr
  apply symmetricKernelCost_real_bound K s m b R hR
  · apply rectangularKernelCost_real_bound K s m b R hR
    intro a d c ha hd hc
    exact (hrow.forward a d c hd (hc.trans hb)).trans (hgrow a ha)
  · apply rectangularKernelCost_real_bound K s b m R hR
    intro a d c ha hd hc
    exact (hrow.cyclic_forward a d c (hd.trans hb) hc).trans (hgrow a ha)
  · apply rectangularKernelCost_real_bound K m s b R hR
    intro a d c ha hd hc
    exact (hrow.adjoint a d c ha (hc.trans hb)).trans (hgrow d hd)
  · apply rectangularKernelCost_real_bound K m b s R hR
    intro a d c ha hd hc
    exact (hrow.cyclic_transpose a d c ha (hd.trans hb)).trans (hgrow c hc)
  · apply rectangularKernelCost_real_bound K b s m R hR
    intro a d c ha hd hc
    exact (hrow.transpose_adjoint a d c (ha.trans hb) hc).trans (hgrow d hd)
  · apply rectangularKernelCost_real_bound K b m s R hR
    intro a d c ha hd hc
    exact (hrow.transpose_forward a d c (ha.trans hb) hd).trans (hgrow c hc)

theorem matrixProductCost_fixed_six_row_bound {m : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (s b : ℕ) (hm : 1 ≤ m) (hb : b ≤ 2*width (1/2) m) :
    (matrixProductCost K s m b:ℝ) ≤ 16*χ*(s+m:ℕ)*(m:ℝ) := by
  have hχ0 : 0 ≤ χ := (by norm_num : (0:ℝ) ≤ 1).trans hχ
  have hs := symmetricKernelCost_fixed_six_row_bound K χ hχ0 hrow s b hb
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hb' : (b:ℝ) ≤ 2*m := by
    exact_mod_cast hb.trans (Nat.mul_le_mul_left 2 (half_width_le m hm))
  have hbase : (s:ℝ)*m+(m:ℝ)^2 ≤ χ*(s+m:ℕ)*(m:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hχ
      (show 0 ≤ (s+m:ℕ)*(m:ℝ) by positivity)
    push_cast at hh ⊢
    nlinarith only [hh]
  have hsm : 0 ≤ (s:ℝ)*m := by positivity
  have hsq : 1 ≤ (m:ℝ)^2 := by nlinarith only [hm1]
  have hunit : 1 ≤ χ*(s+m:ℕ)*(m:ℝ) := by nlinarith only [hbase,hsm,hsq]
  have hmb := mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg m)
  have hbs := mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg s)
  have hvol : (s:ℝ)*m+(m:ℝ)*b+(b:ℝ)*s+1 ≤ 6*χ*(s+m:ℕ)*(m:ℝ) := by
    nlinarith only [hbase,hunit,hmb,hbs,hsm,hsq]
  push_cast at hs hvol hunit
  simp only [matrixProductCost, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  nlinarith only [hs,hvol,hunit]

theorem matrixProductCost_fixed_six_subshape_bound {m : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (s k b : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    (matrixProductCost K s k b:ℝ) ≤ 16*χ*(s+m:ℕ)*(m:ℝ) :=
  (Nat.cast_le.mpr (matrixProductCost_mono K le_rfl hk le_rfl)).trans
    (matrixProductCost_fixed_six_row_bound K χ hχ hrow s b hm hb)

theorem matrixProductCost_fixed_input_pair_bound {m : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (n p N b : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hb : b ≤ 2*width (1/2) m) :
    ((matrixProductCost K n m b+matrixProductCost K p m b:ℕ):ℝ) ≤ 64*χ*(m:ℝ)*(N:ℝ) := by
  have hχ0 : 0 ≤ χ := (by norm_num : (0:ℝ) ≤ 1).trans hχ
  have h1 := matrixProductCost_fixed_six_row_bound K χ hχ hrow n b hm hb
  have h2 := matrixProductCost_fixed_six_row_bound K χ hχ hrow p b hm hb
  have hdim : (n+m:ℕ)+(p+m:ℕ) ≤ 4*(N:ℝ) := by exact_mod_cast (show n+m+(p+m) ≤ 4*N by omega)
  have hscale := mul_le_mul_of_nonneg_left hdim (show 0 ≤ 16*χ*(m:ℝ) by positivity)
  push_cast at h1 h2 hdim hscale ⊢
  nlinarith only [h1,h2,hscale]

theorem matrixProductCost_fixed_fine_pair_bound {m : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedSixRowKernelEnvelopes m K χ)
    (s t b : ℕ) (hm : 1 ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((matrixProductCost K s m b+matrixProductCost K t m b:ℕ):ℝ) ≤
      32*χ*(m:ℝ)*(s+t+m:ℕ) := by
  have hχ0 : 0 ≤ χ := (by norm_num : (0:ℝ) ≤ 1).trans hχ
  have h1 := matrixProductCost_fixed_six_row_bound K χ hχ hrow s b hm hb
  have h2 := matrixProductCost_fixed_six_row_bound K χ hχ hrow t b hm hb
  have hn : 0 ≤ χ*(s+t:ℕ)*(m:ℝ) := by positivity
  push_cast at h1 h2 hn ⊢
  nlinarith only [h1,h2,hn]

theorem symmetricKernelCost_fixed_output_bound {N : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χOut : ℝ) (hχOut : 0 ≤ χOut)
    (hout : FixedOutputKernelEnvelopes N K χOut)
    (r : ℕ) (hr : r ≤ width (1/2) N) :
    (symmetricKernelCost K N r N:ℝ) ≤ (N:ℝ)^2*χOut := by
  let R : ℝ := (N:ℝ)^2*χOut
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have h1 : (rectangularKernelCost K N r N:ℝ) ≤ R := by
    apply rectangularKernelCost_real_bound K N r N R hR
    intro a b c ha hb hc
    exact hout.dense_output a b c ha (hb.trans hr) hc
  have h2 : (rectangularKernelCost K N N r:ℝ) ≤ R := by
    apply rectangularKernelCost_real_bound K N N r R hR
    intro a b c ha hb hc
    exact hout.outer a b c ha hb (hc.trans hr)
  have h3 : (rectangularKernelCost K r N N:ℝ) ≤ R := by
    apply rectangularKernelCost_real_bound K r N N R hR
    intro a b c ha hb hc
    exact hout.transpose_outer a b c (ha.trans hr) hb hc
  exact symmetricKernelCost_real_bound K N r N R hR h1 h2 h3 h3 h2 h1

theorem matrixProductCost_fixed_output_half_bound {N : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χOut : ℝ) (hχOut : 1 ≤ χOut)
    (hout : FixedOutputKernelEnvelopes N K χOut)
    (r : ℕ) (hN : 1 ≤ N) (hr : r ≤ width (1/2) N) :
    (matrixProductCost K N r N:ℝ) ≤ 5*χOut*(N:ℝ)^2 := by
  have hχ0 : 0 ≤ χOut := (by norm_num : (0:ℝ) ≤ 1).trans hχOut
  have hs := symmetricKernelCost_fixed_output_bound K χOut hχ0 hout r hr
  have hNr : (r:ℝ) ≤ N := by exact_mod_cast hr.trans (half_width_le N hN)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : 1 ≤ (N:ℝ)^2 := by nlinarith only [hN1]
  have hscale := mul_le_mul_of_nonneg_right hχOut (sq_nonneg (N:ℝ))
  have h1 := mul_le_mul_of_nonneg_left hNr (Nat.cast_nonneg N)
  have h2 := mul_le_mul_of_nonneg_right hNr (Nat.cast_nonneg N)
  simp only [matrixProductCost, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  nlinarith only [hs,hsq,hscale,h1,h2]

theorem matrixProductCost_fixed_output_sqrt_bound {N : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χOut : ℝ) (hχOut : 1 ≤ χOut)
    (hout : FixedOutputKernelEnvelopes N K χOut)
    (n m r p : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    (matrixProductCost K n r p:ℝ) ≤ 5*χOut*(N:ℝ)^2 := by
  apply (Nat.cast_le.mpr (matrixProductCost_mono K hn le_rfl hp)).trans
  apply matrixProductCost_fixed_output_half_bound K χOut hχOut hout r (by omega)
  exact sqrt_rank_fits_outer_width (1/2) le_rfl m N r hm hmN hr

theorem matrixProductCost_fixed_output_sqrt_max_bound {N : ℕ}
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ χOut : ℝ) (hχOut : 1 ≤ χOut)
    (hout : FixedOutputKernelEnvelopes N K χOut)
    (n m r p : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    (matrixProductCost K n r p:ℝ) ≤ 5*max χ χOut*(N:ℝ)^2 := by
  apply (matrixProductCost_fixed_output_sqrt_bound K χOut hχOut hout n m r p hm hmN hn hp hr).trans
  gcongr
  exact le_max_right χ χOut

end
end HierarchicalAbsoluteSpectral
