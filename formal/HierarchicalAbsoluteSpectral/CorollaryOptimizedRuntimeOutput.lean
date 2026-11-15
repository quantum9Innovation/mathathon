import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedOutputKernelFamily
import HierarchicalAbsoluteSpectral.BaseMainStrongCost

/-! The actual physical range, factor projection and dense expansion caps
fit additive input, small-core and output charges for every returned rank. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Matmul.RectangularPrograms
variable {N m r w L : ℕ}

theorem comparator_nat_sup_real_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ) (B : ℝ) (h : ∀ i, (f i:ℝ) ≤ B) :
    ((Finset.univ.sup f:ℕ):ℝ) ≤ B := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ:Finset ι) Finset.univ_nonempty f
  rw [hi]
  exact h i

theorem comparator_psd_cost_ambient
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C E : ℝ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 1 ≤ m) (hw : w ≤ m) :
    (psdGramCost kernels w:ℝ) ≤ 9*(C+1)*(m:ℝ)^E := by
  by_cases hw1 : 1 ≤ w
  · apply (psdGramCost_bound kernels C E hC hE (fun a b c D _ => hK a b c D) w hw1).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow (Nat.cast_nonneg w) (by exact_mod_cast hw) (by linarith)
  · have hw0 : w=0 := by omega
    rw [hw0,psdGramCost]
    simp only [Nat.cast_zero]
    positivity

theorem comparator_projection_cap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ χOut : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (hout : FixedOutputKernelEnvelopes N kernels χOut)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    (projectionOutputWorkCap kernels N m N r:ℝ) ≤
      32*χ*(N:ℝ)*(m:ℝ)+(N:ℝ)^2*χOut := by
  apply comparator_nat_sup_real_le
  intro w
  have hw : (w.val:ℝ) ≤ Real.sqrt (m:ℝ) :=
    (by exact_mod_cast Nat.le_of_lt_succ w.isLt : (w.val:ℝ) ≤ r).trans hr
  have hwidth := sqrt_rank_fits_outer_width (1/2) le_rfl m m w.val hm le_rfl hw
  have hw2 : w.val ≤ 2*width (1/2) m := by omega
  have hleft := hrow.transpose_adjoint w.val N m hw2 le_rfl
  have hright := hrow.transpose_forward w.val m N hw2 le_rfl
  have hdense := hout.sqrt_rank N m w.val N hm hNm le_rfl hw le_rfl
  have hNmR : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hp : 0 ≤ χ*(m:ℝ) := by positivity
  push_cast at hleft hright ⊢
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hNmR)]

theorem comparator_exact_range_cap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ C E : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hw : (w:ℝ) ≤ Real.sqrt (m:ℝ)) :
    (exactRangeWorkCap kernels N w:ℝ) ≤
      32*χ*(N:ℝ)*(m:ℝ)+9*(C+1)*(m:ℝ)^E := by
  have hwidth := sqrt_rank_fits_outer_width (1/2) le_rfl m m w hm le_rfl hw
  have hwm : w ≤ m := hwidth.trans (half_width_le m hm)
  have hw2 : w ≤ 2*width (1/2) m := by omega
  have hfirst := hrow.adjoint w N w hwm hw2
  have hpsd := comparator_psd_cost_ambient kernels C E hC hE hK hm hwm
  have hlast : (kernelColumnWorkCap kernels N w w:ℝ) ≤ 8*χ*(N+m:ℕ)*(m:ℝ) := by
    apply comparator_nat_sup_real_le
    intro d
    apply hrow.forward N w d.val hwm
    exact (Nat.le_of_lt_succ d.isLt).trans hw2
  have hNmR : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hp : 0 ≤ χ*(m:ℝ) := by positivity
  unfold exactRangeWorkCap
  push_cast at hfirst hlast ⊢
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hNmR)]

theorem comparator_exact_output_cap
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ χOut Ck E : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (hout : FixedOutputKernelEnvelopes N kernels χOut) (hC : 0 < Ck) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ Ck*(D:ℝ)^E)
    (I : FixedProblem N m N r L) (S : StoredSketches N m N L) (C : MainSupportData S)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    (mainExactOutputWorkCap kernels I S C:ℝ) ≤
      96*χ*(N:ℝ)*(m:ℝ)+9*(Ck+1)*(m:ℝ)^E+(N:ℝ)^2*χOut := by
  have hprojection := comparator_projection_cap kernels χ χOut hχ hrow hout hm hNm hr
  apply comparator_nat_sup_real_le
  intro w
  have hw : (w.val:ℝ) ≤ Real.sqrt (m:ℝ) :=
    (by exact_mod_cast Nat.le_of_lt_succ w.isLt : (w.val:ℝ) ≤ r).trans hr
  have hwidth := sqrt_rank_fits_outer_width (1/2) le_rfl m m w.val hm le_rfl hw
  have hw2 : w.val ≤ 2*width (1/2) m := by omega
  have hfirst := hrow.forward N m w.val le_rfl hw2
  have hsecond := hrow.forward m C.pair.dimension w.val C.pair.dimension_le_fin hw2
  have hrange := comparator_exact_range_cap kernels χ Ck E hχ hrow hC hE hK hm hNm hw
  have hNmR : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hp : 0 ≤ χ*(m:ℝ) := by positivity
  push_cast at hfirst hsecond ⊢
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hNmR)]

end
end HierarchicalAbsoluteSpectral
