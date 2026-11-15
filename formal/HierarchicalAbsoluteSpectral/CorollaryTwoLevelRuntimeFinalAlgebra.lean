import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalCoreCap
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalLogs
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeAlgebra
import HierarchicalAbsoluteSpectral.BaseFixedOutputCost

/-! Thin-output product bounds and a single explicit small-core algebra
charge for the final two-level runtime envelope. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
variable {N m r w k L : ℕ}

theorem twoLevelRuntimeThinProjection_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (N m r : ℕ) :
    twoLevelFactorProjectionWorkCap K N m N r ≤ 2*matrixProductCost K N m (r+1) := by
  apply Finset.sup_le
  intro d _
  have hleft := (kernel_cost_le_matrixProductCost_cyclic K d.val N m).trans
    (matrixProductCost_mono K (A:=N) (B:=m) (C:=r+1) le_rfl le_rfl (by omega))
  have hright := kernel_cost_le_matrixProductCost K d.val m N (r+1) m N
    (by omega) le_rfl le_rfl
  have he : matrixProductCost K (r+1) m N = matrixProductCost K N m (r+1) := by
    rw [← matrixProductCost_rotate K m N (r+1),matrixProductCost_swap K m N (r+1)]
  rw [he] at hright
  omega

theorem twoLevelRuntimeExactRange_product_bound_nat
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (N m r w : ℕ)
    (hrm : r ≤ m) (hwr : w ≤ r) :
    exactRangeWorkCap K N w ≤ 2*matrixProductCost K N m (r+1)+psdGramCost K w := by
  have hfirst := (kernel_cost_le_matrixProductCost_cyclic K w N w).trans
    (matrixProductCost_mono K (A:=N) (B:=m) (C:=r+1) le_rfl
      (hwr.trans hrm) (by omega))
  have hlast := kernelColumnWorkCap_product_bound K N m r w (hwr.trans hrm) hwr
  unfold exactRangeWorkCap
  omega

theorem twoLevelRuntimeThinExact_product_bound_nat
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem N m N r L) (S : StoredSketches N m N L) (C : MainSupportData S)
    (hNm : m ≤ N) (hrm : r ≤ m) (B : ℕ)
    (hpsd : ∀ w ≤ r, psdGramCost K w ≤ B) :
    twoLevelFactorExactWorkCap K I S C ≤ 6*matrixProductCost K N m (r+1)+B := by
  have hprojection := twoLevelRuntimeThinProjection_product_bound K N m r
  apply Finset.sup_le
  intro d _
  have hd : d.val ≤ r := by omega
  have hfirst := kernel_cost_le_matrixProductCost K N m d.val N m (r+1)
    le_rfl le_rfl (by omega)
  have hsecond := kernel_cost_le_matrixProductCost K m C.pair.dimension d.val N m (r+1)
    hNm C.pair.dimension_le_fin (by omega)
  have hrange := twoLevelRuntimeExactRange_product_bound_nat K N m r d.val hrm hd
  have hsmall := hpsd d.val hd
  omega

theorem twoLevelRuntimePhysicalRange_product_bound_nat
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (N m r B : ℕ)
    (hrm : r ≤ m) (hpsd : psdGramCost K r ≤ B) :
    exactRangeWorkCap K N r ≤ 2*matrixProductCost K N m (r+1)+B := by
  exact (twoLevelRuntimeExactRange_product_bound_nat K N m r r hrm le_rfl).trans
    (Nat.add_le_add_left hpsd _)

theorem twoLevelRuntimeThinExact_product_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (Ck E : ℝ) (hC : 0 < Ck) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((K a b c).cost:ℝ) ≤ Ck*(D:ℝ)^E)
    (I : FixedProblem N m N r L) (S : StoredSketches N m N L) (C : MainSupportData S)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hrm : r ≤ m) :
    (twoLevelFactorExactWorkCap K I S C:ℝ) ≤
      6*(matrixProductCost K N m (r+1):ℝ)+9*(Ck+1)*(m:ℝ)^E := by
  have hprojection : (twoLevelFactorProjectionWorkCap K N m N r:ℝ) ≤
      2*(matrixProductCost K N m (r+1):ℝ) := by
    exact_mod_cast twoLevelRuntimeThinProjection_product_bound K N m r
  apply comparator_nat_sup_real_le
  intro d
  have hd : d.val ≤ r := by omega
  have hfirst := kernel_cost_le_matrixProductCost K N m d.val N m (r+1)
    le_rfl le_rfl (by omega)
  have hsecond := kernel_cost_le_matrixProductCost K m C.pair.dimension d.val N m (r+1)
    hNm C.pair.dimension_le_fin (by omega)
  have hrange := exactRangeWorkCap_product_bound K Ck E hC hE hK N m r d.val hrm hd
  have hfirstR : ((K N m d.val).cost:ℝ) ≤ matrixProductCost K N m (r+1) := by exact_mod_cast hfirst
  have hsecondR : ((K m C.pair.dimension d.val).cost:ℝ) ≤ matrixProductCost K N m (r+1) := by exact_mod_cast hsecond
  change (((K N m d.val).cost+(K m C.pair.dimension d.val).cost+
    exactRangeWorkCap K N d.val+twoLevelFactorProjectionWorkCap K N m N r:ℕ):ℝ) ≤ _
  push_cast
  dsimp only [fixedOutputCoreCost] at hrange
  linarith

/-- All small-core algebra charges, including Newton iteration, are rounded
into one integer envelope. The caller chooses `E = 9/4+1/100000`. -/
def twoLevelRuntimeCoreAlgebraCharge (C E : ℝ) (m : ℕ) : ℕ :=
  ⌈2000*(C+1)*(m:ℝ)^E*(1+Real.log (m:ℝ))⌉₊

theorem twoLevelRuntimeCoreAlgebraCharge_dominates (C E D : ℝ) (m : ℕ)
    (hC : 0 < C) (hm : 1 ≤ m) (hD : 0 ≤ D) (hDmax : D ≤ 2000) :
    D*(C+1)*(m:ℝ)^E ≤ (twoLevelRuntimeCoreAlgebraCharge C E m:ℝ) := by
  have hlog : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hCP : 0 ≤ (C+1)*(m:ℝ)^E := by positivity
  have hceil := Nat.le_ceil (2000*(C+1)*(m:ℝ)^E*(1+Real.log (m:ℝ)))
  change _ ≤ (twoLevelRuntimeCoreAlgebraCharge C E m:ℝ) at hceil
  have hmul := mul_le_mul_of_nonneg_right hDmax hCP
  nlinarith [mul_nonneg hCP hlog]

theorem twoLevelRuntimeCoreAlgebraCharge_positive (C E : ℝ) (m : ℕ)
    (hC : 0 < C) (hE : 0 ≤ E) (hm : 1 ≤ m) :
    1 ≤ twoLevelRuntimeCoreAlgebraCharge C E m := by
  have hpow : 1 ≤ (m:ℝ)^E := Real.one_le_rpow (by exact_mod_cast hm) hE
  have hdom := twoLevelRuntimeCoreAlgebraCharge_dominates C E 1 m hC hm (by norm_num) (by norm_num)
  have hh : (1:ℝ) ≤ (twoLevelRuntimeCoreAlgebraCharge C E m:ℝ) := by nlinarith
  exact_mod_cast hh

theorem twoLevelRuntimeBaseNewtonSteps_bound (m : ℕ) (h : ℝ) (hm : 2 ≤ m)
    (hh : 0 < h) (hhsmall : h ≤ 1/64) (hlog : Real.log (1/h) ≤ 3*Real.log (m:ℝ)) :
    ((baseNewtonSteps h hh+1:ℕ):ℝ) ≤ 16*Real.log (m:ℝ) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : (1/2:ℝ) ≤ Real.log (m:ℝ) :=
    family_log_two_lower.trans (Real.log_le_log (by norm_num : (0:ℝ) < 2) hmR)
  have hquot : 1/(4*h) ≤ 1/h :=
    div_le_div_of_nonneg_left (by norm_num) hh (by linarith)
  have hlog4 := Real.log_le_log (by positivity : 0 < 1/(4*h)) hquot
  have hsteps := baseNewtonSteps_bound h hh hhsmall
  push_cast
  linarith

theorem twoLevelRuntimeBaseAlgebraCharge_bound
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C E : ℝ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((K a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 2 ≤ m) (hk : k ≤ m) (h : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1/64)
    (hlog : Real.log (1/h) ≤ 3*Real.log (m:ℝ)) :
    baseConstructionCost K k h hh ≤ twoLevelRuntimeCoreAlgebraCharge C E m := by
  have hbase := comparator_base_cost_ambient K C E hC hE hK (by omega : 1 ≤ m) hk h hh
  have hsteps := twoLevelRuntimeBaseNewtonSteps_bound m h hm hh hhsmall hlog
  have hCP : 0 ≤ (C+1)*(m:ℝ)^E := by positivity
  have hlogm : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hmul := mul_le_mul_of_nonneg_right hsteps (show 0 ≤ 100*(C+1)*(m:ℝ)^E by positivity)
  have hceil := Nat.le_ceil (2000*(C+1)*(m:ℝ)^E*(1+Real.log (m:ℝ)))
  change _ ≤ (twoLevelRuntimeCoreAlgebraCharge C E m:ℝ) at hceil
  have hbound : (baseConstructionCost K k h hh:ℝ) ≤ (twoLevelRuntimeCoreAlgebraCharge C E m:ℝ) := by
    nlinarith [mul_nonneg hCP hlogm]
  exact_mod_cast hbound

theorem twoLevelRuntimeSmallAlgebraCharge_bounds
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C E : ℝ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((K a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 2 ≤ m) (hk : k ≤ m) (hr : r ≤ m) :
    kernelEnvelope K k ≤ twoLevelRuntimeCoreAlgebraCharge C E m ∧
      psdGramCost K r ≤ twoLevelRuntimeCoreAlgebraCharge C E m ∧
      k*k ≤ twoLevelRuntimeCoreAlgebraCharge C E m ∧
      k ≤ twoLevelRuntimeCoreAlgebraCharge C E m ∧
      ⌈212*(C+1)*(k:ℝ)^E⌉₊ ≤ twoLevelRuntimeCoreAlgebraCharge C E m ∧
      ∀ raw ≤ m, rangeDeflationWorkCap K k raw ≤ twoLevelRuntimeCoreAlgebraCharge C E m := by
  have hm1 : 1 ≤ m := by omega
  have henv := comparator_kernel_envelope_ambient K C E hC hK hm1 hk
  have hpsd := comparator_psd_cost_ambient K C E hC hE hK hm1 hr
  have hinertia := comparator_inertia_ceiling_ambient C E hC hE hm1 hk
  have h1 : (C+1)*(m:ℝ)^E ≤ (twoLevelRuntimeCoreAlgebraCharge C E m:ℝ) := by
    simpa only [one_mul] using
      twoLevelRuntimeCoreAlgebraCharge_dominates C E 1 m hC hm1 (by norm_num) (by norm_num)
  have h9 := twoLevelRuntimeCoreAlgebraCharge_dominates C E 9 m hC hm1 (by norm_num) (by norm_num)
  have h11 := twoLevelRuntimeCoreAlgebraCharge_dominates C E 11 m hC hm1 (by norm_num) (by norm_num)
  have h213 := twoLevelRuntimeCoreAlgebraCharge_dominates C E 213 m hC hm1 (by norm_num) (by norm_num)
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hkR : (k:ℝ) ≤ m := by exact_mod_cast hk
  have hpower : (m:ℝ)^2 ≤ (m:ℝ)^E := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hmR hE
  have hlinear : (m:ℝ) ≤ (m:ℝ)^E := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hmR (show (1:ℝ) ≤ E by linarith)
  have hP : 0 ≤ (m:ℝ)^E := by positivity
  have hbig : (m:ℝ)^E ≤ (C+1)*(m:ℝ)^E := by nlinarith
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast henv.trans (show C*(m:ℝ)^E ≤ (twoLevelRuntimeCoreAlgebraCharge C E m:ℝ) by nlinarith)
  · exact_mod_cast hpsd.trans h9
  · have hsq := mul_le_mul hkR hkR (Nat.cast_nonneg k) (Nat.cast_nonneg m)
    have hh : (k:ℝ)*k ≤ (twoLevelRuntimeCoreAlgebraCharge C E m:ℝ) := by nlinarith
    exact_mod_cast hh
  · exact_mod_cast hkR.trans (hlinear.trans (hbig.trans h1))
  · exact_mod_cast hinertia.trans h213
  · intro raw hraw
    have hh := comparator_range_algebra_ambient K C E hC hE hK hm1 hk hraw
    have hmin := Nat.min_le_left (algebraRangeWorkCap K k raw) (22*k*raw*raw)
    have hhR : (rangeDeflationWorkCap K k raw:ℝ) ≤ 11*(C+1)*(m:ℝ)^E :=
      (Nat.cast_le.mpr hmin).trans hh
    exact_mod_cast hhR.trans h11

theorem TwoLevelProblem.runtime_base_algebra_charge
    (I : TwoLevelProblem N m r)
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (C E : ℝ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((K a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ m) :
    baseConstructionCost K k (I.fixed.accuracy 0) (I.fixed.accuracy_positive 0 (by omega)) ≤
      twoLevelRuntimeCoreAlgebraCharge C E m := by
  apply twoLevelRuntimeBaseAlgebraCharge_bound K C E hC hE hK hm hk
    (I.fixed.accuracy 0) (I.fixed.accuracy_positive 0 (by omega)) I.fixed.initial_accuracy_le
  have hl := twoLevelRuntime_rounded_log_inverse (m:ℝ) 7 100
    (by exact_mod_cast hm) (by norm_num)
  have he : I.fixed.accuracy 0 = twoLevelH0 m := by
    simp only [TwoLevelProblem.fixed_accuracy,twoLevelAccuracy,ite_true]
  rw [he]
  change Real.log (1/twoLevelH0 m) ≤ _ at hl
  have hlog : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith

theorem twoLevelRuntimeThinOutputCoreCharge_bounds
    (K : ∀ a b c : ℕ, ArithmeticKernel a b c) (Ck E : ℝ) (hC : 0 < Ck) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((K a b c).cost:ℝ) ≤ Ck*(D:ℝ)^E)
    (I : FixedProblem N m N r L) (S : StoredSketches N m N L) (C : MainSupportData S)
    (hm : 2 ≤ m) (hNm : m ≤ N) (hrm : r ≤ m)
    (hT : (matrixProductCost K N m (r+1):ℝ) ≤ (m:ℝ)^E) :
    twoLevelFactorExactWorkCap K I S C ≤ twoLevelRuntimeCoreAlgebraCharge Ck E m ∧
      exactRangeWorkCap K N r ≤ twoLevelRuntimeCoreAlgebraCharge Ck E m ∧
      twoLevelFactorProjectionWorkCap K N m N r ≤ twoLevelRuntimeCoreAlgebraCharge Ck E m := by
  have hm1 : 1 ≤ m := by omega
  have he := twoLevelRuntimeThinExact_product_bound K Ck E hC hE hK I S C hm1 hNm hrm
  have hr := exactRangeWorkCap_product_bound K Ck E hC hE hK N m r r hrm le_rfl
  dsimp only [fixedOutputCoreCost] at hr
  have hp : (twoLevelFactorProjectionWorkCap K N m N r:ℝ) ≤
      2*(matrixProductCost K N m (r+1):ℝ) := by
    exact_mod_cast twoLevelRuntimeThinProjection_product_bound K N m r
  have hdom := twoLevelRuntimeCoreAlgebraCharge_dominates Ck E 15 m hC hm1 (by norm_num) (by norm_num)
  have hP : 0 ≤ (m:ℝ)^E := by positivity
  refine ⟨?_,?_,?_⟩
  · have hh : (twoLevelFactorExactWorkCap K I S C:ℝ) ≤
        (twoLevelRuntimeCoreAlgebraCharge Ck E m:ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : (exactRangeWorkCap K N r:ℝ) ≤ (twoLevelRuntimeCoreAlgebraCharge Ck E m:ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : (twoLevelFactorProjectionWorkCap K N m N r:ℝ) ≤
        (twoLevelRuntimeCoreAlgebraCharge Ck E m:ℝ) := by nlinarith
    exact_mod_cast hh

end
end HierarchicalAbsoluteSpectral
