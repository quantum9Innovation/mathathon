import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeConstants
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeDegrees
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeAlgebra
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeBudget

/-! Discharge the intermediate core envelope from the original rank bound,
actual constant schedule, and verified circuit family. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Matmul.RectangularPrograms
variable {N m r : ℕ}

theorem comparator_le_nat_ceil {v : ℕ} {X : ℝ} (hv : (v:ℝ) ≤ X) : v ≤ ⌈X⌉₊ := by
  exact_mod_cast hv.trans (Nat.le_ceil X)

def comparatorActionScale (I : FixedProblem N m N r 1) : ℝ :=
  comparatorFactorConstant+2048*(neumannCount I.massAccuracy I.final_budget.mass_positive:ℝ)+20

def comparatorCoreConstant : ℝ :=
  1000*(baseNewtonSteps (1/1024) (by norm_num)+1:ℕ)

def comparatorActionCharge (I : FixedProblem N m N r 1) (χ : ℝ) : ℕ :=
  ⌈comparatorActionScale I*χ*(N:ℝ)*(m:ℝ)⌉₊

def comparatorCoreCharge (C ζ : ℝ) (m : ℕ) : ℕ :=
  ⌈comparatorCoreConstant*(C+1)*(m:ℝ)^(9/4+ζ)⌉₊

def comparatorOutputCharge (χ χOut C ζ : ℝ) (N m : ℕ) : ℕ :=
  ⌈100*(χ*(N:ℝ)*(m:ℝ)+(C+1)*(m:ℝ)^(9/4+ζ)+(N:ℝ)^2*χOut)⌉₊

theorem comparator_actual_core_envelope
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (S : StoredSketches N m N 1) (C : MainSupportData S) (hm : 2 ≤ m)
    (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) :
    ComparatorCoreEnvelope kernels I S C Ck (9/4+ζ)
      (comparatorActionCharge I χ) (comparatorCoreCharge Ck ζ m)
      (comparatorOutputCharge χ χOut Ck ζ N m) (comparatorOuterDegreeCap I) := by
  let X : ℝ := χ*(N:ℝ)*(m:ℝ)
  let Y : ℝ := (Ck+1)*(m:ℝ)^(9/4+ζ)
  let Z : ℝ := (N:ℝ)^2*χOut
  have hm1 : 1 ≤ m := by omega
  have hNm : m ≤ N := I.core_le_rows
  have hE : (2:ℝ) ≤ 9/4+ζ := by linarith
  have hk : C.pair.dimension ≤ m := C.pair.dimension_le_fin
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hm1.trans hNm
  have hX : 1 ≤ X := by
    have hh : (1:ℝ) ≤ χ*(N:ℝ) := by nlinarith [mul_le_mul hχ hNr (by norm_num) (by positivity)]
    exact (by simpa only [one_mul] using mul_le_mul hh hmr (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ χ*(N:ℝ)))
  have hP1 : (1:ℝ) ≤ (m:ℝ)^(9/4+ζ) := Real.one_le_rpow hmr (by linarith)
  have hY : 1 ≤ Y := by
    have hp : 0 ≤ Ck*(m:ℝ)^(9/4+ζ) := by positivity
    dsimp [Y]
    nlinarith
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hCB : 1000 ≤ comparatorCoreConstant := by
    have hq : (0:ℝ) ≤ (baseNewtonSteps (1/1024) (by norm_num):ℝ) := by positivity
    unfold comparatorCoreConstant
    push_cast
    nlinarith
  have hDfactor : comparatorFactorConstant ≤ comparatorActionScale I := by
    unfold comparatorActionScale
    have hq : (0:ℝ) ≤ neumannCount I.massAccuracy I.final_budget.mass_positive := by positivity
    linarith
  have hDtrue : 2048*(neumannCount I.massAccuracy I.final_budget.mass_positive:ℝ) ≤ comparatorActionScale I := by
    unfold comparatorActionScale
    linarith [comparatorFactorConstant_ge_one]
  have hD20 : 20 ≤ comparatorActionScale I := by
    unfold comparatorActionScale
    have hq : (0:ℝ) ≤ neumannCount I.massAccuracy I.final_budget.mass_positive := by positivity
    linarith [comparatorFactorConstant_ge_one]
  have hA (t : ℝ) (ht : t ≤ comparatorActionScale I) :
      t*X ≤ (comparatorActionCharge I χ:ℝ) := by
    calc
      _ ≤ comparatorActionScale I*X := mul_le_mul_of_nonneg_right ht (by linarith)
      _ = comparatorActionScale I*χ*(N:ℝ)*(m:ℝ) := by dsimp [X]; ring
      _ ≤ _ := Nat.le_ceil _
  have hB (t : ℝ) (ht : t ≤ comparatorCoreConstant) :
      t*Y ≤ (comparatorCoreCharge Ck ζ m:ℝ) := by
    calc
      _ ≤ comparatorCoreConstant*Y := mul_le_mul_of_nonneg_right ht (by linarith)
      _ = comparatorCoreConstant*(Ck+1)*(m:ℝ)^(9/4+ζ) := by dsimp [Y]; ring
      _ ≤ _ := Nat.le_ceil _
  have hO : 96*X+9*Y+Z ≤ (comparatorOutputCharge χ χOut Ck ζ N m:ℝ) := by
    calc
      _ ≤ 100*(X+Y+Z) := by nlinarith
      _ = 100*(χ*(N:ℝ)*(m:ℝ)+(Ck+1)*(m:ℝ)^(9/4+ζ)+(N:ℝ)^2*χOut) := rfl
      _ ≤ _ := Nat.le_ceil _
  have hrR : (r:ℝ) ≤ Real.sqrt (m:ℝ) :=
    (by exact_mod_cast hr : (r:ℝ) ≤ ⌊Real.sqrt (m:ℝ)⌋₊).trans (Nat.floor_le (Real.sqrt_nonneg _))
  have hb0 : r+1 ≤ 2*width (1/2) m := by
    have hh := (family_rounded_rank_width m r hm1 hr).2
    simpa only [width,← Real.sqrt_eq_rpow] using hh
  have hforward (a b c : ℕ) (ha : a ≤ N) (hb : b ≤ m) (hc : c ≤ r+1) :
      ((kernels a b c).cost:ℝ) ≤ 16*X := by
    have hh := hEnv.row.forward a b c hb (hc.trans hb0)
    have haR : (a:ℝ) ≤ N := by exact_mod_cast ha
    have hmN : (m:ℝ) ≤ N := by exact_mod_cast hNm
    have hp : 0 ≤ χ*(m:ℝ) := by positivity
    dsimp [X]
    push_cast at hh
    nlinarith [mul_nonneg hp (sub_nonneg.mpr haR),mul_nonneg hp (sub_nonneg.mpr hmN)]
  have hblock : (C.pair.dimension:ℝ)*(r+1) ≤ 2*X := by
    have hb2 : r+1 ≤ 2*m := hb0.trans (Nat.mul_le_mul_left 2 (half_width_le m hm1))
    have h1 := mul_le_mul (by exact_mod_cast hk : (C.pair.dimension:ℝ) ≤ m)
      (by exact_mod_cast hb2 : (r+1:ℝ) ≤ 2*m) (by positivity) (Nat.cast_nonneg m)
    have h2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hNm : (m:ℝ) ≤ N) (Nat.cast_nonneg m)
    have h3 := mul_le_mul_of_nonneg_right hχ (show 0 ≤ (N:ℝ)*(m:ℝ) by positivity)
    dsimp [X]
    nlinarith
  have hYP : (m:ℝ)^(9/4+ζ) ≤ Y := by
    have hh : 0 ≤ Ck*(m:ℝ)^(9/4+ζ) := by positivity
    dsimp [Y]
    nlinarith
  have hYB : Y ≤ (comparatorCoreCharge Ck ζ m:ℝ) := by simpa only [one_mul] using hB 1 (by linarith)
  constructor
  · have hh := (show (1:ℝ) ≤ X by exact hX).trans
      (by simpa only [one_mul] using hA 1 (by linarith))
    exact_mod_cast hh
  · exact_mod_cast hY.trans hYB
  · have hh : (1:ℝ) ≤ (comparatorOutputCharge χ χOut Ck ζ N m:ℝ) := by linarith
    exact_mod_cast hh
  · intro b hb
    have hh := comparator_factor_action_cost (b:=b) kernels χ hχ hEnv.row I haccuracy S C hm1 hNm (hb.trans hb0)
    have hle := hA comparatorFactorConstant hDfactor
    dsimp [X] at hle
    exact_mod_cast hh.trans (by convert hle using 1 <;> ring)
  · intro b hb
    have hh := comparator_stored_pencil_cost (b:=b) kernels χ hχ hEnv.row I.A I.Bᵀ
      C.pair.factor C.pair.leftInverseᵀ 0 I.massAccuracy I.final_budget.mass_positive
      hm1 hNm le_rfl le_rfl hk (hb.trans hb0)
    have hle := hA (2048*(neumannCount I.massAccuracy I.final_budget.mass_positive:ℝ)) hDtrue
    change (mainTrueActionCost kernels I S C b:ℝ) ≤ _ at hh
    dsimp [X] at hle
    exact_mod_cast hh.trans (by convert hle using 1 <;> ring)
  · intro b hb
    exact_mod_cast (hforward _ _ _ (hk.trans hNm) hk hb).trans (hA 16 (by linarith))
  · exact_mod_cast hblock.trans (hA 2 (by linarith))
  · have hh := comparator_base_cost_ambient kernels Ck (9/4+ζ) hC hE hEnv.core hm1 hk
      (1/1024) (by norm_num)
    have hcoeff : 100*(baseNewtonSteps (1/1024) (by norm_num)+1:ℕ) ≤ comparatorCoreConstant := by
      unfold comparatorCoreConstant
      push_cast
      have hq : (0:ℝ) ≤ baseNewtonSteps (1/1024) (by norm_num) := by positivity
      nlinarith
    have hle := hB (100*(baseNewtonSteps (1/1024) (by norm_num)+1:ℕ)) hcoeff
    dsimp [Y] at hle
    have hh' := hh.trans (by convert hle using 1 <;> ring)
    simpa only [haccuracy,comparatorAccuracy_zero] using (show baseConstructionCost kernels C.pair.dimension (1/1024) (by norm_num) ≤ comparatorCoreCharge Ck ζ m by exact_mod_cast hh')
  · have hh := comparator_kernel_envelope_ambient kernels Ck (9/4+ζ) hC hEnv.core hm1 hk
    have hCY : Ck*(m:ℝ)^(9/4+ζ) ≤ Y := by
      dsimp [Y]
      nlinarith [show 0 ≤ (m:ℝ)^(9/4+ζ) by positivity]
    exact_mod_cast hh.trans (hCY.trans hYB)
  · exact_mod_cast (comparator_psd_cost_ambient kernels Ck (9/4+ζ) hC hE hEnv.core hm1 I.rank_le_core).trans
      (by simpa only [Y] using hB 9 (by linarith))
  · have hh := mul_le_mul (by exact_mod_cast hk : (C.pair.dimension:ℝ) ≤ m)
      (by exact_mod_cast hk : (C.pair.dimension:ℝ) ≤ m) (by positivity) (Nat.cast_nonneg m)
    have hp : (m:ℝ)*(m:ℝ) ≤ (m:ℝ)^(9/4+ζ) := by
      simpa only [Real.rpow_two,pow_two] using Real.rpow_le_rpow_of_exponent_le hmr hE
    exact_mod_cast (hh.trans (hp.trans (hYP.trans hYB)))
  · have hp : (m:ℝ) ≤ (m:ℝ)^(9/4+ζ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hmr (show (1:ℝ) ≤ 9/4+ζ by linarith)
    exact_mod_cast (show (C.pair.dimension:ℝ) ≤ m by exact_mod_cast hk).trans (hp.trans (hYP.trans hYB))
  · have hh := comparator_exact_output_cap kernels χ χOut Ck (9/4+ζ) hχ hEnv.row hEnv.output hC hE hEnv.core I S C hm1 hNm hrR
    exact_mod_cast hh.trans (by simpa only [X,Y,Z] using hO)
  · have hh := comparator_exact_range_cap kernels χ Ck (9/4+ζ) hχ hEnv.row hC hE hEnv.core hm1 hNm hrR
    have hle : 32*X+9*Y ≤ (comparatorOutputCharge χ χOut Ck ζ N m:ℝ) := by nlinarith
    exact_mod_cast hh.trans (by simpa only [X,Y] using hle)
  · have hh := comparator_projection_cap kernels χ χOut hχ hEnv.row hEnv.output hm1 hNm hrR
    have hle : 32*X+Z ≤ (comparatorOutputCharge χ χOut Ck ζ N m:ℝ) := by nlinarith
    exact_mod_cast hh.trans (by simpa only [X,Z] using hle)
  · exact_mod_cast (hforward N m r le_rfl le_rfl (by omega)).trans (hA 16 (by linarith))
  · exact_mod_cast (hforward m C.pair.dimension r hNm hk (by omega)).trans (hA 16 (by linarith))
  · intro hrc
    exact mainQueryDegree_comparator_cap I S C hm hrc
  · intro hrc
    have hq := mainQueryDegree_comparator_cap I S C hm hrc
    have hw : (mainQueryDegree I S C hrc+1)*(r+1) ≤ m :=
      (Nat.mul_le_mul_right (r+1) (Nat.succ_le_succ hq)).trans hraw
    have hh := comparator_range_algebra_ambient kernels Ck (9/4+ζ) hC hE hEnv.core hm1 hk hw
    change (mainQueryRangeCap kernels I S C hrc:ℝ) ≤ _ at hh
    exact_mod_cast hh.trans (by simpa only [Y] using hB 11 (by linarith))
  · have hh := comparator_inertia_ceiling_ambient Ck (9/4+ζ) hC hE hm1 hk
    exact_mod_cast hh.trans (by simpa only [Y] using hB 213 (by linarith))
  · intro hkc
    exact mainStrongDegree_comparator_cap I S C hm hkc

end
end HierarchicalAbsoluteSpectral
