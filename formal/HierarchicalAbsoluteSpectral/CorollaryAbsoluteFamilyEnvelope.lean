import HierarchicalAbsoluteSpectral.CorollaryAbsoluteEnvelope
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalCore

/-! Actual verified family kernels and scalar degree/action bounds give
one envelope for all attempted widths, including the zero-width query. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Matmul.RectangularPrograms
variable {N m r L : ℕ}

theorem absolute_family_attempt_envelope
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck M : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck) (hM : 1 ≤ M)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r L) (hzero : I.accuracy 0=1/1024)
    (S : StoredSketches N m N L) (C : MainSupportData S) (hm : 2 ≤ m)
    (R : ℕ) (hr : R ≤ ⌊Real.sqrt (m:ℝ)⌋₊) (Q : ℕ)
    (hraw : (Q+1)*(R+1) ≤ m)
    (hactions : ∀ b ≤ R+1,
      (mainFactorActionCost kernels I S C b L:ℝ) ≤ M ∧
      (mainTrueActionCost kernels I S C b:ℝ) ≤ M ∧
      ((kernels C.pair.dimension C.pair.dimension b).cost:ℝ) ≤ M ∧
      (C.pair.dimension:ℝ)*b ≤ M ∧ ((kernels N m b).cost:ℝ) ≤ M ∧
      ((kernels m C.pair.dimension b).cost:ℝ) ≤ M)
    (hquery : ∀ s ≤ R, ∀ hs : s < C.pair.dimension, absoluteQueryDegree I S C hs ≤ Q)
    (hstrong : ∀ hk : 1 ≤ C.pair.dimension, absoluteStrongDegree I S C hk ≤ Q) :
    AbsoluteAttemptEnvelope kernels I S C Ck (9/4+ζ) R
      ⌈M⌉₊ (familyFinalCoreCharge Ck ζ m) (familyFinalOutputCharge χ χOut Ck ζ N m) Q := by
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
  have hCB : 1000 ≤ familyFinalCoreConstant := by
    have hq : (0:ℝ) ≤ (baseNewtonSteps (1/1024) (by norm_num):ℝ) := by positivity
    unfold familyFinalCoreConstant
    push_cast
    nlinarith
  have hB (t : ℝ) (ht : t ≤ familyFinalCoreConstant) :
      t*Y ≤ (familyFinalCoreCharge Ck ζ m:ℝ) := by
    calc
      _ ≤ familyFinalCoreConstant*Y := mul_le_mul_of_nonneg_right ht (by linarith)
      _ = familyFinalCoreConstant*(Ck+1)*(m:ℝ)^(9/4+ζ) := by dsimp [Y]; ring
      _ ≤ _ := Nat.le_ceil _
  have hO : 96*X+9*Y+Z ≤ (familyFinalOutputCharge χ χOut Ck ζ N m:ℝ) := by
    calc
      _ ≤ 100*(X+Y+Z) := by nlinarith
      _ = 100*(χ*(N:ℝ)*(m:ℝ)+(Ck+1)*(m:ℝ)^(9/4+ζ)+(N:ℝ)^2*χOut) := rfl
      _ ≤ _ := Nat.le_ceil _
  have hrR : (R:ℝ) ≤ Real.sqrt (m:ℝ) :=
    (by exact_mod_cast hr : (R:ℝ) ≤ ⌊Real.sqrt (m:ℝ)⌋₊).trans (Nat.floor_le (Real.sqrt_nonneg _))
  have hYP : (m:ℝ)^(9/4+ζ) ≤ Y := by
    have hh : 0 ≤ Ck*(m:ℝ)^(9/4+ζ) := by positivity
    dsimp [Y]
    nlinarith
  have hYB : Y ≤ (familyFinalCoreCharge Ck ζ m:ℝ) := by simpa only [one_mul] using hB 1 (by linarith)
  have hceil : M ≤ (⌈M⌉₊:ℝ) := Nat.le_ceil M
  constructor
  · exact_mod_cast hM.trans hceil
  · exact_mod_cast hY.trans hYB
  · have hh : (1:ℝ) ≤ (familyFinalOutputCharge χ χOut Ck ζ N m:ℝ) := by linarith
    exact_mod_cast hh
  · intro b hb
    exact family_final_nat_le_of_real ((hactions b hb).1.trans hceil)
  · intro b hb
    exact family_final_nat_le_of_real ((hactions b hb).2.1.trans hceil)
  · intro b hb
    exact family_final_nat_le_of_real ((hactions b hb).2.2.1.trans hceil)
  · apply family_final_nat_le_of_real
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
      (hactions (R+1) le_rfl).2.2.2.1.trans hceil
  · have hh := comparator_base_cost_ambient kernels Ck (9/4+ζ) hC hE hEnv.core hm1 hk
      (1/1024) (by norm_num)
    have hcoeff : 100*(baseNewtonSteps (1/1024) (by norm_num)+1:ℕ) ≤ familyFinalCoreConstant := by
      unfold familyFinalCoreConstant
      push_cast
      have hq : (0:ℝ) ≤ baseNewtonSteps (1/1024) (by norm_num) := by positivity
      nlinarith
    have hle := hB (100*(baseNewtonSteps (1/1024) (by norm_num)+1:ℕ)) hcoeff
    dsimp [Y] at hle
    have hh' : (baseConstructionCost kernels C.pair.dimension (1/1024) (by norm_num):ℝ) ≤
        (familyFinalCoreCharge Ck ζ m:ℝ) := hh.trans (by simpa only [mul_assoc] using hle)
    simpa only [hzero] using (show baseConstructionCost kernels C.pair.dimension (1/1024) (by norm_num) ≤ familyFinalCoreCharge Ck ζ m by exact_mod_cast hh')
  · have hh := comparator_kernel_envelope_ambient kernels Ck (9/4+ζ) hC hEnv.core hm1 hk
    have hCY : Ck*(m:ℝ)^(9/4+ζ) ≤ Y := by
      dsimp [Y]
      nlinarith [show 0 ≤ (m:ℝ)^(9/4+ζ) by positivity]
    exact_mod_cast hh.trans (hCY.trans hYB)
  · have hh := mul_le_mul (by exact_mod_cast hk : (C.pair.dimension:ℝ) ≤ m)
      (by exact_mod_cast hk : (C.pair.dimension:ℝ) ≤ m) (by positivity) (Nat.cast_nonneg m)
    have hp : (m:ℝ)*(m:ℝ) ≤ (m:ℝ)^(9/4+ζ) := by
      simpa only [Real.rpow_two,pow_two] using Real.rpow_le_rpow_of_exponent_le hmr hE
    exact_mod_cast (hh.trans (hp.trans (hYP.trans hYB)))
  · intro s hs
    have hsR : (s:ℝ) ≤ Real.sqrt (m:ℝ) :=
      (show (s:ℝ) ≤ R by exact_mod_cast hs).trans hrR
    have hh := comparator_exact_range_cap kernels χ Ck (9/4+ζ) hχ hEnv.row hC hE hEnv.core hm1 hNm hsR
    have hle : 32*X+9*Y ≤ (familyFinalOutputCharge χ χOut Ck ζ N m:ℝ) := by nlinarith
    apply family_final_nat_le_of_real
    exact hh.trans (by simpa only [X,Y,mul_assoc] using hle)
  · intro s hs
    have hsR : (s:ℝ) ≤ Real.sqrt (m:ℝ) :=
      (show (s:ℝ) ≤ R by exact_mod_cast hs).trans hrR
    have hh := comparator_projection_cap kernels χ χOut hχ hEnv.row hEnv.output hm1 hNm hsR
    have hle : 32*X+Z ≤ (familyFinalOutputCharge χ χOut Ck ζ N m:ℝ) := by nlinarith
    apply family_final_nat_le_of_real
    exact hh.trans (by simpa only [X,Z,mul_assoc] using hle)
  · intro s hs
    exact family_final_nat_le_of_real ((hactions s (by omega)).2.2.2.2.1.trans hceil)
  · intro s hs
    exact family_final_nat_le_of_real ((hactions s (by omega)).2.2.2.2.2.trans hceil)
  · intro s hs hrc
    exact hquery s hs hrc
  · intro s hs hrc
    have hq := hquery s hs hrc
    have hw : (absoluteQueryDegree I S C hrc+1)*(s+1) ≤ m :=
      (Nat.mul_le_mul (Nat.succ_le_succ hq) (Nat.succ_le_succ hs)).trans hraw
    have hh := comparator_range_algebra_ambient kernels Ck (9/4+ζ) hC hE hEnv.core hm1 hk hw
    change (absoluteQueryRangeCap kernels I S C hrc:ℝ) ≤ _ at hh
    apply family_final_nat_le_of_real
    exact hh.trans (by simpa only [Y,mul_assoc] using hB 11 (by linarith))
  · have hh := comparator_inertia_ceiling_ambient Ck (9/4+ζ) hC hE hm1 hk
    apply family_final_nat_le_of_real
    exact hh.trans (by simpa only [Y,mul_assoc] using hB 213 (by linarith))
  · intro hkc
    exact hstrong hkc

end
end HierarchicalAbsoluteSpectral
