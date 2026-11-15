import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeFinite
import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeDimension
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalNumeric

/-! Polynomial-log unfolding of the actual constant-schedule core cap.
The leading dimension term is N^2 (N/m)^(1/4), exactly the ordinary
comparator exponent in the optimized example. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {N m r : ℕ}

def comparatorQueryCoefficient (D : ℝ) : ℝ := 20000*D*comparatorAlphaRootConstant+3
def comparatorActionCoefficient (D : ℝ) : ℝ := (comparatorFactorConstant+20480020)*D
def comparatorOuterNumericCoefficient (D : ℝ) : ℝ := 1000*(10000*D+1)*(30000*D+1)
def comparatorCoreNumericCoefficient (D : ℝ) : ℝ :=
  comparatorOuterNumericCoefficient D*(2*comparatorQueryCoefficient D*comparatorActionCoefficient D+202)
def comparatorSmallNumericCoefficient (D : ℝ) : ℝ :=
  comparatorOuterNumericCoefficient D*(comparatorCoreConstant+102)

theorem comparator_query_dimension_bound (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy)
    (htheta : I.theta=min (comparatorDimensionTheta m N) (1/1048576))
    (D ell : ℝ) (hD : 1 ≤ D) (hell : 1 ≤ ell) (hellEq : ell=Real.log (m:ℝ))
    (hMagnitude : comparatorScalarMagnitude I ≤ D*ell) :
    (comparatorOuterDegreeCap I:ℝ)+1 ≤
      (comparatorQueryCoefficient D*(N/m:ℝ)^(1/4:ℝ))*(N/m:ℝ)*ell^5 := by
  let M := comparatorScalarMagnitude I
  let R : ℝ := N/m
  have hm : 1 ≤ m := I.rank_positive.trans I.rank_le_core
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hR : 1 ≤ R := (one_le_div hm0).mpr (by exact_mod_cast I.core_le_rows)
  have hRp : 0 < R := by linarith
  have hM : 1000 ≤ M := (comparatorScalarMagnitude_bounds I).1
  have hroot := Real.sqrt_pos.mpr I.alpha_positive
  have hInv := comparator_inverse_alpha_dimension_bound I haccuracy htheta
  have hC : 1 ≤ comparatorAlphaRootConstant := comparatorAlphaRootConstant_ge_one
  have hceil : (comparatorOuterDegreeCap I:ℝ) ≤ 10000*M*(1+ell)/Real.sqrt I.alpha+2 := by
    unfold comparatorOuterDegreeCap
    rw [← hellEq]
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ 10000*M*(1+ell)/Real.sqrt I.alpha+1 by positivity)).le
    dsimp [M] at hh ⊢
    linarith
  have hfirst : M*(1+ell) ≤ 2*D*ell^2 := by
    have hh := mul_le_mul hMagnitude (show 1+ell ≤ 2*ell by linarith)
      (by positivity : 0 ≤ 1+ell) (by positivity : 0 ≤ D*ell)
    dsimp [M]
    nlinarith
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0:ℝ) ≤ 10000)) hInv
    (by positivity : 0 ≤ 1/Real.sqrt I.alpha) (by positivity : 0 ≤ 10000*(2*D*ell^2))
  have hmain : 10000*M*(1+ell)/Real.sqrt I.alpha ≤
      20000*D*comparatorAlphaRootConstant*R^(5/4:ℝ)*ell^2 := by
    calc
      _ = (10000*(M*(1+ell)))*(1/Real.sqrt I.alpha) := by ring
      _ ≤ (10000*(2*D*ell^2))*(comparatorAlphaRootConstant*(N/m:ℝ)^(5/4:ℝ)) := hprod
      _ = _ := by dsimp [R]; ring
  have hlarge : 1 ≤ R^(5/4:ℝ)*ell^2 :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hR (by norm_num)) (one_le_pow₀ hell)
  have hQ : (comparatorOuterDegreeCap I:ℝ)+1 ≤ comparatorQueryCoefficient D*R^(5/4:ℝ)*ell^2 := by
    unfold comparatorQueryCoefficient
    nlinarith only [hceil,hmain,hlarge]
  have hpow : ell^2 ≤ ell^5 := pow_le_pow_right₀ hell (by norm_num)
  have hcoef : 0 ≤ comparatorQueryCoefficient D*R^(5/4:ℝ) := by
    unfold comparatorQueryCoefficient
    positivity
  calc
    _ ≤ comparatorQueryCoefficient D*R^(5/4:ℝ)*ell^2 := hQ
    _ ≤ comparatorQueryCoefficient D*R^(5/4:ℝ)*ell^5 := mul_le_mul_of_nonneg_left hpow hcoef
    _ = _ := by
      have he : (5/4:ℝ)=1+1/4 := by norm_num
      rw [he,Real.rpow_add hRp,Real.rpow_one]
      dsimp [R]
      ring

theorem comparator_action_dimension_bound (I : FixedProblem N m N r 1)
    (haccuracy : I.accuracy=comparatorAccuracy) (χ D ell : ℝ)
    (hχ : 1 ≤ χ) (hD : 1 ≤ D) (hell : 1 ≤ ell)
    (hMagnitude : comparatorScalarMagnitude I ≤ D*ell) :
    comparatorActionScale I*χ*(N:ℝ)*(m:ℝ) ≤
      comparatorActionCoefficient D*χ*(N:ℝ)*(m:ℝ)*ell^5 := by
  have hM := (comparatorScalarMagnitude_bounds I).1
  have hT := comparator_neumann_count_bound I haccuracy
  have hF := comparatorFactorConstant_ge_one
  have hscale : comparatorActionScale I ≤
      (comparatorFactorConstant+20480020)*comparatorScalarMagnitude I := by
    unfold comparatorActionScale
    have hh := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ comparatorScalarMagnitude I by linarith)
      (show 0 ≤ comparatorFactorConstant+20 by linarith)
    nlinarith
  have hbound := hscale.trans (mul_le_mul_of_nonneg_left hMagnitude (show 0 ≤ comparatorFactorConstant+20480020 by linarith))
  have hsize := mul_le_mul_of_nonneg_right hbound (show 0 ≤ χ*(N:ℝ)*(m:ℝ) by positivity)
  have hpow : ell ≤ ell^5 := le_self_pow₀ hell (by norm_num)
  have hlast := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ comparatorActionCoefficient D*χ*(N:ℝ)*(m:ℝ) by unfold comparatorActionCoefficient; positivity)
  calc
    _ ≤ comparatorActionCoefficient D*χ*(N:ℝ)*(m:ℝ)*ell := by
      calc
        _ = comparatorActionScale I*(χ*(N:ℝ)*(m:ℝ)) := by ring
        _ ≤ ((comparatorFactorConstant+20480020)*(D*ell))*(χ*(N:ℝ)*(m:ℝ)) := hsize
        _ = _ := by unfold comparatorActionCoefficient; ring
    _ ≤ _ := hlast

theorem comparator_actual_core_numeric
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck X D ell : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hD : 1 ≤ D) (hell : 1 ≤ ell)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (htheta : I.theta=min (comparatorDimensionTheta m N) (1/1048576))
    (S : StoredSketches N m N 1) (C : MainSupportData S) (hm : 2 ≤ m)
    (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊) (hellEq : ell=Real.log (m:ℝ))
    (hMagnitude : comparatorScalarMagnitude I ≤ D*ell)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) :
    (mainCoreWorkCap kernels I S C Ck (9/4+ζ):ℝ) ≤
      comparatorCoreNumericCoefficient D*X*(N:ℝ)^2*(N/m:ℝ)^(1/4:ℝ)*ell^12+
        comparatorSmallNumericCoefficient D*(Ck+1)*(m:ℝ)^(9/4+ζ)*ell^2 := by
  let A : ℝ := comparatorActionScale I*χ*(N:ℝ)*(m:ℝ)
  let CQ : ℝ := comparatorQueryCoefficient D*(N/m:ℝ)^(1/4:ℝ)
  let CA : ℝ := comparatorActionCoefficient D
  have hM := (comparatorScalarMagnitude_bounds I).1
  have hF := comparatorFactorConstant_ge_one
  have hCα := comparatorAlphaRootConstant_ge_one
  have hA1 : 1 ≤ A := by
    have hscale : 1 ≤ comparatorActionScale I := by
      have hT0 : (0:ℝ) ≤ neumannCount I.massAccuracy I.final_budget.mass_positive := by positivity
      unfold comparatorActionScale
      linarith
    have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hNR : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from (show 1 ≤ m by omega).trans I.core_le_rows)
    have hX1 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hχ hNR) hmR
    have hh := one_le_mul_of_one_le_of_one_le hscale hX1
    dsimp [A]
    nlinarith
  have henv := comparator_actual_core_envelope kernels ζ χ χOut Ck hζ hχ hχOut hC hEnv
    I haccuracy S C hm hr hraw
  have henv' : ComparatorCoreEnvelope kernels I S C Ck (9/4+ζ) ⌈A⌉₊
      (familyFinalCoreCharge Ck ζ m) (familyFinalOutputCharge χ χOut Ck ζ N m) (comparatorOuterDegreeCap I) := by
    simpa only [A,comparatorActionCharge,comparatorCoreCharge,comparatorCoreConstant,
      comparatorOutputCharge,familyFinalCoreCharge,familyFinalCoreConstant,familyFinalOutputCharge] using henv
  have hT : (I.queryCap:ℝ) ≤ (10000*D)*ell :=
    (comparator_query_cap_bound I haccuracy).trans (by nlinarith only [hMagnitude])
  have hR : (I.repetitions:ℝ) ≤ (30000*D)*ell :=
    (comparator_repetitions_bound I haccuracy).trans (by nlinarith only [hMagnitude])
  have hQ := comparator_query_dimension_bound I haccuracy htheta D ell hD hell hellEq hMagnitude
  have hAction := comparator_action_dimension_bound I haccuracy χ D ell hχ hD hell hMagnitude
  have hCA : 0 ≤ CA := by dsimp [CA,comparatorActionCoefficient]; positivity
  have hCQ : 0 ≤ CQ := by dsimp [CQ,comparatorQueryCoefficient]; positivity
  have hh := family_final_core_numeric kernels I S C Ck ζ χ χOut X A 1 ell CA CQ
    (10000*D) (30000*D) (comparatorOuterDegreeCap I)
    hC hζ hχ hχOut hχX hχOutX hA1 le_rfl hell hCA hCQ (by positivity) (by positivity)
    (by omega) hT hR hQ (by simpa only [one_mul,mul_one] using hAction) henv'
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 1 ≤ m by omega)
  have hratio : 1 ≤ (N/m:ℝ) := (one_le_div hm0).mpr (by exact_mod_cast I.core_le_rows)
  have hpow : 1 ≤ (N/m:ℝ)^(1/4:ℝ) := Real.one_le_rpow hratio (by norm_num)
  have hco : 2*CQ*CA+202 ≤
      (2*comparatorQueryCoefficient D*comparatorActionCoefficient D+202)*(N/m:ℝ)^(1/4:ℝ) := by
    dsimp [CQ,CA]
    nlinarith only [hpow]
  have hX0 : 0 ≤ X := by linarith
  have hmain := mul_le_mul_of_nonneg_right hco
    (show 0 ≤ comparatorOuterNumericCoefficient D*X*(N:ℝ)^2*ell^12 by
      unfold comparatorOuterNumericCoefficient; positivity)
  apply hh.trans
  dsimp [CQ,CA,comparatorCoreNumericCoefficient,comparatorSmallNumericCoefficient,
    comparatorOuterNumericCoefficient] at hmain ⊢
  simp only [one_mul,mul_one]
  have hCE : familyFinalCoreConstant=comparatorCoreConstant := rfl
  rw [hCE]
  nlinarith only [hmain]

end
end HierarchicalAbsoluteSpectral
