import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeTotalNumeric

/-! The complete costs below refer to the two executed comparator programs,
including their five dimensional-accuracy preparation operations. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {N m r : ℕ}

theorem comparator_rest_coefficient_nonneg (D c : ℝ) (hc : 0 ≤ c) :
    0 ≤ comparatorRestNumericCoefficient D c := by
  have hlog := family_log_two_lower
  unfold comparatorRestNumericCoefficient twoLevelSketchLogCoefficient
  positivity

theorem comparator_total_numeric_of_body
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck X D c ell : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hD : 1 ≤ D) (hc : 0 ≤ c) (hell : 1 ≤ ell)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (htheta : I.theta=min (comparatorDimensionTheta m N) (1/1048576))
    (S : StoredSketches N m N 1) (C : MainSupportData S) (hm : 2 ≤ m)
    (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊) (hellEq : ell=Real.log (m:ℝ))
    (hMagnitude : comparatorScalarMagnitude I ≤ D*ell)
    (hconfidence : Real.log (1/I.delta) ≤ c*ell) (hside : Real.log (N:ℝ) ≤ 3*ell)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) (body : ℕ)
    (hbody : body ≤ 4+3*I.queryCap+2*I.repetitions+29+
      4*sketchFormationCap N m I.sketchFailure+2*comparatorGramRowWorkCap kernels m N+
        psdGramCost kernels m+2*kernelEnvelope kernels m+mainCoreWorkCap kernels I S C Ck (9/4+ζ)) :
    ((2*m*(N+N)+N*N+mainRandomizedWork I (5+body):ℕ):ℝ) ≤
      2*(comparatorGramRowWorkCap kernels m N:ℝ)+
        comparatorTotalMainCoefficient D c*X*(N:ℝ)^2*(N/m:ℝ)^(1/4:ℝ)*ell^12+
        comparatorTotalSmallCoefficient D*(Ck+1)*(m:ℝ)^(9/4+ζ)*ell^2 := by
  have ht := comparator_total_of_body kernels I body
    (mainCoreWorkCap kernels I S C Ck (9/4+ζ)) hbody
  have htr : ((2*m*(N+N)+N*N+mainRandomizedWork I (5+body):ℕ):ℝ) ≤
      (comparatorNumericRestCap kernels I:ℝ)+(mainCoreWorkCap kernels I S C Ck (9/4+ζ):ℝ) := by
    exact_mod_cast ht
  have hrest := comparator_numeric_rest_bound kernels ζ χ χOut Ck D c ell hζ hC hD hc hell
    hEnv I haccuracy hm hellEq hMagnitude hconfidence hside
  have hcore := comparator_actual_core_numeric kernels ζ χ χOut Ck X D ell
    hζ hχ hχOut hC hχX hχOutX hD hell hEnv I haccuracy htheta S C hm hr hellEq hMagnitude hraw
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hratio : 1 ≤ (N/m:ℝ)^(1/4:ℝ) := Real.one_le_rpow
    ((one_le_div hm0).mpr (by exact_mod_cast I.core_le_rows)) (by norm_num)
  have hX1 : 1 ≤ X := hχ.trans hχX
  have hscale : 1 ≤ X*(N/m:ℝ)^(1/4:ℝ) := one_le_mul_of_one_le_of_one_le hX1 hratio
  have hp : ell^2 ≤ ell^12 := pow_le_pow_right₀ hell (by norm_num)
  have hmain : (N:ℝ)^2*ell^2 ≤ X*(N:ℝ)^2*(N/m:ℝ)^(1/4:ℝ)*ell^12 := by
    have h1 := mul_le_mul_of_nonneg_left hp (sq_nonneg (N:ℝ))
    have h2 := mul_le_mul_of_nonneg_right hscale (show 0 ≤ (N:ℝ)^2*ell^12 by positivity)
    nlinarith only [h1,h2]
  have hrestScale := mul_le_mul_of_nonneg_left hmain (comparator_rest_coefficient_nonneg D c hc)
  have hsmall := mul_le_mul_of_nonneg_left (one_le_pow₀ hell (n:=2))
    (show 0 ≤ 11*(Ck+1)*(m:ℝ)^(9/4+ζ) by positivity)
  unfold comparatorTotalMainCoefficient comparatorTotalSmallCoefficient
  nlinarith only [htr,hrest,hcore,hrestScale,hsmall]

theorem constantDistortionComparatorProgram_complete_numeric
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck X D c ell : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hD : 1 ≤ D) (hc : 0 ≤ c) (hell : 1 ≤ ell)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (htheta : I.theta=min (comparatorDimensionTheta m N) (1/1048576))
    (hm : 2 ≤ m) (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊) (hellEq : ell=Real.log (m:ℝ))
    (hMagnitude : comparatorScalarMagnitude I ≤ D*ell)
    (hconfidence : Real.log (1/I.delta) ≤ c*ell) (hside : Real.log (N:ℝ) ≤ 3*ell)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) (g : MainRandomTape I) :
    ((2*m*(N+N)+N*N+mainRandomizedWork I (5+(constantDistortionComparatorProgram kernels I g).work):ℕ):ℝ) ≤
      2*(comparatorGramRowWorkCap kernels m N:ℝ)+
        comparatorTotalMainCoefficient D c*X*(N:ℝ)^2*(N/m:ℝ)^(1/4:ℝ)*ell^12+
        comparatorTotalSmallCoefficient D*(Ck+1)*(m:ℝ)^(9/4+ζ)*ell^2 := by
  let S := (mainSketchProgram I g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  apply comparator_total_numeric_of_body kernels ζ χ χOut Ck X D c ell hζ hχ hχOut hC
    hχX hχOutX hD hc hell hEnv I haccuracy htheta S C hm hr hellEq hMagnitude hconfidence hside hraw
  have hs := mainSketchProgram_work_le I g
  have hs' : (mainSketchProgram I g).work ≤ 4*sketchFormationCap N m I.sketchFailure := by nlinarith
  have hcS := comparator_support_uniform_work kernels S.initialA S.initialB (by omega : 1 ≤ m)
    (S.rowsA 0) (S.rowsB 0)
  have hcore := mainCoreProgram_work_bound kernels Ck (9/4+ζ) hC (by linarith) hEnv.core I S C g
  have he : (fixedDepthProgram kernels I g).work=
      (mainSketchProgram I g).work+(coarseSupportProgram kernels S.initialA S.initialB).work+
        (mainCoreProgram kernels I S C g).work := by
    simp only [fixedDepthProgram,work_bind,S,C]
    omega
  unfold constantDistortionComparatorProgram
  rw [preparedFixedDepthProgram_work,he]
  omega

theorem exactGramComparatorProgram_complete_numeric
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck X D c ell : ℝ)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hC : 0 < Ck)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hD : 1 ≤ D) (hc : 0 ≤ c) (hell : 1 ≤ ell)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (htheta : I.theta=min (comparatorDimensionTheta m N) (1/1048576))
    (hm : 2 ≤ m) (hr : r ≤ ⌊Real.sqrt (m:ℝ)⌋₊) (hellEq : ell=Real.log (m:ℝ))
    (hMagnitude : comparatorScalarMagnitude I ≤ D*ell)
    (hconfidence : Real.log (1/I.delta) ≤ c*ell) (hside : Real.log (N:ℝ) ≤ 3*ell)
    (hraw : (comparatorOuterDegreeCap I+1)*(r+1) ≤ m) (g : MainRandomTape I) :
    ((2*m*(N+N)+N*N+mainRandomizedWork I (5+(exactGramComparatorProgram kernels I g).work):ℕ):ℝ) ≤
      2*(comparatorGramRowWorkCap kernels m N:ℝ)+
        comparatorTotalMainCoefficient D c*X*(N:ℝ)^2*(N/m:ℝ)^(1/4:ℝ)*ell^12+
        comparatorTotalSmallCoefficient D*(Ck+1)*(m:ℝ)^(9/4+ζ)*ell^2 := by
  let S := exactComparatorSketches I.A I.B 1
  let C : MainSupportData S := (coarseSupportProgram kernels I.A I.Bᵀ).eval
  apply comparator_total_numeric_of_body kernels ζ χ χOut Ck X D c ell hζ hχ hχOut hC
    hχX hχOutX hD hc hell hEnv I haccuracy htheta S C hm hr hellEq hMagnitude hconfidence hside hraw
  have hs := comparator_support_uniform_work kernels I.A I.Bᵀ (by omega : 1 ≤ m) le_rfl le_rfl
  have hcore := mainCoreProgram_work_bound kernels Ck (9/4+ζ) hC (by linarith) hEnv.core I S C g
  rw [exactGramComparatorProgram_work,preparedMainCoreProgram_work]
  dsimp [S,C] at hcore ⊢
  omega

end
end HierarchicalAbsoluteSpectral
