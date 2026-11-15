import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeGrowth
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalSketchCost

/-! Complete comparator operation accounting beyond the small-core cap:
input entries, Gaussian draws, executed sketch formation, true/sketched
Grams, scalar counters and every dense output entry. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {N m r : ℕ}

def comparatorMetadataWorkCap (I : FixedProblem N m N r 1) : ℕ :=
  N*N+2*m*N+2*r*m+I.queryCap*I.repetitions*((r+1)*m+2*m*m)+
    4+3*I.queryCap+2*I.repetitions+29+5

def comparatorNumericRestCap (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem N m N r 1) : ℕ :=
  twoLevelInitialSketchWorkCap N m I.sketchFailure+
    2*comparatorGramRowWorkCap kernels m N+psdGramCost kernels m+2*kernelEnvelope kernels m+
      comparatorMetadataWorkCap I

def comparatorRestNumericCoefficient (D c : ℝ) : ℝ :=
  100*(30000*D)^2+5*twoLevelSketchLogCoefficient (c+40)

def comparatorTotalMainCoefficient (D c : ℝ) : ℝ :=
  comparatorCoreNumericCoefficient D+comparatorRestNumericCoefficient D c

def comparatorTotalSmallCoefficient (D : ℝ) : ℝ := comparatorSmallNumericCoefficient D+11

theorem comparator_metadata_numeric (I : FixedProblem N m N r 1)
    (U ell : ℝ) (hU : 1 ≤ U) (hell : 1 ≤ ell)
    (hcap : (I.queryCap:ℝ) ≤ U*ell) (hrep : (I.repetitions:ℝ) ≤ U*ell) :
    (comparatorMetadataWorkCap I:ℝ) ≤ 100*U^2*(N:ℝ)^2*ell^2 := by
  let V : ℝ := U^2*(N:ℝ)^2*ell^2
  have hm : (1:ℝ) ≤ m := by exact_mod_cast I.rank_positive.trans I.rank_le_core
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (I.rank_positive.trans I.rank_le_core).trans I.core_le_rows
  have hNm : (m:ℝ) ≤ N := by exact_mod_cast I.core_le_rows
  have hUE : 1 ≤ U*ell := one_le_mul_of_one_le_of_one_le hU hell
  have hUN : 1 ≤ U*ell*(N:ℝ) := one_le_mul_of_one_le_of_one_le hUE hN
  have hV1 : 1 ≤ V := by
    have hh := one_le_pow₀ hUN (n:=2)
    dsimp [V]
    nlinarith only [hh]
  have hUV : U*ell ≤ V := by
    have h1 : U*ell ≤ U*ell*(N:ℝ) := le_mul_of_one_le_right (by positivity) hN
    have h2 := le_self_pow₀ hUN (by norm_num : (2:ℕ) ≠ 0)
    dsimp [V]
    nlinarith only [h1,h2]
  have hNV : (N:ℝ)^2 ≤ V := by
    have hh := mul_le_mul_of_nonneg_right (one_le_pow₀ hUE (n:=2)) (sq_nonneg (N:ℝ))
    dsimp [V]
    nlinarith only [hh]
  have hmmV : (m:ℝ)^2 ≤ V := (pow_le_pow_left₀ (Nat.cast_nonneg m) hNm 2).trans hNV
  have hreads : ((2*m*N:ℕ):ℝ) ≤ 2*V := by
    have hh := mul_le_mul_of_nonneg_right hNm (Nat.cast_nonneg N)
    push_cast
    nlinarith only [hh,hNV]
  have hTV : (I.queryCap:ℝ) ≤ V := hcap.trans hUV
  have hRV : (I.repetitions:ℝ) ≤ V := hrep.trans hUV
  have hbody : (r+1)*m+2*m*m ≤ 4*m*m := by
    have h1 := I.rank_le_core
    have h2 : 1 ≤ m := I.rank_positive.trans I.rank_le_core
    nlinarith
  have hbodyR : (((r+1)*m+2*m*m:ℕ):ℝ) ≤ 4*(m:ℝ)^2 := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,pow_two,mul_assoc] using
      (Nat.cast_le.mpr hbody : (((r+1)*m+2*m*m:ℕ):ℝ) ≤ ((4*m*m:ℕ):ℝ))
  have hqr := mul_le_mul hcap hrep (Nat.cast_nonneg _) (by positivity : 0 ≤ U*ell)
  have hdraws := mul_le_mul hqr hbodyR (Nat.cast_nonneg _) (by positivity : 0 ≤ U*ell*(U*ell))
  have hsize := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg m) hNm 2)
    (show 0 ≤ 4*U^2*ell^2 by positivity)
  have hdraws' : (I.queryCap:ℝ)*I.repetitions*(((r+1)*m+2*m*m:ℕ):ℝ) ≤ 4*V := by
    dsimp [V]
    nlinarith only [hdraws,hsize]
  have hinit : ((2*r*m:ℕ):ℝ) ≤ 2*V := by
    have hh := Nat.mul_le_mul_right m (Nat.mul_le_mul_left 2 I.rank_le_core)
    have hhR : ((2*r*m:ℕ):ℝ) ≤ 2*(m:ℝ)^2 := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat,pow_two,mul_assoc] using
        (Nat.cast_le.mpr hh : ((2*r*m:ℕ):ℝ) ≤ ((2*m*m:ℕ):ℝ))
    nlinarith only [hhR,hmmV]
  unfold comparatorMetadataWorkCap
  push_cast
  push_cast at hdraws' hinit hreads
  dsimp [V] at hV1 hNV hTV hRV hdraws' hinit hreads ⊢
  nlinarith only [hV1,hNV,hTV,hRV,hdraws',hinit,hreads]

theorem comparator_total_of_body (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem N m N r 1) (body core : ℕ)
    (hbody : body ≤ 4+3*I.queryCap+2*I.repetitions+29+
      4*sketchFormationCap N m I.sketchFailure+2*comparatorGramRowWorkCap kernels m N+
        psdGramCost kernels m+2*kernelEnvelope kernels m+core) :
    2*m*(N+N)+N*N+mainRandomizedWork I (5+body) ≤ comparatorNumericRestCap kernels I+core := by
  rw [mainRandomizedWork_eq]
  unfold comparatorNumericRestCap comparatorMetadataWorkCap twoLevelInitialSketchWorkCap
  have hi : 2*m*(N+N)=2*m*N+2*m*N := by ring
  rw [hi]
  omega

theorem comparator_numeric_rest_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (ζ χ χOut Ck D c ell : ℝ)
    (hζ : 0 < ζ) (hC : 0 < Ck) (hD : 1 ≤ D) (hc : 0 ≤ c) (hell : 1 ≤ ell)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (I : FixedProblem N m N r 1) (haccuracy : I.accuracy=comparatorAccuracy)
    (hm : 2 ≤ m) (hellEq : ell=Real.log (m:ℝ))
    (hMagnitude : comparatorScalarMagnitude I ≤ D*ell)
    (hconfidence : Real.log (1/I.delta) ≤ c*ell) (hside : Real.log (N:ℝ) ≤ 3*ell) :
    (comparatorNumericRestCap kernels I:ℝ) ≤
      2*(comparatorGramRowWorkCap kernels m N:ℝ)+11*(Ck+1)*(m:ℝ)^(9/4+ζ)+
        comparatorRestNumericCoefficient D c*(N:ℝ)^2*ell^2 := by
  have hm1 : 1 ≤ m := by omega
  have hN : 0 < N := (show 0 < m by omega).trans_le I.core_le_rows
  have hT : (I.queryCap:ℝ) ≤ (30000*D)*ell := by
    have hh := (comparator_query_cap_bound I haccuracy).trans
      (mul_le_mul_of_nonneg_left hMagnitude (by norm_num : (0:ℝ) ≤ 10000))
    nlinarith only [hh,mul_nonneg (show 0 ≤ D by linarith) (show 0 ≤ ell by linarith)]
  have hR : (I.repetitions:ℝ) ≤ (30000*D)*ell := by
    have hh := (comparator_repetitions_bound I haccuracy).trans
      (mul_le_mul_of_nonneg_left hMagnitude (by norm_num : (0:ℝ) ≤ 30000))
    nlinarith only [hh]
  have hmeta := comparator_metadata_numeric I (30000*D) ell (by linarith) hell hT hR
  have hβ : 0 < I.sketchFailure := mainSketchFailure_positive I
  have hβ1 : I.sketchFailure ≤ 1 := by
    have hh := I.delta_lt_one
    norm_num [FixedProblem.sketchFailure]
    linarith
  have hβlog : Real.log (1/I.sketchFailure) ≤ (c+40)*ell := by
    have he : Real.log (1/I.sketchFailure)=Real.log 40+Real.log (1/I.delta) := by
      unfold FixedProblem.sketchFailure
      norm_num
      rw [Real.log_div (by norm_num) I.delta_positive.ne']
      ring
    have h40 : Real.log (40:ℝ) ≤ 39 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 40)
      linarith
    rw [he]
    nlinarith only [hconfidence,h40,hell]
  have hsketch := twoLevelInitialSketchWorkCap_log_bound N m I.sketchFailure (c+40) hN hm hβ hβ1
    (by linarith) (by simpa only [hellEq] using hβlog)
  have hK : 0 ≤ twoLevelSketchLogCoefficient (c+40) := by
    have hlog := family_log_two_lower
    unfold twoLevelSketchLogCoefficient
    positivity
  have hlogs : 1+Real.log (N:ℝ)+Real.log (m:ℝ) ≤ 5*ell := by rw [← hellEq]; linarith
  have hsketch' : (twoLevelInitialSketchWorkCap N m I.sketchFailure:ℝ) ≤
      5*twoLevelSketchLogCoefficient (c+40)*(N:ℝ)^2*ell^2 := by
    have h1 := mul_le_mul_of_nonneg_left hlogs
      (show 0 ≤ twoLevelSketchLogCoefficient (c+40)*(m:ℝ)*(N:ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right (by exact_mod_cast I.core_le_rows : (m:ℝ) ≤ N)
      (show 0 ≤ 5*twoLevelSketchLogCoefficient (c+40)*(N:ℝ)*ell by positivity)
    have h3 := mul_le_mul_of_nonneg_left (show ell ≤ ell^2 by nlinarith)
      (show 0 ≤ 5*twoLevelSketchLogCoefficient (c+40)*(N:ℝ)^2 by positivity)
    nlinarith only [hsketch,h1,h2,h3]
  have hpsd := comparator_psd_cost_ambient kernels Ck (9/4+ζ) hC (by linarith) hEnv.core hm1 le_rfl
  have henv := comparator_kernel_envelope_ambient kernels Ck (9/4+ζ) hC hEnv.core hm1 le_rfl
  have hsmall : ((psdGramCost kernels m+2*kernelEnvelope kernels m:ℕ):ℝ) ≤
      11*(Ck+1)*(m:ℝ)^(9/4+ζ) := by
    push_cast
    nlinarith [show 0 ≤ (m:ℝ)^(9/4+ζ) by positivity]
  unfold comparatorNumericRestCap comparatorRestNumericCoefficient
  push_cast
  push_cast at hsmall
  nlinarith only [hmeta,hsketch',hsmall]

end
end HierarchicalAbsoluteSpectral
