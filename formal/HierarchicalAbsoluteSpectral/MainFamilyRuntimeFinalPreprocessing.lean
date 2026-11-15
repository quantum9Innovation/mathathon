import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalProgram
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalSketchCost

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
variable {N m r : ℕ}

theorem family_final_coarse_numeric
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p R ell : ℝ) (hC : 0 < C) (hp : 2 ≤ p) (hR : 1 ≤ R) (hell : 1 ≤ ell)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ C*(D:ℝ)^p)
    (m s t : ℕ) (hm : 1 ≤ m)
    (hs : (s:ℝ) ≤ R*(m:ℝ)*ell^3) (ht : (t:ℝ) ≤ R*(m:ℝ)*ell^3) :
    (coarseSupportWorkCap kernels m s t:ℝ) ≤
      (2*C*(2*R)^p+11*(C+1))*(m:ℝ)^p*ell^(3*p) := by
  let D : ℕ := ⌈R*(m:ℝ)*ell^3⌉₊
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hR0 : 0 ≤ R := by linarith
  have hell0 : 0 ≤ ell := by linarith
  have hprod : 1 ≤ R*ell^3 := one_le_mul_of_one_le_of_one_le hR (one_le_pow₀ hell)
  have hmD : m ≤ D := family_final_le_nat_ceil (by
    have hh := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg m)
    nlinarith only [hh])
  have hsD : s ≤ D := family_final_le_nat_ceil hs
  have htD : t ≤ D := family_final_le_nat_ceil ht
  have hD : 1 ≤ D := hm.trans hmD
  have hlarge : 1 ≤ R*(m:ℝ)*ell^3 := by
    have hh := mul_le_mul hprod hmr (by norm_num : (0:ℝ) ≤ 1) (by linarith : 0 ≤ R*ell^3)
    nlinarith only [hh]
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ R*(m:ℝ)*ell^3 by positivity)).le
  have hsize : (D:ℝ) ≤ 2*R*(m:ℝ)*ell^3 := by change (⌈R*(m:ℝ)*ell^3⌉₊:ℝ) ≤ _; linarith
  have hpower : (D:ℝ)^p ≤ (2*R)^p*(m:ℝ)^p*ell^(3*p) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg D) hsize (by linarith)).trans_eq
    rw [Real.mul_rpow (by positivity : 0 ≤ 2*R*(m:ℝ)) (by positivity : 0 ≤ ell^3),
      Real.mul_rpow (by positivity : 0 ≤ 2*R) (Nat.cast_nonneg m),
      ← Real.rpow_natCast ell 3,← Real.rpow_mul hell0]
    norm_num
  have hleft := (hK m s m D hD hmD hsD hmD).trans
    (mul_le_mul_of_nonneg_left hpower hC.le)
  have hright := (hK m t m D hD hmD htD hmD).trans
    (mul_le_mul_of_nonneg_left hpower hC.le)
  have hcoarse := coarseSupportWorkCap_bound_of_scalar_kernels kernels C p hC hp hK m s t hm
    (C*((2*R)^p*(m:ℝ)^p*ell^(3*p))) hleft hright
  have hellpow : 1 ≤ ell^(3*p) := Real.one_le_rpow hell (by linarith)
  have hsmall := mul_le_mul_of_nonneg_left hellpow
    (show 0 ≤ 11*(C+1)*(m:ℝ)^p by positivity)
  nlinarith only [hcoarse,hsmall]

theorem family_final_formation_numeric
    (I : FamilyProblem N m r) (D CD DN ell : ℝ)
    (hD : 0 ≤ D) (hCD : 0 ≤ CD) (hDN : 0 ≤ DN) (hell : 1 ≤ ell)
    (hm : 2 ≤ m) (hellEq : ell=Real.log (m:ℝ))
    (hdepth : (I.prepared.depth:ℝ) ≤ CD*ell)
    (hside : Real.log (N:ℝ) ≤ DN*ell)
    (hconfidence : Real.log (1/I.prepared.fixed.sketchFailure) ≤ D*ell) :
    (((I.prepared.depth+1)*2*sketchFormationCap N m I.prepared.fixed.sketchFailure:ℕ):ℝ) ≤
      (CD+1)*twoLevelSketchLogCoefficient D*(DN+2)*(N:ℝ)^2*ell^2 := by
  have hβ : 0 < I.prepared.fixed.sketchFailure := mainSketchFailure_positive _
  have hβ1 : I.prepared.fixed.sketchFailure ≤ 1 := by
    unfold FixedProblem.sketchFailure
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := I.prepared.fixed.delta_lt_one
    have hL : (0:ℝ) ≤ I.prepared.depth := Nat.cast_nonneg _
    linarith
  have hcount := twoLevelInitialSketchWorkCap_log_bound N m I.prepared.fixed.sketchFailure D
    I.side_positive hm hβ hβ1 hD (by simpa only [hellEq] using hconfidence)
  have hformation : (2*sketchFormationCap N m I.prepared.fixed.sketchFailure:ℕ) ≤
      twoLevelInitialSketchWorkCap N m I.prepared.fixed.sketchFailure := by
    unfold twoLevelInitialSketchWorkCap
    omega
  have hdepth' : (I.prepared.depth:ℝ)+1 ≤ (CD+1)*ell := by nlinarith
  have hlogs : 1+Real.log (N:ℝ)+Real.log (m:ℝ) ≤ (DN+2)*ell := by rw [← hellEq]; nlinarith
  have hK : 0 ≤ twoLevelSketchLogCoefficient D := by unfold twoLevelSketchLogCoefficient; positivity
  have hcap : (2*sketchFormationCap N m I.prepared.fixed.sketchFailure:ℕ) ≤ _ := hformation
  have hcapR : ((2*sketchFormationCap N m I.prepared.fixed.sketchFailure:ℕ):ℝ) ≤
      twoLevelSketchLogCoefficient D*(m:ℝ)*(N:ℝ)*((DN+2)*ell) := by
    apply (Nat.cast_le.mpr hformation).trans
    exact hcount.trans (mul_le_mul_of_nonneg_left hlogs (by positivity))
  have hmul := mul_le_mul hdepth' hcapR (Nat.cast_nonneg _)
    (show 0 ≤ (CD+1)*ell by positivity)
  have hNm : (m:ℝ) ≤ N := by exact_mod_cast I.core_le_side
  have hsize := mul_le_mul_of_nonneg_right hNm
    (show 0 ≤ (CD+1)*twoLevelSketchLogCoefficient D*(DN+2)*(N:ℝ)*ell^2 by positivity)
  push_cast at hmul ⊢
  nlinarith only [hmul,hsize]

theorem family_final_rest_numeric
    (I : FamilyProblem N m r) (U ell : ℝ) (hU : 1 ≤ U) (hell : 1 ≤ ell)
    (hdepth : (I.prepared.depth:ℝ) ≤ U*ell)
    (hcap : (I.prepared.fixed.queryCap:ℝ) ≤ U*ell)
    (hrep : (I.prepared.fixed.repetitions:ℝ) ≤ U*ell) :
    (familyFinalRestCap I:ℝ) ≤ 100*U^2*(N:ℝ)^2*ell^2 := by
  let V := U^2*(N:ℝ)^2*ell^2
  have hN : (1:ℝ) ≤ N := by exact_mod_cast I.side_positive
  have hm : (1:ℝ) ≤ m := by exact_mod_cast I.core_positive
  have hNm : (m:ℝ) ≤ N := by exact_mod_cast I.core_le_side
  have hrm : r ≤ m := I.rank_le_core
  have hUE : 1 ≤ U*ell := one_le_mul_of_one_le_of_one_le hU hell
  have hUN : 1 ≤ U*ell*(N:ℝ) := one_le_mul_of_one_le_of_one_le hUE hN
  have hV1 : 1 ≤ V := by
    have hh := one_le_pow₀ hUN (n:=2)
    dsimp [V]
    nlinarith only [hh]
  have hUV : U*ell ≤ V := by
    have hfirst : U*ell ≤ U*ell*(N:ℝ) := le_mul_of_one_le_right (by positivity) hN
    have hsecond : U*ell*(N:ℝ) ≤ (U*ell*(N:ℝ))^2 := le_self_pow₀ hUN (by norm_num)
    dsimp [V]
    nlinarith only [hfirst,hsecond]
  have hNV : (N:ℝ)^2 ≤ V := by
    have hh := mul_le_mul_of_nonneg_right (one_le_pow₀ hUE (n:=2)) (sq_nonneg (N:ℝ))
    dsimp [V]
    nlinarith only [hh]
  have hmNV : (m:ℝ)*(N:ℝ) ≤ V :=
    (mul_le_mul_of_nonneg_right hNm (Nat.cast_nonneg N)).trans (by simpa only [pow_two] using hNV)
  have hmmV : (m:ℝ)^2 ≤ V := (pow_le_pow_left₀ (Nat.cast_nonneg m) hNm 2).trans hNV
  have hLV : (I.prepared.depth:ℝ) ≤ V := hdepth.trans hUV
  have hTV : (I.prepared.fixed.queryCap:ℝ) ≤ V := hcap.trans hUV
  have hRV : (I.prepared.fixed.repetitions:ℝ) ≤ V := hrep.trans hUV
  have hprepare : ((familyPreparationProgram I).work:ℝ) ≤ 17*V := by
    have hh : ((familyPreparationProgram I).work:ℝ) ≤ 6*(I.prepared.depth:ℝ)+11 := by
      exact_mod_cast familyPreparationProgram_work_le I
    nlinarith only [hh,hLV,hV1]
  have hpad : (((2^dyadicPaddingLevel N:ℕ):ℝ)) ≤ 2*(N:ℝ) := by
    exact_mod_cast (dyadicPaddingLevel_lt_two N I.side_positive).le
  have hLplus : (I.prepared.depth:ℝ)+1 ≤ 2*(U*ell) := by nlinarith only [hdepth,hUE]
  have hpadded := mul_le_mul hLplus hpad (by positivity : (0:ℝ) ≤ (2^dyadicPaddingLevel N:ℕ))
    (by positivity : 0 ≤ 2*(U*ell))
  have hUNV : U*ell*(N:ℝ) ≤ V := by
    have hh : U*ell*(N:ℝ) ≤ (U*ell*(N:ℝ))^2 := le_self_pow₀ hUN (by norm_num)
    dsimp [V]
    nlinarith only [hh]
  have hpadded' : 6*((I.prepared.depth:ℝ)+1)*(2^dyadicPaddingLevel N:ℕ) ≤ 24*V := by
    nlinarith only [hpadded,hUNV]
  have hbody : (r+1)*m+2*m*m ≤ 4*m*m := by
    have hm1 := I.core_positive
    nlinarith only [hrm,hm1]
  have hbodyR : (((r+1)*m+2*m*m:ℕ):ℝ) ≤ 4*(m:ℝ)^2 := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,pow_two,mul_assoc] using
      (Nat.cast_le.mpr hbody : (((r+1)*m+2*m*m:ℕ):ℝ) ≤ ((4*m*m:ℕ):ℝ))
  have hqr := mul_le_mul hcap hrep (Nat.cast_nonneg _)
    (by positivity : 0 ≤ U*ell)
  have hdraws := mul_le_mul hqr hbodyR (Nat.cast_nonneg _)
    (by positivity : 0 ≤ U*ell*(U*ell))
  have hsize := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg m) hNm 2)
    (show 0 ≤ 4*U^2*ell^2 by positivity)
  have hdraws' : (I.prepared.fixed.queryCap:ℝ)*I.prepared.fixed.repetitions*
      (((r+1)*m+2*m*m:ℕ):ℝ) ≤ 4*V := by
    dsimp [V]
    nlinarith only [hdraws,hsize]
  have hinit : ((2*r*m:ℕ):ℝ) ≤ 2*V := by
    have hh : 2*r*m ≤ 2*m*m := Nat.mul_le_mul_right m (Nat.mul_le_mul_left 2 hrm)
    have hhR : ((2*r*m:ℕ):ℝ) ≤ 2*(m:ℝ)^2 := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat,pow_two,mul_assoc] using
        (Nat.cast_le.mpr hh : ((2*r*m:ℕ):ℝ) ≤ ((2*m*m:ℕ):ℝ))
    nlinarith only [hhR,hmmV]
  unfold familyFinalRestCap
  push_cast
  push_cast at hpadded' hdraws' hinit
  dsimp only [V] at hV1 hUV hNV hmNV hmmV hLV hTV hRV hprepare hpadded' hdraws' hinit ⊢
  nlinarith only [hmNV,hNV,hprepare,hpadded',hdraws',hinit,hLV,hTV,hRV,hV1]

end
end HierarchicalAbsoluteSpectral
