import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalNumeric
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalPreprocessing
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalWidth
import HierarchicalAbsoluteSpectral.MainFamilyProgramActionOverhead
import HierarchicalAbsoluteSpectral.MainFamilyProgramPreparationCost

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
variable {N m r : ℕ}

def familyFinalRepetitionCoefficient (D c : ℝ) : ℝ :=
  (c+6+familyQueryCapCoefficient D c)/Real.log 2

def familyFinalMetadataCoefficient (D c : ℝ) : ℝ :=
  2*D+familyQueryCapCoefficient D c+familyFinalRepetitionCoefficient D c+1

def familyFinalMainCoefficient (D c : ℝ) : ℝ :=
  1+1000*(familyQueryCapCoefficient D c+1)*(familyFinalRepetitionCoefficient D c+1)*
      (2*(familyCombinedDegreeCoefficient D c+2)*((2*D+1)*familyActionLeafCoefficient D c)+202)+
    2*(2*D+1)*familySketchFormationCoefficient D c+100*(familyFinalMetadataCoefficient D c)^2

def familyFinalCoreCoefficient (D c C ζ : ℝ) : ℝ :=
  1000*(familyQueryCapCoefficient D c+1)*(familyFinalRepetitionCoefficient D c+1)*
      (familyFinalCoreConstant+102)*(C+1)+
    (2*C*(2*familyCoarseRowCoefficient D c)^(9/4+ζ)+11*(C+1))

theorem family_final_constants_positive (D c C ζ : ℝ) (hD : 1 ≤ D)
    (hc : 0 ≤ c) (hC : 0 < C) :
    1 ≤ familyFinalMainCoefficient D c ∧ 0 ≤ familyFinalCoreCoefficient D c C ζ := by
  have hD0 : 0 ≤ D := by linarith
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hE := familyRowCoefficient_ge_one D c hD0 hc
  have hfine : 0 ≤ familyFineLeafCoefficient D c := by unfold familyFineLeafCoefficient; positivity
  have hleaf : 0 ≤ familyActionLeafCoefficient D c := by unfold familyActionLeafCoefficient; positivity
  have hpad : 0 ≤ familyPaddingCoefficient D := by unfold familyPaddingCoefficient; positivity
  have hform : 0 ≤ familySketchFormationCoefficient D c := by unfold familySketchFormationCoefficient; positivity
  have hquery : 0 ≤ familyQueryCapCoefficient D c := by unfold familyQueryCapCoefficient; positivity
  have hrep : 0 ≤ familyFinalRepetitionCoefficient D c := by unfold familyFinalRepetitionCoefficient; positivity
  have hdeg : 0 ≤ familyCombinedDegreeCoefficient D c := by
    unfold familyCombinedDegreeCoefficient familyQueryDegreeCoefficient familyStrongDegreeCoefficient
    positivity
  have hbase : 0 ≤ familyFinalCoreConstant := by unfold familyFinalCoreConstant; positivity
  have hcoarse : 0 ≤ familyCoarseRowCoefficient D c := by unfold familyCoarseRowCoefficient; linarith
  constructor
  · unfold familyFinalMainCoefficient
    have h1 : 0 ≤ 1000*(familyQueryCapCoefficient D c+1)*(familyFinalRepetitionCoefficient D c+1)*
      (2*(familyCombinedDegreeCoefficient D c+2)*((2*D+1)*familyActionLeafCoefficient D c)+202) := by positivity
    have h2 : 0 ≤ 2*(2*D+1)*familySketchFormationCoefficient D c := by positivity
    nlinarith [sq_nonneg (familyFinalMetadataCoefficient D c)]
  · unfold familyFinalCoreCoefficient
    positivity

theorem family_final_actual_work_log_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FamilyProblem N m r) (g : FamilyRandomTape I)
    (ζ χ χOut X Ck D c : ℝ) (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hC : 0 < Ck)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m) (hmLog : 1 ≤ Real.log (m:ℝ))
    (hL : I.prepared.scalars.schedule.depth ≠ 0)
    (hscale : Real.log (1/Real.sqrt (m/N:ℝ)) ≤ D*Real.log (m:ℝ))
    (hδ : (m:ℝ)^(-c) ≤ I.delta)
    (hraw : (familyCombinedDegreeCeiling I D c+1)*(r+1) ≤ m) :
    (growingDepthExplicitWork kernels I g:ℝ) ≤
      familyFinalMainCoefficient D c*X*(N:ℝ)^2*
        Real.exp (familyFactorLoglogConstant D*(1+Real.log (Real.log (2*(m:ℝ))))^2)*
          (Real.log (m:ℝ))^12+
      familyFinalCoreCoefficient D c Ck ζ*(m:ℝ)^(9/4+ζ)*(Real.log (m:ℝ))^(3*(9/4+ζ)+2) := by
  let P := I.prepared
  let S := (mainSketchProgram P.fixed g).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  let ell := Real.log (m:ℝ)
  let E := Real.exp (familyFactorLoglogConstant D*(1+Real.log (Real.log (2*(m:ℝ))))^2)
  let M := familyActionWorkScale I P D c χ
  let CT := familyQueryCapCoefficient D c
  let CR := familyFinalRepetitionCoefficient D c
  let CA := (2*D+1)*familyActionLeafCoefficient D c
  let CQ := familyCombinedDegreeCoefficient D c+2
  let U := familyFinalMetadataCoefficient D c
  let Q := familyCombinedDegreeCeiling I D c
  let p : ℝ := 9/4+ζ
  have hD0 : 0 ≤ D := by linarith
  have hm1 : 1 ≤ m := by omega
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hN : (1:ℝ) ≤ N := by exact_mod_cast I.side_positive
  have hNm : (m:ℝ) ≤ N := by exact_mod_cast I.core_le_side
  have hX : 1 ≤ X := hχ.trans hχX
  have hχ0 : 0 ≤ χ := by linarith
  have hCT : 0 ≤ CT := by dsimp [CT,familyQueryCapCoefficient]; positivity
  have hCR : 0 ≤ CR := by dsimp [CR,familyFinalRepetitionCoefficient]; positivity
  have hrow := familyRowCoefficient_ge_one D c hD0 hc
  have hfine : 0 ≤ familyFineLeafCoefficient D c := by unfold familyFineLeafCoefficient; positivity
  have hleaf : 1 ≤ familyActionLeafCoefficient D c := by unfold familyActionLeafCoefficient; linarith
  have hCA : 0 ≤ CA := by dsimp [CA]; positivity
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ,familyCombinedDegreeCoefficient,familyQueryDegreeCoefficient,familyStrongDegreeCoefficient]
    positivity
  have hp : 2 ≤ p := by dsimp [p]; linarith
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hCTcap : (P.fixed.queryCap:ℝ) ≤ CT*ell :=
    P.queryCap_log_bound I hL D c hD0 hc (hlog2.trans hmLog) hscale hδ
  have hCRrep : (P.fixed.repetitions:ℝ) ≤ CR*ell :=
    P.repetitions_log_bound I hL D c hD0 hc (hlog2.trans hmLog) hscale hδ
  have hdepth0 := familySchedule_depth_log_linear (Real.sqrt_pos.mpr I.ratio_positive)
    P.scalars.schedule_scale (by rw [familyScalarSchedule_scale_depth]; exact Nat.pos_of_ne_zero hL) hscale
  rw [← P.normal_depth I hL] at hdepth0
  have hdepth : (P.depth:ℝ) ≤ 2*D*ell := by
    have hh := mul_le_mul_of_nonneg_left family_log_two_lower (Nat.cast_nonneg P.depth)
    nlinarith
  have hU : 1 ≤ U := by dsimp [U,familyFinalMetadataCoefficient]; nlinarith only [hD,hCT,hCR]
  have hUT : CT ≤ U := by dsimp [U,familyFinalMetadataCoefficient]; nlinarith only [hD,hCR]
  have hUR : CR ≤ U := by dsimp [U,familyFinalMetadataCoefficient]; nlinarith only [hD,hCT]
  have hUD : 2*D ≤ U := by dsimp [U,familyFinalMetadataCoefficient]; linarith
  have hrest := family_final_rest_numeric I U ell hU hmLog
    (hdepth.trans (mul_le_mul_of_nonneg_right hUD (by linarith)))
    (hCTcap.trans (mul_le_mul_of_nonneg_right hUT (by linarith)))
    (hCRrep.trans (mul_le_mul_of_nonneg_right hUR (by linarith)))
  have hK := familyActionCostConstant_ge_one D hD
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogK : 0 ≤ Real.log (2*familyActionCostConstant D) := Real.log_nonneg (by linarith)
  have hK0 : 0 ≤ familyFactorLoglogConstant D := by unfold familyFactorLoglogConstant; positivity
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hK0 (sq_nonneg _))
  have hF := familyFactorActionOverhead_ge_one I P D c hD hc hmLog
  have hM : 1 ≤ M := by
    rw [show M=familyFactorActionOverhead I P D c*χ*(N:ℝ)*(m:ℝ) by
      dsimp [M]; exact familyActionWorkScale_eq I P D c χ]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hχ) hN) hmR
  have hactions := fun b hb => P.six_action_bounds I hL kernels χ hχ hEnv.row D c hD hc hm hmLog hscale hδ g C b hb
  have hdegrees := P.combined_degree_bounds I hL S C D c hD0 hc (hlog2.trans hmLog) hscale hδ
  have hquery : ∀ hr : r < C.pair.dimension, mainQueryDegree P.fixed S C hr ≤ Q := by
    intro hr
    have hh := hdegrees.1 hr
    dsimp only [Q]
    omega
  have hcoreEnv := family_final_six_core_envelope kernels ζ χ χOut Ck M hζ hχ hχOut hC hM hEnv
    P.fixed (P.normal_initial I hL) S C hm I.rank_le_sqrt Q hraw hactions hquery hdegrees.2
  have hQ0 := familyCombinedDegreeCeiling_bound I D c hD0 hc hmLog
  have hratio : 1 ≤ (N:ℝ)/m := (le_div_iff₀ (show (0:ℝ) < m by exact_mod_cast I.core_positive)).mpr (by simpa using hNm)
  have hratio5 : 1 ≤ ((N:ℝ)/m)*ell^5 := one_le_mul_of_one_le_of_one_le hratio (one_le_pow₀ hmLog)
  have hQ : (Q:ℝ)+1 ≤ CQ*((N:ℝ)/m)*ell^5 := by dsimp [Q,CQ,ell]; nlinarith only [hQ0,hratio5]
  have hFbound := P.factor_action_overhead_polylog I hL D c hD hc hmLog hscale
  have hAction : M ≤ CA*E*χ*(N:ℝ)*(m:ℝ)*ell^5 := by
    rw [show M=familyFactorActionOverhead I P D c*χ*(N:ℝ)*(m:ℝ) by
      dsimp [M]; exact familyActionWorkScale_eq I P D c χ]
    have hf : familyFactorActionOverhead I P D c ≤ CA*ell^5*E := hFbound
    calc
      _ ≤ (CA*ell^5*E)*χ*(N:ℝ)*(m:ℝ) := by gcongr
      _ = _ := by ring
  have hcore := family_final_core_numeric kernels P.fixed S C Ck ζ χ χOut X M E ell CA CQ CT CR Q
    hC hζ hχ hχOut hχX hχOutX hM hE hmLog hCA hCQ hCT hCR hm1 hCTcap hCRrep hQ hAction hcoreEnv
  have hrows := P.actual_initial_rows_scale I hL D c hD0 hc hm hmLog hscale hδ g
  have hR : 1 ≤ familyCoarseRowCoefficient D c := by unfold familyCoarseRowCoefficient; linarith
  have hcoarse := family_final_coarse_numeric kernels Ck p (familyCoarseRowCoefficient D c) ell hC hp hR hmLog hEnv.core
    m (S.levelA 0).1 (S.levelB 0).1 hm1 hrows.1 hrows.2
  have hform := P.sketch_formation_cap_scale I hL D c hD0 hc hm hmLog hscale hδ
  have hformC : 0 ≤ familySketchFormationCoefficient D c := by
    unfold familySketchFormationCoefficient familyPaddingCoefficient
    positivity
  have hdepth1 : (P.depth:ℝ)+1 ≤ (2*D+1)*ell := by nlinarith only [hdepth,hmLog]
  have hformation := mul_le_mul hdepth1 hform (Nat.cast_nonneg _) (by positivity : 0 ≤ (2*D+1)*ell)
  have hformationN := mul_le_mul_of_nonneg_right hNm
    (show 0 ≤ 2*(2*D+1)*familySketchFormationCoefficient D c*(N:ℝ)*ell^2 by positivity)
  have hformation' : (((P.depth+1)*2*sketchFormationCap N m P.fixed.sketchFailure:ℕ):ℝ) ≤
      2*(2*D+1)*familySketchFormationCoefficient D c*(N:ℝ)^2*ell^2 := by
    push_cast
    nlinarith only [hformation,hformationN]
  have hwork := family_final_explicit_work_cap kernels I g Ck p hC hp hEnv.core
  have hworkR : (growingDepthExplicitWork kernels I g:ℝ) ≤
      (familyFinalRestCap I:ℝ)+(((P.depth+1)*2*sketchFormationCap N m P.fixed.sketchFailure:ℕ):ℝ)+
      (coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1:ℝ)+
      (mainCoreWorkCap kernels P.fixed S C Ck p:ℝ) := by
    dsimp only [familyFinalPreprocessingCap] at hwork
    simp only [← add_assoc] at hwork
    exact_mod_cast hwork
  have hmainScale : (N:ℝ)^2*ell^2 ≤ X*(N:ℝ)^2*E*ell^12 := by
    have h1 : ell^2 ≤ ell^12 := pow_le_pow_right₀ hmLog (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hX hE) (show 0 ≤ ell^12 by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans (by simpa only [one_mul,mul_assoc] using h2)) (sq_nonneg (N:ℝ))
    nlinarith only [h3]
  have hpow2 : ell^2 ≤ ell^(3*p+2) := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_le hmLog (show (2:ℝ) ≤ 3*p+2 by linarith))
  have hpow3 : ell^(3*p) ≤ ell^(3*p+2) := Real.rpow_le_rpow_of_exponent_le hmLog (by linarith)
  have hmainC : 0 ≤ 1000*(CT+1)*(CR+1)*(2*CQ*CA+202) := by positivity
  have hcoreC : 0 ≤ 1000*(CT+1)*(CR+1)*(familyFinalCoreConstant+102)*(Ck+1) := by
    have hh : 0 ≤ familyFinalCoreConstant := by unfold familyFinalCoreConstant; positivity
    positivity
  have hcoarseC : 0 ≤ 2*Ck*(2*familyCoarseRowCoefficient D c)^p+11*(Ck+1) := by positivity
  have hcoreGrow := mul_le_mul_of_nonneg_left hpow2
    (show 0 ≤ 1000*(CT+1)*(CR+1)*(familyFinalCoreConstant+102)*(Ck+1)*(m:ℝ)^p by positivity)
  have hcoarseGrow := mul_le_mul_of_nonneg_left hpow3
    (show 0 ≤ (2*Ck*(2*familyCoarseRowCoefficient D c)^p+11*(Ck+1))*(m:ℝ)^p by positivity)
  have hrestGrow := mul_le_mul_of_nonneg_left hmainScale (show 0 ≤ 100*U^2 by positivity)
  have hformGrow := mul_le_mul_of_nonneg_left hmainScale
    (show 0 ≤ 2*(2*D+1)*familySketchFormationCoefficient D c by positivity)
  have hspare : 0 ≤ X*(N:ℝ)^2*E*ell^12 := by positivity
  dsimp only [familyFinalMainCoefficient,familyFinalCoreCoefficient] at ⊢
  dsimp only [CT,CR,CA,CQ,U,p,E,ell] at hcore hcoarse hworkR hrest hformation' hmainScale hcoreGrow hcoarseGrow hrestGrow hformGrow hspare ⊢
  nlinarith only [hworkR,hrest,hformation',hcoarse,hcore,hcoreGrow,hcoarseGrow,hrestGrow,hformGrow,hspare]

end
end HierarchicalAbsoluteSpectral
