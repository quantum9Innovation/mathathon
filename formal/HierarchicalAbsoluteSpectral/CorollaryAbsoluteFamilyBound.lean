import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamilyEnvelope
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamilyPreprocessing
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteActionsFamily
import HierarchicalAbsoluteSpectral.CorollaryAbsoluteNumeric
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalBound

/-! Realized work on the actual sketch event, with a rank-independent
logarithmic bound for all visited doubling attempts. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option pp.proofs false
noncomputable section
open Matrix
variable {N m : ℕ}

theorem absolute_family_actual_work_log_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteFamilyProblem N m) (g : AbsoluteFamilyTape I)
    (ζ χ χOut X Ck D c : ℝ) (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hC : 0 < Ck)
    (hEnv : FixedFamilyKernelEnvelopes ζ N m kernels χ χOut Ck)
    (hD : 1 ≤ D) (hc : 0 ≤ c) (hm : 2 ≤ m) (hmLog : 1 ≤ Real.log (m:ℝ))
    (hL : I.seed.prepared.scalars.schedule.depth ≠ 0)
    (hscale : Real.log (1/Real.sqrt (m/N:ℝ)) ≤ D*Real.log (m:ℝ))
    (hδ : (m:ℝ)^(-c) ≤ I.seed.delta)
    (hraw : (familyCombinedDegreeCeiling I.seed D c+1)*(Nat.sqrt m+1) ≤ m)
    (hsketch : MainSketchGood I.fixed.seed (mainSketchProgram I.fixed.seed g.1).eval)
    (hsmall : I.slackRank ≤ Nat.sqrt m/2) :
    (absoluteFamilyExplicitWork kernels I g:ℝ) ≤
      4*familyFinalMainCoefficient D c*X*(N:ℝ)^2*
        Real.exp (familyFactorLoglogConstant D*(1+Real.log (Real.log (2*(m:ℝ))))^2)*
          (Real.log (m:ℝ))^13+
      4*familyFinalCoreCoefficient D c Ck ζ*(m:ℝ)^(9/4+ζ)*(Real.log (m:ℝ))^(3*(9/4+ζ)+3) := by
  let P := I.seed.prepared
  let S := (mainSketchProgram I.fixed.seed g.1).eval
  let C := (coarseSupportProgram kernels S.initialA S.initialB).eval
  let ell := Real.log (m:ℝ)
  let E := Real.exp (familyFactorLoglogConstant D*(1+Real.log (Real.log (2*(m:ℝ))))^2)
  let M := familyActionWorkScale I.seed P D c χ
  let CT := familyQueryCapCoefficient D c
  let CR := familyFinalRepetitionCoefficient D c
  let CA := (2*D+1)*familyActionLeafCoefficient D c
  let CQ := familyCombinedDegreeCoefficient D c+2
  let U := familyFinalMetadataCoefficient D c
  let Q := familyCombinedDegreeCeiling I.seed D c
  let p : ℝ := 9/4+ζ
  have hD0 : 0 ≤ D := by linarith
  have hm1 : 1 ≤ m := by omega
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hN : (1:ℝ) ≤ N := by exact_mod_cast I.seed.side_positive
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
  have hCTcapP : (P.fixed.queryCap:ℝ) ≤ CT*ell :=
    P.queryCap_log_bound I.seed hL D c hD0 hc (hlog2.trans hmLog) hscale hδ
  have hCRrepP : (P.fixed.repetitions:ℝ) ≤ CR*ell :=
    P.repetitions_log_bound I.seed hL D c hD0 hc (hlog2.trans hmLog) hscale hδ
  have hCTcap : (I.fixed.seed.queryCap:ℝ) ≤ CT*ell := by
    rw [I.fixed_seed_eq]
    exact hCTcapP
  have hCRrep : (I.fixed.seed.repetitions:ℝ) ≤ CR*ell := by
    rw [I.fixed_seed_eq]
    exact hCRrepP
  have hdepth0 := familySchedule_depth_log_linear (Real.sqrt_pos.mpr I.seed.ratio_positive)
    P.scalars.schedule_scale (by rw [familyScalarSchedule_scale_depth]; exact Nat.pos_of_ne_zero hL) hscale
  rw [← P.normal_depth I.seed hL] at hdepth0
  have hdepth : (P.depth:ℝ) ≤ 2*D*ell := by
    have hh := mul_le_mul_of_nonneg_left family_log_two_lower (Nat.cast_nonneg P.depth)
    nlinarith
  have hU : 1 ≤ U := by dsimp [U,familyFinalMetadataCoefficient]; nlinarith only [hD,hCT,hCR]
  have hUT : CT ≤ U := by dsimp [U,familyFinalMetadataCoefficient]; nlinarith only [hD,hCR]
  have hUR : CR ≤ U := by dsimp [U,familyFinalMetadataCoefficient]; nlinarith only [hD,hCT]
  have hUD : 2*D ≤ U := by dsimp [U,familyFinalMetadataCoefficient]; linarith
  have hrest := family_final_rest_numeric I.seed U ell hU hmLog
    (hdepth.trans (mul_le_mul_of_nonneg_right hUD (by linarith)))
    (hCTcapP.trans (mul_le_mul_of_nonneg_right hUT (by linarith)))
    (hCRrepP.trans (mul_le_mul_of_nonneg_right hUR (by linarith)))
  have hK := familyActionCostConstant_ge_one D hD
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogK : 0 ≤ Real.log (2*familyActionCostConstant D) := Real.log_nonneg (by linarith)
  have hK0 : 0 ≤ familyFactorLoglogConstant D := by unfold familyFactorLoglogConstant; positivity
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hK0 (sq_nonneg _))
  have hF := familyFactorActionOverhead_ge_one I.seed P D c hD hc hmLog
  have hM : 1 ≤ M := by
    rw [show M=familyFactorActionOverhead I.seed P D c*χ*(N:ℝ)*(m:ℝ) by
      dsimp [M]; exact familyActionWorkScale_eq I.seed P D c χ]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hχ) hN) hmR
  let R := 2*I.fixed.slackRank
  have hR : R ≤ ⌊Real.sqrt (m:ℝ)⌋₊ := by
    rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
    have hh := I.internal_slackRank_le.trans hsmall
    dsimp [R]
    omega
  have hRm : R ≤ m := hR.trans (by
    rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
    exact Nat.sqrt_le_self m)
  have hrawR : (Q+1)*(R+1) ≤ m := by
    have hh : R ≤ Nat.sqrt m := by simpa only [Real.nat_floor_real_sqrt_eq_nat_sqrt] using hR
    exact (Nat.mul_le_mul_left (Q+1) (Nat.succ_le_succ hh)).trans hraw
  have hactions := fun b hb => I.fixed_six_action_bounds hL kernels χ hχ hEnv.row D c hD hc
    hm hmLog hscale hδ g.1 C R hR b hb
  have hdegrees := I.fixed_degree_bounds hL S C D c hD0 hc (hlog2.trans hmLog) hscale hδ
  have hquery : ∀ s ≤ R, ∀ hs : s < C.pair.dimension,
      absoluteQueryDegree I.fixed.seed S C hs ≤ Q := fun s _ hs => hdegrees.1 s hs
  have hzero : I.fixed.seed.accuracy 0=1/1024 := by
    rw [I.fixed_seed_eq]
    exact P.normal_initial I.seed hL
  have hcoreEnv := absolute_family_attempt_envelope kernels ζ χ χOut Ck M hζ hχ hχOut hC hM hEnv
    I.fixed.seed hzero S C hm R hR Q hrawR hactions hquery hdegrees.2
  have hQ0 := familyCombinedDegreeCeiling_bound I.seed D c hD0 hc hmLog
  have hratio : 1 ≤ (N:ℝ)/m := (le_div_iff₀ (show (0:ℝ) < m by exact_mod_cast I.core_positive)).mpr (by simpa using hNm)
  have hratio5 : 1 ≤ ((N:ℝ)/m)*ell^5 := one_le_mul_of_one_le_of_one_le hratio (one_le_pow₀ hmLog)
  have hQ : (Q:ℝ)+1 ≤ CQ*((N:ℝ)/m)*ell^5 := by dsimp [Q,CQ,ell]; nlinarith only [hQ0,hratio5]
  have hFbound := P.factor_action_overhead_polylog I.seed hL D c hD hc hmLog hscale
  have hAction : M ≤ CA*E*χ*(N:ℝ)*(m:ℝ)*ell^5 := by
    rw [show M=familyFactorActionOverhead I.seed P D c*χ*(N:ℝ)*(m:ℝ) by
      dsimp [M]; exact familyActionWorkScale_eq I.seed P D c χ]
    have hf : familyFactorActionOverhead I.seed P D c ≤ CA*ell^5*E := hFbound
    calc
      _ ≤ (CA*ell^5*E)*χ*(N:ℝ)*(m:ℝ) := by gcongr
      _ = _ := by ring
  have hcore := absolute_final_uniform_attempt_numeric kernels I.fixed S C R hRm
    Ck ζ χ χOut X M E ell CA CQ CT CR Q
    hC hζ hχ hχOut hχX hχOutX hM hE hmLog hCA hCQ hCT hCR hm1 hCTcap hCRrep hQ hAction hcoreEnv
  have hloop := absolute_doubling_fuel_log_bound m hm1 hmLog
  have hcoreLoop : (((Nat.log 2 m+2)*absoluteUniformAttemptWorkCap kernels I.fixed S C R Ck p:ℕ):ℝ) ≤
      4*(1000*(CT+1)*(CR+1)*(2*CQ*CA+202))*X*(N:ℝ)^2*E*ell^13+
        4*(1000*(CT+1)*(CR+1)*(familyFinalCoreConstant+102)*(Ck+1))*(m:ℝ)^p*ell^3 := by
    have hh := mul_le_mul hloop hcore
      (Nat.cast_nonneg (absoluteUniformAttemptWorkCap kernels I.fixed S C R Ck p))
      (show 0 ≤ 4*Real.log (m:ℝ) by linarith)
    push_cast
    convert hh using 1 <;> simp only [ell,p] <;> ring
  have hrows := P.absolute_initial_rows_scale_of_fixed I.seed I.fixed.seed I.fixed_seed_eq hL D c
    hD0 hc hm hmLog hscale hδ g.1
  have hRcoarse : 1 ≤ familyCoarseRowCoefficient D c := by unfold familyCoarseRowCoefficient; linarith
  have hcoarse := family_final_coarse_numeric kernels Ck p (familyCoarseRowCoefficient D c) ell hC hp hRcoarse hmLog hEnv.core
    m (S.levelA 0).1 (S.levelB 0).1 hm1 hrows.1 hrows.2
  have hform := P.sketch_formation_cap_scale I.seed hL D c hD0 hc hm hmLog hscale hδ
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
  have hwork := absolute_family_explicit_work_cap_on_sketch_event kernels I g Ck p hC hp hEnv.core hsketch hsmall
  have hworkR : (absoluteFamilyExplicitWork kernels I g:ℝ) ≤
      (familyFinalRestCap I.seed:ℝ)+6+(((P.depth+1)*2*sketchFormationCap N m P.fixed.sketchFailure:ℕ):ℝ)+
      (coarseSupportWorkCap kernels m (S.levelA 0).1 (S.levelB 0).1:ℝ)+
      (((Nat.log 2 m+2)*absoluteUniformAttemptWorkCap kernels I.fixed S C R Ck p:ℕ):ℝ) := by
    exact_mod_cast hwork
  have hV : 1 ≤ U^2*(N:ℝ)^2*ell^2 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hU) (one_le_pow₀ hN)) (one_le_pow₀ hmLog)
  have hrestSix : (familyFinalRestCap I.seed:ℝ)+6 ≤ 106*U^2*(N:ℝ)^2*ell^2 := by
    nlinarith only [hrest,hV]
  have hmainScale : (N:ℝ)^2*ell^2 ≤ X*(N:ℝ)^2*E*ell^13 := by
    have h1 : ell^2 ≤ ell^13 := pow_le_pow_right₀ hmLog (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hX hE) (show 0 ≤ ell^13 by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans (by simpa only [one_mul,mul_assoc] using h2)) (sq_nonneg (N:ℝ))
    nlinarith only [h3]
  have hpow2 : ell^3 ≤ ell^(3*p+3) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hmLog (show (3:ℝ) ≤ 3*p+3 by linarith)
    change ell^(3:ℝ) ≤ ell^(3*p+3) at hh
    rw [Real.rpow_natCast ell 3] at hh
    exact hh
  have hpow3 : ell^(3*p) ≤ 4*ell^(3*p+3) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hmLog (show 3*p ≤ 3*p+3 by linarith)
    have hp0 : 0 ≤ ell^(3*p+3) := Real.rpow_nonneg (by linarith) _
    linarith
  have hmainC : 0 ≤ 1000*(CT+1)*(CR+1)*(2*CQ*CA+202) := by positivity
  have hcoreC : 0 ≤ 1000*(CT+1)*(CR+1)*(familyFinalCoreConstant+102)*(Ck+1) := by
    have hh : 0 ≤ familyFinalCoreConstant := by unfold familyFinalCoreConstant; positivity
    positivity
  have hcoarseC : 0 ≤ 2*Ck*(2*familyCoarseRowCoefficient D c)^p+11*(Ck+1) := by positivity
  have hcoreGrow := mul_le_mul_of_nonneg_left hpow2
    (show 0 ≤ 4*(1000*(CT+1)*(CR+1)*(familyFinalCoreConstant+102)*(Ck+1))*(m:ℝ)^p by positivity)
  have hcoarseGrow := mul_le_mul_of_nonneg_left hpow3
    (show 0 ≤ (2*Ck*(2*familyCoarseRowCoefficient D c)^p+11*(Ck+1))*(m:ℝ)^p by positivity)
  have hrestGrow := mul_le_mul_of_nonneg_left hmainScale (show 0 ≤ 106*U^2 by positivity)
  have hformGrow := mul_le_mul_of_nonneg_left hmainScale
    (show 0 ≤ 2*(2*D+1)*familySketchFormationCoefficient D c by positivity)
  have hspare : 0 ≤ X*(N:ℝ)^2*E*ell^13 := by positivity
  have hextra : 0 ≤ (3*(2*(2*D+1)*familySketchFormationCoefficient D c)+294*U^2+4)*
      X*(N:ℝ)^2*E*ell^13 := by positivity
  dsimp only [familyFinalMainCoefficient,familyFinalCoreCoefficient] at ⊢
  dsimp only [CT,CR,CA,CQ,U,p,E,ell] at hcoreLoop hcoarse hworkR hrestSix hformation' hmainScale hcoreGrow hcoarseGrow hrestGrow hformGrow hspare hextra ⊢
  nlinarith only [hworkR,hrestSix,hformation',hcoarse,hcoreLoop,hcoreGrow,hcoarseGrow,hrestGrow,hformGrow,hspare,hextra]


end
end HierarchicalAbsoluteSpectral
