import HierarchicalAbsoluteSpectral.CorollaryAbsoluteEnvelope
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalNumeric

/-! Numeric bounds for the actual supremum of absolute-attempt work and
executed Gaussian draws. The attempted rank bound is independent of the
fixed input's seed rank. Constants agree with the main-family comparator
bound; its query-count factor is a harmless upper bound for one attempt. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
variable {N m r L : ℕ}

theorem absolute_final_fixed_attempt_numeric
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem N m N r L) (S : StoredSketches N m N L) (C : MainSupportData S)
    (R : ℕ) (hRm : R ≤ m)
    (Ck ζ χ χOut X M E ell CA CQ CT CR : ℝ) (Q : ℕ)
    (hC : 0 < Ck) (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hM : 1 ≤ M)
    (hE : 1 ≤ E) (hell : 1 ≤ ell) (hCA : 0 ≤ CA) (hCQ : 0 ≤ CQ)
    (hCT : 0 ≤ CT) (hCR : 0 ≤ CR) (hm : 1 ≤ m)
    (hmetaT : (I.queryCap:ℝ) ≤ CT*ell) (hmetaR : (I.repetitions:ℝ) ≤ CR*ell)
    (hQ : (Q:ℝ)+1 ≤ CQ*((N:ℝ)/m)*ell^5)
    (hAction : M ≤ CA*E*χ*(N:ℝ)*(m:ℝ)*ell^5)
    (henv : AbsoluteAttemptEnvelope kernels I S C Ck (9/4+ζ) R ⌈M⌉₊
      (familyFinalCoreCharge Ck ζ m) (familyFinalOutputCharge χ χOut Ck ζ N m) Q) :
    ((Finset.univ.sup (fun s : Fin (R+1) =>
      absoluteAttemptWorkCap kernels I S C s.val Ck (9/4+ζ)+
        I.repetitions*((s.val+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s.val*C.pair.dimension) : ℕ):ℝ) ≤
      1000*(CT+1)*(CR+1)*(2*CQ*CA+202)*X*(N:ℝ)^2*E*ell^12+
        1000*(CT+1)*(CR+1)*(familyFinalCoreConstant+102)*(Ck+1)*(m:ℝ)^(9/4+ζ)*ell^2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hNm : (m:ℝ) ≤ N := by exact_mod_cast I.core_le_rows
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hX : 0 ≤ X := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hell0 : 0 ≤ ell := by linarith
  have hχ0 : 0 ≤ χ := by linarith
  have hCT1 : 0 ≤ CT+1 := by linarith
  have hCR1 : 0 ≤ CR+1 := by linarith
  obtain ⟨hA,hB,hO⟩ := family_final_charge_bounds Ck ζ χ χOut M hC hζ hχ hχOut hM hm I.core_le_rows
  have hT : (I.queryCap:ℝ)+1 ≤ (CT+1)*ell := by nlinarith
  have hR : (I.repetitions:ℝ)+1 ≤ (CR+1)*ell := by nlinarith
  have hcore : Finset.univ.sup (fun s : Fin (R+1) =>
      absoluteAttemptWorkCap kernels I S C s.val Ck (9/4+ζ)+
        I.repetitions*((s.val+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s.val*C.pair.dimension) ≤
      1000*(I.queryCap+1)*(I.repetitions+1)*
        ((Q+1)*⌈M⌉₊+familyFinalCoreCharge Ck ζ m+familyFinalOutputCharge χ χOut Ck ζ N m) := by
    apply Finset.sup_le
    intro s _
    have hh := henv.attempt_work_with_draws kernels I S C Ck (9/4+ζ) R ⌈M⌉₊
      (familyFinalCoreCharge Ck ζ m) (familyFinalOutputCharge χ χOut Ck ζ N m) Q s.val (by omega)
    apply hh.trans
    calc
      _ ≤ (I.queryCap+1)*(1000*(I.repetitions+1)*
          ((Q+1)*⌈M⌉₊+familyFinalCoreCharge Ck ζ m+familyFinalOutputCharge χ χOut Ck ζ N m)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ = _ := by ring
  have hproduct := mul_le_mul hQ hA (Nat.cast_nonneg _) (by positivity : 0 ≤ CQ*((N:ℝ)/m)*ell^5)
  have hproduct' := mul_le_mul_of_nonneg_left hAction
    (show 0 ≤ 2*CQ*((N:ℝ)/m)*ell^5 by positivity)
  have he : (2*CQ*((N:ℝ)/m)*ell^5)*(CA*E*χ*(N:ℝ)*(m:ℝ)*ell^5) =
      2*CQ*CA*χ*(N:ℝ)^2*E*ell^10 := by field_simp [hm0.ne'] <;> ring
  rw [he] at hproduct'
  have hdegree : ((Q:ℝ)+1)*(⌈M⌉₊:ℝ) ≤ 2*CQ*CA*X*(N:ℝ)^2*E*ell^10 := by
    calc
      _ ≤ (CQ*((N:ℝ)/m)*ell^5)*(2*M) := hproduct
      _ = (2*CQ*((N:ℝ)/m)*ell^5)*M := by ring
      _ ≤ 2*CQ*CA*χ*(N:ℝ)^2*E*ell^10 := hproduct'
      _ ≤ _ := by gcongr
  have hinput : χ*(N:ℝ)*(m:ℝ) ≤ X*(N:ℝ)^2 := by
    calc
      _ ≤ χ*(N:ℝ)*(N:ℝ) := mul_le_mul_of_nonneg_left hNm (by positivity)
      _ = χ*(N:ℝ)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hχX (sq_nonneg _)
  have houtput : (N:ℝ)^2*χOut ≤ X*(N:ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_right hχOutX (sq_nonneg (N:ℝ))]
  have hlarge : 1 ≤ E*ell^10 := one_le_mul_of_one_le_of_one_le hE (one_le_pow₀ hell)
  have hrest : 101*(χ*(N:ℝ)*(m:ℝ)+(N:ℝ)^2*χOut) ≤
      202*X*(N:ℝ)^2*E*ell^10 := by
    have hh := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 202*X*(N:ℝ)^2 by positivity)
    nlinarith only [hinput,houtput,hh]
  have hsum : ((Q:ℝ)+1)*(⌈M⌉₊:ℝ)+(familyFinalCoreCharge Ck ζ m:ℝ)+
      (familyFinalOutputCharge χ χOut Ck ζ N m:ℝ) ≤
      (2*CQ*CA+202)*X*(N:ℝ)^2*E*ell^10+
        (familyFinalCoreConstant+102)*(Ck+1)*(m:ℝ)^(9/4+ζ) := by
    nlinarith only [hdegree,hB,hO,hrest]
  have houter := mul_le_mul hT hR (by positivity : (0:ℝ) ≤ (I.repetitions:ℝ)+1) (by positivity : 0 ≤ (CT+1)*ell)
  have htotal := mul_le_mul (mul_le_mul_of_nonneg_left houter (by norm_num : (0:ℝ) ≤ 1000)) hsum
    (by positivity : 0 ≤ ((Q:ℝ)+1)*(⌈M⌉₊:ℝ)+(familyFinalCoreCharge Ck ζ m:ℝ)+
      (familyFinalOutputCharge χ χOut Ck ζ N m:ℝ)) (by positivity : 0 ≤ 1000*((CT+1)*ell*((CR+1)*ell)))
  have hcoreR : ((Finset.univ.sup (fun s : Fin (R+1) =>
      absoluteAttemptWorkCap kernels I S C s.val Ck (9/4+ζ)+
        I.repetitions*((s.val+1)*C.pair.dimension+2*C.pair.dimension*C.pair.dimension)+s.val*C.pair.dimension) : ℕ):ℝ) ≤
      1000*((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1)*
        (((Q:ℝ)+1)*(⌈M⌉₊:ℝ)+(familyFinalCoreCharge Ck ζ m:ℝ)+
          (familyFinalOutputCharge χ χOut Ck ζ N m:ℝ)) := by exact_mod_cast hcore
  apply hcoreR.trans
  calc
    _ = 1000*(((I.queryCap:ℝ)+1)*((I.repetitions:ℝ)+1))*
        (((Q:ℝ)+1)*(⌈M⌉₊:ℝ)+(familyFinalCoreCharge Ck ζ m:ℝ)+
          (familyFinalOutputCharge χ χOut Ck ζ N m:ℝ)) := by ring
    _ ≤ 1000*((CT+1)*ell*((CR+1)*ell))*
        ((2*CQ*CA+202)*X*(N:ℝ)^2*E*ell^10+
          (familyFinalCoreConstant+102)*(Ck+1)*(m:ℝ)^(9/4+ζ)) := htotal
    _ = _ := by ring


/-- Numeric bound for the exact absolute-program attempt supremum,
including executed Gaussian draws. Every cost input is a component of the
constructed attempt envelope, not a hypothesis of the final cost bound. -/
theorem absolute_final_uniform_attempt_numeric
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : AbsoluteProblem N m N L) (S : StoredSketches N m N L) (C : MainSupportData S)
    (R : ℕ) (hRm : R ≤ m)
    (Ck ζ χ χOut X M E ell CA CQ CT CR : ℝ) (Q : ℕ)
    (hC : 0 < Ck) (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hM : 1 ≤ M)
    (hE : 1 ≤ E) (hell : 1 ≤ ell) (hCA : 0 ≤ CA) (hCQ : 0 ≤ CQ)
    (hCT : 0 ≤ CT) (hCR : 0 ≤ CR) (hm : 1 ≤ m)
    (hmetaT : (I.seed.queryCap:ℝ) ≤ CT*ell) (hmetaR : (I.seed.repetitions:ℝ) ≤ CR*ell)
    (hQ : (Q:ℝ)+1 ≤ CQ*((N:ℝ)/m)*ell^5)
    (hAction : M ≤ CA*E*χ*(N:ℝ)*(m:ℝ)*ell^5)
    (henv : AbsoluteAttemptEnvelope kernels I.seed S C Ck (9/4+ζ) R ⌈M⌉₊
      (familyFinalCoreCharge Ck ζ m) (familyFinalOutputCharge χ χOut Ck ζ N m) Q) :
    (absoluteUniformAttemptWorkCap kernels I S C R Ck (9/4+ζ):ℝ) ≤
      1000*(CT+1)*(CR+1)*(2*CQ*CA+202)*X*(N:ℝ)^2*E*ell^12+
        1000*(CT+1)*(CR+1)*(familyFinalCoreConstant+102)*(Ck+1)*(m:ℝ)^(9/4+ζ)*ell^2 := by
  simpa only [absoluteUniformAttemptWorkCap] using
    absolute_final_fixed_attempt_numeric kernels I.seed S C R hRm
      Ck ζ χ χOut X M E ell CA CQ CT CR Q hC hζ hχ hχOut hχX hχOutX hM hE hell
      hCA hCQ hCT hCR hm hmetaT hmetaR hQ hAction henv

end
end HierarchicalAbsoluteSpectral
