import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalSix
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalProgram

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
variable {N m r L : ℕ}

theorem family_final_charge_bounds (C ζ χ χOut M : ℝ) (hC : 0 < C)
    (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut) (hM : 1 ≤ M)
    (hm : 1 ≤ m) (hNm : m ≤ N) :
    (⌈M⌉₊:ℝ) ≤ 2*M ∧
      (familyFinalCoreCharge C ζ m:ℝ) ≤
        (familyFinalCoreConstant+1)*(C+1)*(m:ℝ)^(9/4+ζ) ∧
      (familyFinalOutputCharge χ χOut C ζ N m:ℝ) ≤
        101*(χ*(N:ℝ)*(m:ℝ)+(C+1)*(m:ℝ)^(9/4+ζ)+(N:ℝ)^2*χOut) := by
  let Y := (C+1)*(m:ℝ)^(9/4+ζ)
  let V := χ*(N:ℝ)*(m:ℝ)+Y+(N:ℝ)^2*χOut
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hm.trans hNm
  have hY : 1 ≤ Y := by
    have hp := Real.one_le_rpow hmR (show 0 ≤ (9:ℝ)/4+ζ by linarith)
    have hh := mul_le_mul (show (1:ℝ) ≤ C+1 by linarith) hp (by norm_num : (0:ℝ) ≤ 1)
      (show 0 ≤ C+1 by linarith)
    simpa only [one_mul,Y] using hh
  have hV : 1 ≤ V := by
    have hinput : 0 ≤ χ*(N:ℝ)*(m:ℝ) := by positivity
    have houtput : 0 ≤ (N:ℝ)^2*χOut := by positivity
    dsimp [V]
    linarith
  have hM0 : 0 ≤ M := by linarith
  have hB0 : 0 ≤ familyFinalCoreConstant*Y := by
    unfold familyFinalCoreConstant
    positivity
  have hO0 : 0 ≤ 100*V := by positivity
  have hA := (Nat.ceil_lt_add_one hM0).le
  have hB := (Nat.ceil_lt_add_one hB0).le
  have hO := (Nat.ceil_lt_add_one hO0).le
  refine ⟨by linarith,?_,?_⟩
  · change (⌈familyFinalCoreConstant*(C+1)*(m:ℝ)^(9/4+ζ)⌉₊:ℝ) ≤ _
    have he : familyFinalCoreConstant*(C+1)*(m:ℝ)^(9/4+ζ) = familyFinalCoreConstant*Y := by dsimp [Y]; ring
    rw [he]
    dsimp [Y] at hY hB ⊢
    nlinarith
  · change (⌈100*(χ*(N:ℝ)*(m:ℝ)+(C+1)*(m:ℝ)^(9/4+ζ)+(N:ℝ)^2*χOut)⌉₊:ℝ) ≤ _
    change (⌈100*V⌉₊:ℝ) ≤ 101*V
    linarith

theorem family_final_core_numeric
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (I : FixedProblem N m N r L) (S : StoredSketches N m N L) (C : MainSupportData S)
    (Ck ζ χ χOut X M E ell CA CQ CT CR : ℝ) (Q : ℕ)
    (hC : 0 < Ck) (hζ : 0 < ζ) (hχ : 1 ≤ χ) (hχOut : 1 ≤ χOut)
    (hχX : χ ≤ X) (hχOutX : χOut ≤ X) (hM : 1 ≤ M)
    (hE : 1 ≤ E) (hell : 1 ≤ ell) (hCA : 0 ≤ CA) (hCQ : 0 ≤ CQ)
    (hCT : 0 ≤ CT) (hCR : 0 ≤ CR) (hm : 1 ≤ m)
    (hmetaT : (I.queryCap:ℝ) ≤ CT*ell) (hmetaR : (I.repetitions:ℝ) ≤ CR*ell)
    (hQ : (Q:ℝ)+1 ≤ CQ*((N:ℝ)/m)*ell^5)
    (hAction : M ≤ CA*E*χ*(N:ℝ)*(m:ℝ)*ell^5)
    (henv : ComparatorCoreEnvelope kernels I S C Ck (9/4+ζ) ⌈M⌉₊
      (familyFinalCoreCharge Ck ζ m) (familyFinalOutputCharge χ χOut Ck ζ N m) Q) :
    (mainCoreWorkCap kernels I S C Ck (9/4+ζ):ℝ) ≤
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
  have hcore := ComparatorCoreEnvelope.core_work kernels I S C Ck (9/4+ζ) ⌈M⌉₊
    (familyFinalCoreCharge Ck ζ m) (familyFinalOutputCharge χ χOut Ck ζ N m) Q henv
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
  have hcoreR : (mainCoreWorkCap kernels I S C Ck (9/4+ζ):ℝ) ≤
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

end
end HierarchicalAbsoluteSpectral
