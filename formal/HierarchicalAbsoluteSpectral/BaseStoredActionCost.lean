import HierarchicalAbsoluteSpectral.BaseStoredActions
import HierarchicalAbsoluteSpectral.CoarseAlgebraHierarchyKernels

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
variable {k m b s t N : ℕ}

theorem storedCongruenceGramAction_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η ζ C : ℝ) (hC : 0 ≤ C)
    (hEnv : HierarchyKernelEnvelopes κ η ζ N m kernels C)
    (F : Matrix (Fin s) (Fin m) ℝ) (L : Matrix (Fin m) (Fin k) ℝ)
    (hk : k ≤ m) (hb : b ≤ Matmul.RectangularPrograms.width κ m) :
    ((storedCongruenceGramAction (b:=b) kernels F L).cost:ℝ) ≤
      6*C*(s+m:ℕ)*(m:ℝ)^(1+η) := by
  have h1 := hEnv.stored_forward k m b le_rfl hb
  have h2 := hEnv.stored_adjoint m s b le_rfl hb
  have h3 := hEnv.stored_forward s m b le_rfl hb
  have h4 := hEnv.stored_forward m k b hk hb
  have hkR : (k:ℝ) ≤ m := by exact_mod_cast hk
  have hP : 0 ≤ (m:ℝ)^(1+η) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [storedCongruenceGramAction_cost,Nat.cast_add,Nat.cast_add,Nat.cast_add]
  push_cast at h1 h2 h3 h4 ⊢
  nlinarith [mul_nonneg (mul_nonneg hC hP) (sub_nonneg.mpr hkR),
    mul_nonneg (mul_nonneg hC hP) (Nat.cast_nonneg s)]

theorem dyadicStoppingLevel_le_neumannCount (ε : ℝ) (hε : 0 < ε) :
    dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε ≤ neumannCount ε hε := by
  have hh (q : ℕ) : q ≤ 2^q := by
    induction q with
    | zero => norm_num
    | succ q ih =>
      have hp : 1 ≤ 2^q := Nat.one_le_two_pow
      rw [pow_succ]
      omega
  exact hh _

theorem storedFinePencilAction_cost_neumann_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (L : Matrix (Fin m) (Fin k) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (t0 ε : ℝ) (hε : 0 < ε) :
    (storedFinePencilAction (b:=b) kernels HA HB L U t0 ε hε).cost ≤
      8*neumannCount ε hε*((storedCongruenceGramAction (b:=b) kernels HA U).cost+
        (storedCongruenceGramAction (b:=b) kernels HB L).cost+k*b+1) := by
  have hs := dyadicStoppingLevel_le_neumannCount ε hε
  have hq : 1 ≤ neumannCount ε hε := Nat.one_le_two_pow
  have he : (storedFinePencilAction (b:=b) kernels HA HB L U t0 ε hε).cost =
      2*dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε+1+
      2*neumannCount ε hε*((storedCongruenceGramAction (b:=b) kernels HA U).cost+2*k*b)+
      (storedCongruenceGramAction (b:=b) kernels HB L).cost+2*k*b := by
    rw [storedFinePencilAction_cost,storedCongruenceGramAction_cost,storedCongruenceGramAction_cost]
  rw [he]
  nlinarith [Nat.mul_le_mul_right (storedCongruenceGramAction (b:=b) kernels HB L).cost hq,
    Nat.mul_le_mul_right (k*b) hq]

theorem storedFinePencilAction_cost_log_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (L : Matrix (Fin m) (Fin k) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (t0 ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((storedFinePencilAction (b:=b) kernels HA HB L U t0 ε hε).cost:ℝ) ≤
      8*(1+4*Real.log (1/ε))*
        (((storedCongruenceGramAction (b:=b) kernels HA U).cost:ℝ)+
          (storedCongruenceGramAction (b:=b) kernels HB L).cost+(k:ℝ)*b+1) := by
  have hcost : ((storedFinePencilAction (b:=b) kernels HA HB L U t0 ε hε).cost:ℝ) ≤
      8*(neumannCount ε hε:ℝ)*
        (((storedCongruenceGramAction (b:=b) kernels HA U).cost:ℝ)+
          (storedCongruenceGramAction (b:=b) kernels HB L).cost+(k:ℝ)*b+1) := by
    exact_mod_cast storedFinePencilAction_cost_neumann_bound (b:=b) kernels HA HB L U t0 ε hε
  apply hcost.trans
  gcongr
  exact neumannCount_bound ε hε hε1

theorem storedFinePencilAction_cost_row_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η ζ C : ℝ) (hκ : κ ≤ 1) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hEnv : HierarchyKernelEnvelopes κ η ζ N m kernels C)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (L : Matrix (Fin m) (Fin k) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (t0 ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hm : 1 ≤ m) (hk : k ≤ m) (hb : b ≤ Matmul.RectangularPrograms.width κ m) :
    ((storedFinePencilAction (b:=b) kernels HA HB L U t0 ε hε).cost:ℝ) ≤
      128*(C+1)*(1+4*Real.log (1/ε))*(s+t+m:ℕ)*(m:ℝ)^(1+η) := by
  let P := (m:ℝ)^(1+η)
  let E := (s+t+m:ℕ)*P
  have hGL := storedCongruenceGramAction_work_bound kernels κ η ζ C hC hEnv HA U hk hb
  have hGQ := storedCongruenceGramAction_work_bound kernels κ η ζ C hC hEnv HB L hk hb
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hkr : (k:ℝ) ≤ m := by exact_mod_cast hk
  have hbr : (b:ℝ) ≤ m := by exact_mod_cast hb.trans (rectangular_width_le_self κ hκ m hm)
  have hP : (m:ℝ) ≤ P := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hmr (show (1:ℝ) ≤ 1+η by linarith)
  have hP0 : 0 ≤ P := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hmE : (m:ℝ)*P ≤ E := by
    apply mul_le_mul_of_nonneg_right _ hP0
    exact_mod_cast (show m ≤ s+t+m by omega)
  have hkb : (k:ℝ)*b+1 ≤ 2*E := by
    have hp := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg m)
    have hprod := mul_le_mul hkr hbr (Nat.cast_nonneg b) (Nat.cast_nonneg m)
    nlinarith
  have hraw : ((storedCongruenceGramAction (b:=b) kernels HA U).cost:ℝ)+
      (storedCongruenceGramAction (b:=b) kernels HB L).cost ≤ 12*C*E := by
    have hextra : 0 ≤ C*(s+t:ℕ)*P := by positivity
    dsimp [E,P] at hextra ⊢
    push_cast at hGL hGQ hextra ⊢
    nlinarith
  have hsum : ((storedCongruenceGramAction (b:=b) kernels HA U).cost:ℝ)+
      (storedCongruenceGramAction (b:=b) kernels HB L).cost+(k:ℝ)*b+1 ≤ 16*(C+1)*E := by
    nlinarith [mul_nonneg hC hE0]
  have hlog : 0 ≤ 1+4*Real.log (1/ε) := by
    have hh : 1 ≤ 1/ε := (le_div_iff₀ hε).mpr (by linarith)
    have hl := Real.log_nonneg hh
    linarith
  calc
    _ ≤ 8*(1+4*Real.log (1/ε))*
        (((storedCongruenceGramAction (b:=b) kernels HA U).cost:ℝ)+
          (storedCongruenceGramAction (b:=b) kernels HB L).cost+(k:ℝ)*b+1) :=
      storedFinePencilAction_cost_log_bound kernels HA HB L U t0 ε hε hε1
    _ ≤ 8*(1+4*Real.log (1/ε))*(16*(C+1)*E) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [E,P]; ring

end
end HierarchicalAbsoluteSpectral
