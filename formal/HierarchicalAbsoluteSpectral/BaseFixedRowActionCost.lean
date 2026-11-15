import HierarchicalAbsoluteSpectral.BaseStoredActionCost
import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedKernelFamily

/-! Fixed-row envelopes for the literal stored-factor actions. Row counts
may vanish. The fine-action estimates include the executed Neumann-degree
search and all scalar block operations. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Matmul.RectangularPrograms
variable {m k b s t : ℕ}

theorem fixedRowKernelEnvelopes_four_orientations
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((kernels s k b).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) ∧
    ((kernels k s b).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) ∧
    ((kernels b k s).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) ∧
    ((kernels b s k).cost:ℝ) ≤ 8*χ*(s+m:ℕ)*(m:ℝ) :=
  ⟨hrow.forward s k b hk hb,hrow.adjoint k s b hk hb,
    hrow.transpose_forward b k s hb hk,hrow.transpose_adjoint b s k hb hk⟩

theorem storedCongruenceGramAction_cost_fixed_row_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (F : Matrix (Fin s) (Fin m) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((storedCongruenceGramAction (b:=b) kernels F U).cost:ℝ) ≤
      64*χ*(s+m:ℕ)*(m:ℝ) := by
  have h1 := hrow.forward k m b le_rfl hb
  have h2 := hrow.adjoint m s b le_rfl hb
  have h3 := hrow.forward s m b le_rfl hb
  have h4 := hrow.forward m k b hk hb
  have hkm : (k:ℝ) ≤ m := by exact_mod_cast hk
  have hp : 0 ≤ χ*(m:ℝ) := by positivity
  rw [storedCongruenceGramAction_cost]
  push_cast at h1 h2 h3 h4 ⊢
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hkm),
    mul_nonneg hp (Nat.cast_nonneg s),mul_nonneg hp (Nat.cast_nonneg m)]

/-- The scalar block cost can be absorbed even when the stored sketch has
zero rows. Positive core size is needed to absorb the constant operation. -/
theorem fixedRow_scalar_cost_bound
    (χ : ℝ) (hχ : 1 ≤ χ) (hm : 1 ≤ m) (hk : k ≤ m)
    (hb : b ≤ 2*width (1/2) m) :
    1 ≤ χ*(s+m:ℕ)*(m:ℝ) ∧
      (k:ℝ)*b+1 ≤ 3*χ*(s+m:ℕ)*(m:ℝ) := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hsm : (m:ℝ) ≤ (s+m:ℕ) := by exact_mod_cast (show m ≤ s+m by omega)
  have hs1 : (1:ℝ) ≤ (s+m:ℕ) := hm1.trans hsm
  have hkR : (k:ℝ) ≤ m := by exact_mod_cast hk
  have hb' : b ≤ 2*m := hb.trans (Nat.mul_le_mul_left 2 (half_width_le m hm))
  have hbR : (b:ℝ) ≤ 2*m := by exact_mod_cast hb'
  have hA1 : 1 ≤ χ*(s+m:ℕ)*(m:ℝ) := by
    have hχs : (1:ℝ) ≤ χ*(s+m:ℕ) := by
      nlinarith [mul_le_mul hχ hs1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ χ)]
    simpa only [one_mul] using mul_le_mul hχs hm1
      (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ χ*(s+m:ℕ))
  have hkb : (k:ℝ)*b ≤ 2*χ*(s+m:ℕ)*(m:ℝ) := by
    have h1 := mul_le_mul hkR hbR (Nat.cast_nonneg b) (Nat.cast_nonneg m)
    have h2 := mul_le_mul_of_nonneg_right hsm (Nat.cast_nonneg m)
    have h3 := mul_le_mul_of_nonneg_right hχ
      (mul_nonneg (Nat.cast_nonneg (s+m)) (Nat.cast_nonneg m))
    nlinarith
  exact ⟨hA1,by linarith⟩

theorem storedFinePencilAction_cost_fixed_row_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (U V : Matrix (Fin m) (Fin k) ℝ) (tau ε : ℝ) (hε : 0 < ε)
    (hm : 1 ≤ m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((storedFinePencilAction (b:=b) kernels HA HB U V tau ε hε).cost:ℝ) ≤
      2048*(neumannCount ε hε:ℝ)*χ*(s+t+m:ℕ)*(m:ℝ) := by
  let A : ℝ := χ*(s+t+m:ℕ)*(m:ℝ)
  have hscalar := fixedRow_scalar_cost_bound (s:=s+t) χ hχ hm hk hb
  have hA1 : 1 ≤ A := hscalar.1
  have hkb : (k:ℝ)*b+1 ≤ 3*A := by simpa only [A,mul_assoc] using hscalar.2
  have hGA := storedCongruenceGramAction_cost_fixed_row_bound kernels χ hχ hrow HA V hk hb
  have hGB := storedCongruenceGramAction_cost_fixed_row_bound kernels χ hχ hrow HB U hk hb
  have hGA' : ((storedCongruenceGramAction (b:=b) kernels HA V).cost:ℝ) ≤ 64*A := by
    apply hGA.trans
    dsimp [A]
    have hst : ((s+m:ℕ):ℝ) ≤ (s+t+m:ℕ) := by
      exact_mod_cast (show s+m ≤ s+t+m by omega)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hst (by positivity)) (Nat.cast_nonneg m)
    nlinarith only [hh]
  have hGB' : ((storedCongruenceGramAction (b:=b) kernels HB U).cost:ℝ) ≤ 64*A := by
    apply hGB.trans
    dsimp [A]
    have hst : ((t+m:ℕ):ℝ) ≤ (s+t+m:ℕ) := by
      exact_mod_cast (show t+m ≤ s+t+m by omega)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hst (by positivity)) (Nat.cast_nonneg m)
    nlinarith only [hh]
  have hsum : ((storedCongruenceGramAction (b:=b) kernels HA V).cost:ℝ)+
      (storedCongruenceGramAction (b:=b) kernels HB U).cost+(k:ℝ)*b+1 ≤ 256*A := by
    linarith
  have hraw : ((storedFinePencilAction (b:=b) kernels HA HB U V tau ε hε).cost:ℝ) ≤
      8*(neumannCount ε hε:ℝ)*
        (((storedCongruenceGramAction (b:=b) kernels HA V).cost:ℝ)+
          (storedCongruenceGramAction (b:=b) kernels HB U).cost+(k:ℝ)*b+1) := by
    exact_mod_cast storedFinePencilAction_cost_neumann_bound (b:=b) kernels HA HB U V tau ε hε
  calc
    _ ≤ 8*(neumannCount ε hε:ℝ)*(256*A) :=
      hraw.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by dsimp [A]; ring

theorem storedFinePencilAction_cost_fixed_row_log_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (U V : Matrix (Fin m) (Fin k) ℝ) (tau ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hm : 1 ≤ m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((storedFinePencilAction (b:=b) kernels HA HB U V tau ε hε).cost:ℝ) ≤
      2048*(1+4*Real.log (1/ε))*χ*(s+t+m:ℕ)*(m:ℝ) := by
  apply (storedFinePencilAction_cost_fixed_row_bound kernels χ hχ hrow HA HB U V tau ε hε hm hk hb).trans
  gcongr
  exact neumannCount_bound ε hε hε1

/-- The complete leaf of the action recurrence, including its additional
scalar block cost. -/
theorem storedFinePencilAction_cost_fixed_row_leaf_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (U V : Matrix (Fin m) (Fin k) ℝ) (tau ε : ℝ) (hε : 0 < ε)
    (hm : 1 ≤ m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((storedFinePencilAction (b:=b) kernels HA HB U V tau ε hε).cost:ℝ)+(k:ℝ)*b+1 ≤
      4096*(neumannCount ε hε:ℝ)*χ*(s+t+m:ℕ)*(m:ℝ) := by
  have hc := storedFinePencilAction_cost_fixed_row_bound kernels χ hχ hrow HA HB U V tau ε hε hm hk hb
  have hs := (fixedRow_scalar_cost_bound (s:=s+t) χ hχ hm hk hb).2
  have hq : (1:ℝ) ≤ neumannCount ε hε := by exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2^dyadicStoppingLevel (1/2) ε (by norm_num) (by norm_num) hε)
  have hA : 0 ≤ χ*(s+t+m:ℕ)*(m:ℝ) := by positivity
  have hqa := mul_le_mul_of_nonneg_right hq hA
  nlinarith

theorem storedFinePencilAction_cost_fixed_row_leaf_log_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (U V : Matrix (Fin m) (Fin k) ℝ) (tau ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hm : 1 ≤ m) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((storedFinePencilAction (b:=b) kernels HA HB U V tau ε hε).cost:ℝ)+(k:ℝ)*b+1 ≤
      4096*(1+4*Real.log (1/ε))*χ*(s+t+m:ℕ)*(m:ℝ) := by
  apply (storedFinePencilAction_cost_fixed_row_leaf_bound kernels χ hχ hrow HA HB U V tau ε hε hm hk hb).trans
  gcongr
  exact neumannCount_bound ε hε hε1

end
end HierarchicalAbsoluteSpectral
