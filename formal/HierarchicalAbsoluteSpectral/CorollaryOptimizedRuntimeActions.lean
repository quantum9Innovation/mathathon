import HierarchicalAbsoluteSpectral.CoarseAlgebraFixedKernelFamily
import HierarchicalAbsoluteSpectral.BaseStoredActionCost

/-! Input-optimal counted actions for the constant-distortion comparators.
These estimates use the actual finite circuit envelopes in all four
orientations, including growing block width r+1. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Matmul.RectangularPrograms
variable {N m k b s t : ℕ}

theorem comparator_stored_gram_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (F : Matrix (Fin s) (Fin m) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (hNm : m ≤ N) (hs : s ≤ N) (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((storedCongruenceGramAction (b:=b) kernels F U).cost:ℝ) ≤ 64*χ*(N:ℝ)*(m:ℝ) := by
  have h1 := hrow.forward k m b le_rfl hb
  have h2 := hrow.adjoint m s b le_rfl hb
  have h3 := hrow.forward s m b le_rfl hb
  have h4 := hrow.forward m k b hk hb
  have hkN : (k:ℝ) ≤ N := by exact_mod_cast hk.trans hNm
  have hmN : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hsN : (s:ℝ) ≤ N := by exact_mod_cast hs
  have hp : 0 ≤ χ*(m:ℝ) := by positivity
  rw [storedCongruenceGramAction_cost]
  push_cast at h1 h2 h3 h4 ⊢
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hkN),
    mul_nonneg hp (sub_nonneg.mpr hmN),mul_nonneg hp (sub_nonneg.mpr hsN)]

theorem comparator_stored_pencil_cost
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (χ : ℝ) (hχ : 1 ≤ χ)
    (hrow : FixedRowKernelEnvelopes m kernels χ)
    (HA : Matrix (Fin s) (Fin m) ℝ) (HB : Matrix (Fin t) (Fin m) ℝ)
    (U V : Matrix (Fin m) (Fin k) ℝ) (tau epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hm : 1 ≤ m) (hNm : m ≤ N) (hs : s ≤ N) (ht : t ≤ N)
    (hk : k ≤ m) (hb : b ≤ 2*width (1/2) m) :
    ((storedFinePencilAction (b:=b) kernels HA HB U V tau epsilon hepsilon).cost:ℝ) ≤
      2048*(neumannCount epsilon hepsilon:ℝ)*χ*(N:ℝ)*(m:ℝ) := by
  let A : ℝ := χ*(N:ℝ)*(m:ℝ)
  have hA1 : 1 ≤ A := by
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hm.trans hNm
    dsimp [A]
    have hχN : (1:ℝ) ≤ χ*(N:ℝ) := by
      nlinarith [mul_le_mul hχ hN1 (by positivity) (by positivity)]
    exact (by simpa only [one_mul] using
      mul_le_mul hχN hm1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ χ*(N:ℝ)))
  have hGA := comparator_stored_gram_cost kernels χ hχ hrow HA V hNm hs hk hb
  have hGB := comparator_stored_gram_cost kernels χ hχ hrow HB U hNm ht hk hb
  have hb' : b ≤ 2*m := Nat.le_trans hb (Nat.mul_le_mul_left 2 (half_width_le m hm))
  have hkR : (k:ℝ) ≤ m := by exact_mod_cast hk
  have hbR : (b:ℝ) ≤ 2*m := by exact_mod_cast hb'
  have hmN : (m:ℝ) ≤ N := by exact_mod_cast hNm
  have hkb : (k:ℝ)*b ≤ 2*A := by
    have h1 := mul_le_mul hkR hbR (Nat.cast_nonneg b) (Nat.cast_nonneg m)
    have h2 := mul_le_mul_of_nonneg_right hmN (Nat.cast_nonneg m)
    have h3 := mul_le_mul_of_nonneg_right hχ
      (mul_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg m))
    dsimp [A]
    nlinarith
  have hsum : ((storedCongruenceGramAction (b:=b) kernels HA V).cost:ℝ)+
      (storedCongruenceGramAction (b:=b) kernels HB U).cost+(k:ℝ)*b+1 ≤ 256*A := by
    dsimp [A] at hA1 hkb ⊢
    nlinarith
  have hraw : ((storedFinePencilAction (b:=b) kernels HA HB U V tau epsilon hepsilon).cost:ℝ) ≤
      8*(neumannCount epsilon hepsilon:ℝ)*
        (((storedCongruenceGramAction (b:=b) kernels HA V).cost:ℝ)+
          (storedCongruenceGramAction (b:=b) kernels HB U).cost+(k:ℝ)*b+1) := by
    exact_mod_cast storedFinePencilAction_cost_neumann_bound (b:=b) kernels HA HB U V tau epsilon hepsilon
  have htotal := hraw.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  calc
    _ ≤ 8*(neumannCount epsilon hepsilon:ℝ)*(256*A) := htotal
    _ = _ := by dsimp [A]; ring

end
end HierarchicalAbsoluteSpectral
