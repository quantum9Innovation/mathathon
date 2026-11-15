import HierarchicalAbsoluteSpectral.DyadicDCT
import HierarchicalAbsoluteSpectral.RadixTwoDFT

/-! The cosine-transform coefficients are obtained from one length-4n
Fourier transform with an explicitly padded input. All roots used by this
identity are the nested-square-root numbers defined in `DyadicNodes`.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Chebyshev Finset Complex
open scoped ComplexConjugate

theorem dyadicRoot_isDyadicRoot (s : ℕ) : IsDyadicRoot (dyadicRoot s) (s+2) := by
  change (dyadicRoot s)^(2^(s+1)) = -1
  rw [dyadicRoot_eq_exp, ← Complex.exp_nat_mul]
  have heq : ((2^(s+1) : ℕ) : ℂ)*
      (((Real.pi/(2:ℝ)^(s+1) : ℝ) : ℂ)*I) = Real.pi*I := by
    push_cast
    field_simp
  rw [heq, Complex.exp_pi_mul_I]

theorem dyadicRoot_norm (s : ℕ) : ‖dyadicRoot s‖ = 1 := by
  rw [dyadicRoot_eq_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, Real.exp_zero]

theorem dyadicRoot_pow_order (s : ℕ) : (dyadicRoot s)^(4*2^s) = 1 := by
  have h := dyadicRoot_isDyadicRoot s
  change (dyadicRoot s)^(2^(s+1)) = -1 at h
  have heq : 4*2^s = 2^(s+1)*2 := by rw [pow_succ]; ring
  rw [heq, pow_mul, h]
  norm_num

theorem dyadicRoot_power_re (s j k : ℕ) :
    ((dyadicRoot s)^((2*j+1)*k)).re = (T ℝ (k : ℤ)).eval (dyadicNode s j) := by
  rw [chebyshev_at_dyadic_node, dyadicRoot_eq_exp, ← Complex.exp_nat_mul]
  have heq : (((2*j+1)*k : ℕ) : ℂ)*
      (((Real.pi/(2:ℝ)^(s+1) : ℝ) : ℂ)*I) =
      (((k : ℝ)*dyadicAngle s j : ℝ) : ℂ)*I := by
    unfold dyadicAngle
    push_cast
    rw [pow_succ]
    field_simp
  rw [heq, Complex.exp_ofReal_mul_I_re]

theorem unit_root_reflection (N a : ℕ) (w : ℂ) (hw : ‖w‖ = 1)
    (hperiod : w^N = 1) (ha : a ≤ N) : w^(N-a) = conj (w^a) := by
  have hne : w ≠ 0 := by intro h; simp [h] at hw
  have hmul : w^(N-a)*w^a = 1 := by
    rw [← pow_add, Nat.sub_add_cancel ha, hperiod]
  have hinv : (w^a)⁻¹ = conj (w^a) :=
    Complex.inv_eq_conj (by simp only [norm_pow, hw, one_pow])
  rw [← hinv]
  exact eq_inv_of_mul_eq_one_left hmul

theorem finiteDFT_add (n k : ℕ) (w : ℂ) (v u : ℕ → ℂ) :
    finiteDFT n w (fun j => v j + u j) k = finiteDFT n w v k + finiteDFT n w u k := by
  simp only [finiteDFT, mul_add, Finset.sum_add_distrib]

theorem finiteDFT_sum {ι : Type*} (S : Finset ι) (n k : ℕ) (w : ℂ) (v : ι → ℕ → ℂ) :
    finiteDFT n w (fun j => ∑ i ∈ S, v i j) k = ∑ i ∈ S, finiteDFT n w (v i) k := by
  simp only [finiteDFT, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem finiteDFT_single (n a k : ℕ) (w z : ℂ) (ha : a < n) :
    finiteDFT n w (fun j => if j = a then z else 0) k = w^(a*k)*z := by
  classical
  simp only [finiteDFT, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, ha, ↓reduceIte]

def paddedCosineInput (s : ℕ) (v : Fin (2^s) → ℝ) (j : ℕ) : ℂ :=
  ∑ t : Fin (2^s), ((if j = 2*t.val+1 then (v t : ℂ) else 0) +
    (if j = 4*2^s-(2*t.val+1) then (v t : ℂ) else 0))

/-- The input padding is a copy or a zero, with constant-time index formulas.
No real arithmetic or finite real sum is used to prepare this input. -/
def paddedCosineLookup (s : ℕ) (v : Fin (2^s) → ℝ) (j : ℕ) : ℂ :=
  if hj : j < 4*2^s then
    if heven : j%2 = 0 then 0
    else if hfirst : j < 2*2^s then
      (v ⟨j/2, by omega⟩ : ℂ)
    else
      (v ⟨(4*2^s-j)/2, by omega⟩ : ℂ)
  else 0

theorem paddedCosineLookup_eq (s : ℕ) (v : Fin (2^s) → ℝ) (j : ℕ) (hj : j < 4*2^s) :
    paddedCosineLookup s v j = paddedCosineInput s v j := by
  unfold paddedCosineLookup
  rw [dif_pos hj]
  by_cases heven : j%2 = 0
  · rw [dif_pos heven]
    symm
    apply Finset.sum_eq_zero
    intro t ht
    have h1 : j ≠ 2*t.val+1 := by omega
    have h2 : j ≠ 4*2^s-(2*t.val+1) := by have ht' := t.isLt; omega
    simp only [h1, h2, ↓reduceIte, add_zero]
  · rw [dif_neg heven]
    by_cases hfirst : j < 2*2^s
    · rw [dif_pos hfirst]
      let t0 : Fin (2^s) := ⟨j/2, by omega⟩
      have h1 (t : Fin (2^s)) : (j = 2*t.val+1) ↔ t = t0 := by
        constructor
        · intro h
          apply Fin.ext
          dsimp [t0]
          omega
        · rintro rfl
          dsimp [t0]
          omega
      have h2 (t : Fin (2^s)) : j ≠ 4*2^s-(2*t.val+1) := by have ht := t.isLt; omega
      simp only [paddedCosineInput, h1, h2, ↓reduceIte, add_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      rfl
    · rw [dif_neg hfirst]
      let t0 : Fin (2^s) := ⟨(4*2^s-j)/2, by omega⟩
      have h1 (t : Fin (2^s)) : j ≠ 2*t.val+1 := by have ht := t.isLt; omega
      have h2 (t : Fin (2^s)) : (j = 4*2^s-(2*t.val+1)) ↔ t = t0 := by
        constructor
        · intro h
          apply Fin.ext
          dsimp [t0]
          omega
        · rintro rfl
          dsimp [t0]
          omega
      simp only [paddedCosineInput, h1, h2, ↓reduceIte, zero_add, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      rfl

theorem finiteDFT_paddedCosineLookup (s k : ℕ) (v : Fin (2^s) → ℝ) (w : ℂ) :
    finiteDFT (4*2^s) w (paddedCosineLookup s v) k =
      finiteDFT (4*2^s) w (paddedCosineInput s v) k := by
  unfold finiteDFT
  apply Finset.sum_congr rfl
  intro j hj
  rw [paddedCosineLookup_eq s v j (Finset.mem_range.mp hj)]

theorem finiteDFT_paddedCosineInput (s k : ℕ) (v : Fin (2^s) → ℝ) :
    finiteDFT (4*2^s) (dyadicRoot s) (paddedCosineInput s v) k =
      (2 * ∑ j : Fin (2^s), v j * (T ℝ (k : ℤ)).eval (dyadicNode s j) : ℝ) := by
  unfold paddedCosineInput
  rw [finiteDFT_sum]
  simp only [finiteDFT_add]
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hn : 0 < 2^s := by positivity
  have hj' := j.isLt
  have hpos : 0 < 2*j.val+1 := by omega
  have hlt : 2*j.val+1 < 4*2^s := by omega
  have hlt' : 4*2^s-(2*j.val+1) < 4*2^s := by omega
  rw [finiteDFT_single _ _ _ _ _ hlt, finiteDFT_single _ _ _ _ _ hlt']
  have href : (dyadicRoot s)^((4*2^s-(2*j.val+1))*k) =
      conj ((dyadicRoot s)^((2*j.val+1)*k)) := by
    rw [pow_mul, unit_root_reflection _ _ _ (dyadicRoot_norm s) (dyadicRoot_pow_order s) hlt.le]
    simp only [map_pow, pow_mul]
  rw [href, ← add_mul, Complex.add_conj, dyadicRoot_power_re]
  push_cast
  ring

theorem dyadicDCTCoefficient_via_DFT (s : ℕ) (v : Fin (2^s) → ℝ) (k : Fin (2^s)) :
    dyadicDCTCoefficient s v k =
      (if k.val = 0 then 1/(2*(2^s : ℝ)) else 1/(2^s : ℝ)) *
        (finiteDFT (4*2^s) (dyadicRoot s) (paddedCosineInput s v) k.val).re := by
  rw [finiteDFT_paddedCosineInput]
  simp only [Complex.ofReal_re, dyadicDCTCoefficient]
  split_ifs <;> field_simp

theorem dyadicDCTCoefficient_via_radixTwo (s : ℕ) (v : Fin (2^s) → ℝ) (k : Fin (2^s)) :
    dyadicDCTCoefficient s v k =
      (if k.val = 0 then 1/(2*(2^s : ℝ)) else 1/(2^s : ℝ)) *
        (radixTwoDFT (s+2) (dyadicRoot s) (paddedCosineInput s v) k.val).re := by
  rw [radixTwoDFT_correct _ _ _ (dyadicRoot_isDyadicRoot s) k.val (by
    have hk := k.isLt
    have hn : 0 < 2^s := by positivity
    rw [show 2^(s+2) = 4*2^s by rw [pow_add]; ring]
    omega)]
  rw [show 2^(s+2) = 4*2^s by rw [pow_add]; ring]
  exact dyadicDCTCoefficient_via_DFT s v k

end
end HierarchicalAbsoluteSpectral
