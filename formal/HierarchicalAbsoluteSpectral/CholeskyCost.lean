import HierarchicalAbsoluteSpectral.CholeskyProgram
import HierarchicalAbsoluteSpectral.PaddedKernels

/-! Balanced Cholesky preserves every square multiplication exponent
at least two. The bound is for the executed program's operation count. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

theorem balanced_rpow_split (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 2 ≤ p) :
    ((n/2:ℕ):ℝ)^p+((n-n/2:ℕ):ℝ)^p ≤ (5/9:ℝ)*(n:ℝ)^p := by
  let l := n/2
  let r := n-l
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hr : 1 ≤ r := by dsimp [r, l]; omega
  have hln : l ≤ n := by dsimp [l]; omega
  have hrn : r ≤ n := by dsimp [r]; omega
  have he : l+r = n := by dsimp [l, r]; omega
  have hb1 : r ≤ 2*l := by dsimp [r, l]; omega
  have hb2 : l ≤ 2*r := by dsimp [r, l]; omega
  have hnpos : (0:ℝ) < n := by positivity
  have hs : (l:ℝ)+(r:ℝ) = n := by exact_mod_cast he
  have hb1' : (r:ℝ) ≤ 2*l := by exact_mod_cast hb1
  have hb2' : (l:ℝ) ≤ 2*r := by exact_mod_cast hb2
  have hsq : (l:ℝ)^2+(r:ℝ)^2 ≤ (5/9:ℝ)*(n:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1') (sub_nonneg.mpr hb2')]
  have hpow (a : ℕ) (ha : 1 ≤ a) (han : a ≤ n) :
      (a:ℝ)^p ≤ (a:ℝ)^2*(n:ℝ)^(p-2) := by
    have hapos : (0:ℝ) < a := by positivity
    calc
      _ = (a:ℝ)^2*(a:ℝ)^(p-2) := by
        rw [← Real.rpow_two, ← Real.rpow_add hapos]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast han) (by linarith)) (sq_nonneg _)
  change (l:ℝ)^p+(r:ℝ)^p ≤ _
  calc
    _ ≤ ((l:ℝ)^2+(r:ℝ)^2)*(n:ℝ)^(p-2) := by
      simpa only [add_mul] using add_le_add (hpow l hl hln) (hpow r hr hrn)
    _ ≤ ((5/9:ℝ)*(n:ℝ)^2)*(n:ℝ)^(p-2) :=
      mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_two, ← Real.rpow_add hnpos]
      congr 2
      ring

theorem choleskyCost_bound (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0 < C) (hp : 2 ≤ p)
    (hK : ∀ a b c N : ℕ, 1 ≤ max a (max b c) → 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost:ℝ) ≤ C*(N:ℝ)^p) (n : ℕ) (hn : 1 ≤ n) :
    (choleskyCost kernels n:ℝ) ≤ 9*(C+1)*(n:ℝ)^p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · omega
    · rw [choleskyCost]
      norm_num
      linarith
    · let l := (n+2)/2
      let r := n+2-l
      have hl : l < n+2 := by dsimp [l]; omega
      have hr : r < n+2 := by dsimp [r, l]; omega
      have hl1 : 1 ≤ l := by dsimp [l]; omega
      have hr1 : 1 ≤ r := by dsimp [r, l]; omega
      have hln : l ≤ n+2 := by omega
      have hrn : r ≤ n+2 := by omega
      have he : l+r = n+2 := by dsimp [l, r]; omega
      have hn1 : 1 ≤ n+2 := by omega
      have hnreal : (1:ℝ) ≤ n+2 := by exact_mod_cast hn1
      have hnnonneg : (0:ℝ) ≤ n+2 := by positivity
      have hnp : 0 ≤ (n+2:ℝ)^p := Real.rpow_nonneg hnnonneg _
      have ihl := ih l hl hl1
      have ihr := ih r hr hr1
      have hs := balanced_rpow_split (n+2) (by omega) p hp
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at hs
      change (l:ℝ)^p+(r:ℝ)^p ≤ (5/9:ℝ)*(n+2:ℝ)^p at hs
      have hrec : (choleskyCost kernels l:ℝ)+(choleskyCost kernels r:ℝ) ≤
          (9*(C+1))*((5/9:ℝ)*(n+2:ℝ)^p) := by
        calc
          _ ≤ 9*(C+1)*(l:ℝ)^p+9*(C+1)*(r:ℝ)^p := add_le_add ihl ihr
          _ = 9*(C+1)*((l:ℝ)^p+(r:ℝ)^p) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      have hllr := hK l l r (n+2) (by omega) hn1 hln hln hrn
      have hrlr := hK r l r (n+2) (by omega) hn1 hrn hln hrn
      have hlrr := hK l r r (n+2) (by omega) hn1 hln hrn hrn
      have hquadratic : (r:ℝ)*(r:ℝ)+(l:ℝ)*(r:ℝ) ≤ (n+2:ℝ)^p := by
        have he' : (l:ℝ)+(r:ℝ) = n+2 := by exact_mod_cast he
        have hr' : (r:ℝ) ≤ n+2 := by exact_mod_cast hrn
        have hsq : (r:ℝ)*(r:ℝ)+(l:ℝ)*(r:ℝ) ≤ (n+2:ℝ)^2 := by
          nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ n+2) (sub_nonneg.mpr hr')]
        apply hsq.trans
        simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hnreal hp
      rw [choleskyCost]
      change ((choleskyCost kernels l+choleskyCost kernels r+
        2*(kernels l l r).cost+(kernels r l r).cost+(kernels l r r).cost+r*r+l*r:ℕ):ℝ) ≤ _
      push_cast
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at hllr hrlr hlrr
      rw [show (n:ℝ)+1+1 = n+2 by ring]
      nlinarith

theorem exists_fast_cholesky (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (D : Core n) (hD : D.PosDef), 1 ≤ n →
        ((choleskyProgram kernels n D hD).work:ℝ) ≤ C*(n:ℝ)^(9/4+ζ) := by
  obtain ⟨kernels,C,hC,hK⟩ := exists_padded_arithmetic_kernels ζ hζ
  refine ⟨kernels,9*(C+1),by positivity,?_⟩
  intro n D hD hn
  rw [choleskyProgram_work]
  apply choleskyCost_bound kernels C (9/4+ζ) hC (by linarith) _ n hn
  intro a b c N hm _hN ha hb hc
  apply (hK a b c hm).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  exact_mod_cast max_le ha (max_le hb hc)

end
end HierarchicalAbsoluteSpectral
