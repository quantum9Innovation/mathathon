import HierarchicalAbsoluteSpectral.DCTViaDFT
import HierarchicalAbsoluteSpectral.ScalarConstruction

/-! Fast coefficient generation with an executed real-operation count.
Input padding consists solely of copies and zeroes. The root is supplied
here and is constructed by `dyadicRootProgram` in the complete sampler. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open ArithmeticProgram hiding pure

def dctFFTIndex (s : ℕ) (k : Fin (2^s)) : Fin (2^(s+2)) :=
  ⟨k.val, k.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s ≤ s+2))⟩

def dctProgram (s : ℕ) (w : ℂ) (v : Fin (2^s) → ℝ) : ArithmeticProgram (Fin (2^s) → ℝ) := do
  let f ← fftProgram (s+2) w (paddedCosineLookup s v)
  let b ← dyadicScaleProgram s
  let b0 ← div b 2
  tabulate (2^s) (fun k => mul (if k.val = 0 then b0 else b) (f (dctFFTIndex s k)).re)

theorem dctProgram_eval (s : ℕ) (v : Fin (2^s) → ℝ) (k : Fin (2^s)) :
    (dctProgram s (dyadicRoot s) v).eval k = dyadicDCTCoefficient s v k := by
  simp only [dctProgram, eval_bind, dyadicScaleProgram_eval, eval_div, eval_tabulate, eval_mul]
  rw [(fftProgram_specification (s+2) (dyadicRoot s) (paddedCosineLookup s v)
    (dyadicRoot_isDyadicRoot s)).2.1 (dctFFTIndex s k)]
  change (if k.val = 0 then (1/(2^s : ℝ))/2 else 1/(2^s : ℝ)) *
    (finiteDFT (2^(s+2)) (dyadicRoot s) (paddedCosineLookup s v) k.val).re = _
  rw [show 2^(s+2) = 4*2^s by rw [pow_add]; ring, finiteDFT_paddedCosineLookup,
    dyadicDCTCoefficient_via_DFT]
  congr 1
  split_ifs <;> field_simp

theorem dctProgram_work (s : ℕ) (w : ℂ) (v : Fin (2^s) → ℝ) :
    (dctProgram s w v).work = fftWork (s+2)+s+1+2^s := by
  simp only [dctProgram, work_bind, fftProgram_work, dyadicScaleProgram_work, work_div,
    work_tabulate, work_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_one]
  omega

theorem dctProgram_work_bound (s : ℕ) (w : ℂ) (v : Fin (2^s) → ℝ) :
    (dctProgram s w v).work ≤ 40*(s+3)*2^s := by
  rw [dctProgram_work]
  have h := fftWork_exact (s+2)
  rw [pow_add] at h
  norm_num at h
  have hn : 1 ≤ 2^s := one_le_pow₀ (by decide : 1 ≤ (2:ℕ))
  nlinarith

theorem dctProgram_admissible (s : ℕ) (w : ℂ) (v : Fin (2^s) → ℝ) :
    (dctProgram s w v).admissible := by
  simp [dctProgram, fftProgram_admissible]

theorem dctProgram_specification (s : ℕ) (v : Fin (2^s) → ℝ) :
    (dctProgram s (dyadicRoot s) v).admissible ∧
      (∀ k, (dctProgram s (dyadicRoot s) v).eval k = dyadicDCTCoefficient s v k) ∧
      (dctProgram s (dyadicRoot s) v).work ≤ 40*(s+3)*2^s :=
  ⟨dctProgram_admissible s _ v, dctProgram_eval s v, dctProgram_work_bound s _ v⟩

end
end HierarchicalAbsoluteSpectral
