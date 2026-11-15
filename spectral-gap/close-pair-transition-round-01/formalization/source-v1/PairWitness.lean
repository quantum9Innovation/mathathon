import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Matrix

namespace ClosePair

noncomputable section

def pairPlus {ι : Type*} [DecidableEq ι] (a b : ι) : ι → ℝ :=
  Pi.single a 1 + Pi.single b 1

theorem pairPlus_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (a b : ι) :
    pairPlus a b ⬝ᵥ (M *ᵥ pairPlus a b) =
      M a a + M a b + M b a + M b b := by
  simp [pairPlus, add_dotProduct, dotProduct_add, mulVec_add]
  ring

theorem pairPlus_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) (hab : a ≠ b) :
    pairPlus a b ⬝ᵥ pairPlus a b = 2 := by
  norm_num [pairPlus, dotProduct_add, hab, hab.symm]

theorem pairPlus_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) (hab : a ≠ b) : pairPlus a b ≠ 0 := by
  intro h
  have hh := pairPlus_norm_sq a b hab
  rw [h] at hh
  norm_num at hh

def pairSchur {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : Matrix ι ι ℝ) (z : ℝ) : Matrix ι ι ℝ :=
  (2 * z) • 1 - z ^ 2 • G + H

theorem pairSchur_rayleigh {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : Matrix ι ι ℝ) (z : ℝ) (a b : ι) (hab : a ≠ b)
    (hG : G b a = G a b)
    (haa : H a a = 0) (hbb : H b b = 0)
    (habH : H a b = 0) (hbaH : H b a = 0) :
    (pairPlus a b ⬝ᵥ (pairSchur G H z *ᵥ pairPlus a b)) /
        (pairPlus a b ⬝ᵥ pairPlus a b) =
      2 * z - z ^ 2 * (G a a + G b b) / 2 - z ^ 2 * G a b := by
  rw [pairPlus_quadratic, pairPlus_norm_sq a b hab]
  simp [pairSchur, hab, hab.symm, hG, haa, hbb, habH, hbaH]
  ring

theorem pairSchur_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : Matrix ι ι ℝ) (z g t : ℝ) (a b : ι) (hab : a ≠ b)
    (hG : G b a = G a b)
    (haa : H a a = 0) (hbb : H b b = 0)
    (habH : H a b = 0) (hbaH : H b a = 0)
    (hga : g ≤ G a a) (hgb : g ≤ G b b) (hgab : g * t ≤ G a b) :
    (pairPlus a b ⬝ᵥ (pairSchur G H z *ᵥ pairPlus a b)) /
        (pairPlus a b ⬝ᵥ pairPlus a b) ≤
      2 * z - z ^ 2 * g - z ^ 2 * g * t := by
  rw [pairSchur_rayleigh G H z a b hab hG haa hbb habH hbaH]
  have ha := mul_le_mul_of_nonneg_left hga (sq_nonneg z)
  have hb := mul_le_mul_of_nonneg_left hgb (sq_nonneg z)
  have hc := mul_le_mul_of_nonneg_left hgab (sq_nonneg z)
  nlinarith

theorem pairSchur_negative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : Matrix ι ι ℝ) (z g t : ℝ) (a b : ι) (hab : a ≠ b)
    (hG : G b a = G a b)
    (haa : H a a = 0) (hbb : H b b = 0)
    (habH : H a b = 0) (hbaH : H b a = 0)
    (hga : g ≤ G a a) (hgb : g ≤ G b b) (hgab : g * t ≤ G a b)
    (hthreshold : 2 * z - z ^ 2 * g - z ^ 2 * g * t < 0) :
    pairPlus a b ⬝ᵥ (pairSchur G H z *ᵥ pairPlus a b) < 0 := by
  have h := pairSchur_bound G H z g t a b hab hG haa hbb habH hbaH hga hgb hgab
  rw [pairPlus_norm_sq a b hab] at h
  linarith

#print axioms pairPlus_quadratic
#print axioms pairPlus_norm_sq
#print axioms pairPlus_nonzero
#print axioms pairSchur_rayleigh
#print axioms pairSchur_bound
#print axioms pairSchur_negative

end

end ClosePair
