import HierarchicalAbsoluteSpectral.NewtonScalar
import HierarchicalAbsoluteSpectral.WeightedError
import HierarchicalAbsoluteSpectral.Spectral

/-!
The actual finite matrix inverse iteration, with its spectral representation
proved rather than assumed. The functional calculus appears only in proofs.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k : ℕ}

def upperNewtonMatrix (M : Core k) : ℕ → Core k
  | 0 => (2:ℝ) • 1
  | n+1 => (1/2:ℝ) • (upperNewtonMatrix M n+M*(upperNewtonMatrix M n)⁻¹)

def baseNewtonIterate (S : Core k) (h : ℝ) (n : ℕ) : Core k :=
  upperNewtonMatrix (S*S+(8*h)^2 • (1 : Core k)) n

def baseNewtonMetric (S : Core k) (h : ℝ) (n : ℕ) : Core k :=
  baseNewtonIterate S h n+(8*h) • (1 : Core k)

theorem baseNewton_argument_cfc (S : Core k) (hS : S.IsHermitian) (h : ℝ) :
    cfc (p := IsSelfAdjoint) (fun x : ℝ => x^2+(8*h)^2) S = S*S+(8*h)^2 • (1 : Core k) := by
  rw [cfc_add (p := IsSelfAdjoint) (a := S) _ _ (finite_spectrum_continuous S _)
    (finite_spectrum_continuous S _), cfc_pow (p := IsSelfAdjoint) _ 2 S
    (finite_spectrum_continuous S _), cfc_id' (p := IsSelfAdjoint) ℝ S hS,
    cfc_const (p := IsSelfAdjoint) _ _ hS, Algebra.algebraMap_eq_smul_one, pow_two]

theorem baseNewtonIterate_cfc (S : Core k) (hS : S.IsHermitian) (h : ℝ) (hh : 0 < h) (n : ℕ) :
    baseNewtonIterate S h n =
      cfc (p := IsSelfAdjoint) (fun x : ℝ => upperNewtonScalar (x^2+(8*h)^2) n) S := by
  induction n with
  | zero =>
    simp only [baseNewtonIterate, upperNewtonMatrix, upperNewtonScalar,
      cfc_const (p := IsSelfAdjoint) (2:ℝ) S hS, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    have hi : cfc (p := IsSelfAdjoint)
        (fun x : ℝ => (upperNewtonScalar (x^2+(8*h)^2) n)⁻¹) S =
        (baseNewtonIterate S h n)⁻¹ := by
      rw [ih]
      simpa only [Matrix.nonsing_inv_eq_ringInverse] using
        cfc_inv (p := IsSelfAdjoint) (fun x : ℝ => upperNewtonScalar (x^2+(8*h)^2) n) S
          (fun x _ => (upperNewtonScalar_pos_of_pos _ (by positivity) n).ne')
          (finite_spectrum_continuous S _) hS
    change (1/2:ℝ) • (baseNewtonIterate S h n+
      (S*S+(8*h)^2 • (1 : Core k))*(baseNewtonIterate S h n)⁻¹) = _
    rw [← hi, ih, ← baseNewton_argument_cfc S hS h,
      ← cfc_mul (p := IsSelfAdjoint) _ _ S (finite_spectrum_continuous S _)
        (finite_spectrum_continuous S _),
      ← cfc_add (p := IsSelfAdjoint) (a := S) _ _ (finite_spectrum_continuous S _)
        (finite_spectrum_continuous S _),
      ← cfc_const_mul (p := IsSelfAdjoint) _ _ S (finite_spectrum_continuous S _)]
    apply cfc_congr (p := IsSelfAdjoint)
    intro x hx
    simp only [upperNewtonScalar, upperNewtonStep, div_eq_mul_inv]
    ring

theorem baseNewtonMetric_cfc (S : Core k) (hS : S.IsHermitian) (h : ℝ) (hh : 0 < h) (n : ℕ) :
    baseNewtonMetric S h n = cfc (p := IsSelfAdjoint) (fun x : ℝ => baseNewtonScalar h x n) S := by
  rw [baseNewtonMetric, baseNewtonIterate_cfc S hS h hh n,
    ← Algebra.algebraMap_eq_smul_one,
    ← cfc_const (p := IsSelfAdjoint) (8*h) S hS,
    ← cfc_add (p := IsSelfAdjoint) (a := S) _ _ (finite_spectrum_continuous S _)
      (finite_spectrum_continuous S _)]
  rfl

theorem baseNewtonIterate_posDef (S : Core k) (hS : S.IsHermitian) (h : ℝ) (hh : 0 < h) (n : ℕ) :
    (baseNewtonIterate S h n).PosDef := by
  apply Matrix.IsStrictlyPositive.posDef
  rw [baseNewtonIterate_cfc S hS h hh n]
  exact (cfc_isStrictlyPositive_iff (p := IsSelfAdjoint) _ S
    (finite_spectrum_continuous S _) hS).mpr
      (fun x _ => upperNewtonScalar_pos_of_pos _ (by positivity) n)

theorem baseNewtonMetric_posDef (S : Core k) (hS : S.IsHermitian) (h : ℝ) (hh : 0 < h) (n : ℕ) :
    (baseNewtonMetric S h n).PosDef := by
  apply Matrix.IsStrictlyPositive.posDef
  rw [baseNewtonMetric_cfc S hS h hh n]
  exact (cfc_isStrictlyPositive_iff (p := IsSelfAdjoint) _ S
    (finite_spectrum_continuous S _) hS).mpr (fun x _ => by
      unfold baseNewtonScalar
      have hp := upperNewtonScalar_pos_of_pos (x^2+(8*h)^2) (by positivity) n
      positivity)

theorem baseNewtonMetric_bounds (S : Core k) (hS : S.IsHermitian) (h : ℝ) (n : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/64) (hspec : ∀ x ∈ spectrum ℝ S, -1 ≤ x ∧ x ≤ 1)
    (hn : 2*(1/2:ℝ)^n ≤ 8*h) :
    (8*h) • (1 : Core k) ≤ baseNewtonMetric S h n ∧
      baseNewtonMetric S h n ≤ (2:ℝ) • (1 : Core k) ∧
      (8*h) • (1 : Core k) ≤ baseNewtonMetric S h n-S ∧
      (8*h) • (1 : Core k) ≤ baseNewtonMetric S h n+S := by
  have hb (x : ℝ) (hx : x ∈ spectrum ℝ S) :=
    baseNewtonScalar_bounds h x n hh hh' (hspec x hx).1 (hspec x hx).2 hn
  have hl := algebraMap_le_cfc (p := IsSelfAdjoint) (fun x : ℝ => baseNewtonScalar h x n)
    (8*h) S (fun x hx => (hb x hx).1) (finite_spectrum_continuous S _) hS
  have hu := cfc_le_algebraMap (p := IsSelfAdjoint) (fun x : ℝ => baseNewtonScalar h x n)
    2 S (fun x hx => (hb x hx).2.1) (finite_spectrum_continuous S _) hS
  have hm := algebraMap_le_cfc (p := IsSelfAdjoint) (fun x : ℝ => baseNewtonScalar h x n-x)
    (8*h) S (fun x hx => (hb x hx).2.2.1) (finite_spectrum_continuous S _) hS
  have hp := algebraMap_le_cfc (p := IsSelfAdjoint) (fun x : ℝ => baseNewtonScalar h x n+x)
    (8*h) S (fun x hx => (hb x hx).2.2.2.1) (finite_spectrum_continuous S _) hS
  rw [cfc_sub (p := IsSelfAdjoint) _ _ S (finite_spectrum_continuous S _)
    (finite_spectrum_continuous S _), cfc_id' (p := IsSelfAdjoint) ℝ S hS] at hm
  rw [cfc_add (p := IsSelfAdjoint) (a := S) _ _ (finite_spectrum_continuous S _)
    (finite_spectrum_continuous S _), cfc_id' (p := IsSelfAdjoint) ℝ S hS] at hp
  simpa only [← baseNewtonMetric_cfc S hS h hh n, Algebra.algebraMap_eq_smul_one] using
    And.intro hl (And.intro hu (And.intro hm hp))

theorem baseNewtonMetric_defect (S : Core k) (hS : S.IsHermitian) (h : ℝ) (n : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/64) (hspec : ∀ x ∈ spectrum ℝ S, -1 ≤ x ∧ x ≤ 1)
    (hn : 2*(1/2:ℝ)^n ≤ 8*h) :
    (0 : Core k) ≤ baseNewtonMetric S h n-S*(baseNewtonMetric S h n)⁻¹*S ∧
      baseNewtonMetric S h n-S*(baseNewtonMetric S h n)⁻¹*S ≤ (32*h) • (1 : Core k) := by
  have hF := baseNewtonMetric_posDef S hS h hh n
  have hi : cfc (p := IsSelfAdjoint) (fun x : ℝ => (baseNewtonScalar h x n)⁻¹) S =
      (baseNewtonMetric S h n)⁻¹ := by
    rw [baseNewtonMetric_cfc S hS h hh n]
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      cfc_inv (p := IsSelfAdjoint) (fun x : ℝ => baseNewtonScalar h x n) S (fun x _ => by
        apply ne_of_gt
        unfold baseNewtonScalar
        have hp := upperNewtonScalar_pos_of_pos (x^2+(8*h)^2) (by positivity) n
        positivity) (finite_spectrum_continuous S _) hS
  have hrep : baseNewtonMetric S h n-S*(baseNewtonMetric S h n)⁻¹*S =
      cfc (p := IsSelfAdjoint) (fun x : ℝ => baseNewtonScalar h x n-x^2/baseNewtonScalar h x n) S := by
    have hmul : S*(baseNewtonMetric S h n)⁻¹*S =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x*(baseNewtonScalar h x n)⁻¹*x) S := by
      rw [cfc_mul (p := IsSelfAdjoint) _ _ S (finite_spectrum_continuous S _)
        (finite_spectrum_continuous S _),
        cfc_mul (p := IsSelfAdjoint) _ _ S (finite_spectrum_continuous S _)
        (finite_spectrum_continuous S _), cfc_id' (p := IsSelfAdjoint) ℝ S hS, hi]
    rw [hmul, baseNewtonMetric_cfc S hS h hh n,
      ← cfc_sub (p := IsSelfAdjoint) _ _ S (finite_spectrum_continuous S _)
      (finite_spectrum_continuous S _)]
    apply cfc_congr (p := IsSelfAdjoint)
    intro x hx
    simp only [div_eq_mul_inv, pow_two]
    ring
  have hb (x : ℝ) (hx : x ∈ spectrum ℝ S) :=
    (baseNewtonScalar_bounds h x n hh hh' (hspec x hx).1 (hspec x hx).2 hn).2.2.2.2
  have hl := algebraMap_le_cfc (p := IsSelfAdjoint)
    (fun x : ℝ => baseNewtonScalar h x n-x^2/baseNewtonScalar h x n) 0 S
    (fun x hx => (hb x hx).1) (finite_spectrum_continuous S _) hS
  have hu := cfc_le_algebraMap (p := IsSelfAdjoint)
    (fun x : ℝ => baseNewtonScalar h x n-x^2/baseNewtonScalar h x n) (32*h) S
    (fun x hx => (hb x hx).2) (finite_spectrum_continuous S _) hS
  simpa only [← hrep, map_zero, Algebra.algebraMap_eq_smul_one] using And.intro hl hu

theorem baseNewtonMetric_contraction (S : Core k) (hS : S.IsHermitian) (h : ℝ) (n : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/64) (hspec : ∀ x ∈ spectrum ℝ S, -1 ≤ x ∧ x ≤ 1)
    (hn : 2*(1/2:ℝ)^n ≤ 8*h) : ‖S*(baseNewtonMetric S h n)⁻¹‖ ≤ 1 := by
  have hi : cfc (p := IsSelfAdjoint) (fun x : ℝ => (baseNewtonScalar h x n)⁻¹) S =
      (baseNewtonMetric S h n)⁻¹ := by
    rw [baseNewtonMetric_cfc S hS h hh n]
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      cfc_inv (p := IsSelfAdjoint) (fun x : ℝ => baseNewtonScalar h x n) S (fun x _ => by
        apply ne_of_gt
        unfold baseNewtonScalar
        have hp := upperNewtonScalar_pos_of_pos (x^2+(8*h)^2) (by positivity) n
        positivity) (finite_spectrum_continuous S _) hS
  have hrep : S*(baseNewtonMetric S h n)⁻¹ =
      cfc (p := IsSelfAdjoint) (fun x : ℝ => x/baseNewtonScalar h x n) S := by
    have hmul : S*(baseNewtonMetric S h n)⁻¹ =
        cfc (p := IsSelfAdjoint) (fun x : ℝ => x*(baseNewtonScalar h x n)⁻¹) S := by
      rw [cfc_mul (p := IsSelfAdjoint) _ _ S (finite_spectrum_continuous S _)
        (finite_spectrum_continuous S _), cfc_id' (p := IsSelfAdjoint) ℝ S hS, hi]
    simpa only [div_eq_mul_inv] using hmul
  have hscalar (x : ℝ) (hx : x ∈ spectrum ℝ S) : |x/baseNewtonScalar h x n| ≤ 1 := by
    have hb := baseNewtonScalar_bounds h x n hh hh' (hspec x hx).1 (hspec x hx).2 hn
    have hf : 0 < baseNewtonScalar h x n := by linarith [hb.1]
    have habs : |x| ≤ baseNewtonScalar h x n :=
      abs_le.mpr ⟨by linarith [hb.2.2.2.1], by linarith [hb.2.2.1]⟩
    rw [abs_div, abs_of_pos hf]
    exact (div_le_one hf).mpr habs
  have hCsym : (S*(baseNewtonMetric S h n)⁻¹).IsHermitian := by
    rw [hrep]
    exact cfc_predicate (p := IsSelfAdjoint) _ S
  have hCtrans : (S*(baseNewtonMetric S h n)⁻¹)ᵀ = S*(baseNewtonMetric S h n)⁻¹ := hCsym.eq
  have hCC : (S*(baseNewtonMetric S h n)⁻¹)*(S*(baseNewtonMetric S h n)⁻¹)ᵀ ≤ (1 : Core k) := by
    rw [hCtrans, hrep, ← pow_two, ← cfc_pow (p := IsSelfAdjoint) _ 2 S
      (finite_spectrum_continuous S _)]
    have hu := cfc_le_algebraMap (p := IsSelfAdjoint)
      (fun x : ℝ => (x/baseNewtonScalar h x n)^2) 1 S (fun x hx => by
        have hb := hscalar x hx
        nlinarith [sq_abs (x/baseNewtonScalar h x n), abs_nonneg (x/baseNewtonScalar h x n)])
      (finite_spectrum_continuous S _) hS
    simpa using hu
  apply spectral_norm_le_of_rayleigh _ 1 (by norm_num)
  intro x
  simpa using quadratic_mono hCC x

end
end HierarchicalAbsoluteSpectral
