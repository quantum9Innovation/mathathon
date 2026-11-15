import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic

namespace HierarchicalAbsoluteSpectral

open Polynomial Set

noncomputable section

/-- Translating and contracting the interval by two turns a central derivative
bound into the interior Bernstein bound used below. -/
theorem interior_derivative_bound_of_central
    (hcentral : ∀ (q : ℝ[X]) (M : ℝ),
      (∀ y ∈ Icc (-1 : ℝ) 1, |q.eval y| ≤ M) →
        |q.derivative.eval 0| ≤ q.natDegree * M)
    (p : ℝ[X]) (M x : ℝ)
    (hp : ∀ y ∈ Icc (-1 : ℝ) 1, |p.eval y| ≤ M)
    (hx : |x| ≤ 1 / 2) :
    |p.derivative.eval x| ≤ 2 * p.natDegree * M := by
  let q : ℝ[X] := p.comp (C (1 / 2) * X + C x)
  have hq : ∀ y ∈ Icc (-1 : ℝ) 1, |q.eval y| ≤ M := by
    intro y hy
    dsimp [q]
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
    apply hp
    rcases abs_le.mp hx with ⟨hxl, hxu⟩
    constructor <;> nlinarith [hy.1, hy.2]
  have hdeg : q.natDegree = p.natDegree := by
    dsimp [q]
    rw [natDegree_comp, natDegree_linear (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_one]
  have hder : q.derivative.eval 0 = (1 / 2 : ℝ) * p.derivative.eval x := by
    simp [q, derivative_comp]
  have hc := hcentral q M hq
  rw [hdeg, hder, abs_mul] at hc
  norm_num at hc
  nlinarith

end

end HierarchicalAbsoluteSpectral
