import HierarchicalAbsoluteSpectral.GaussianBasics
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Measure.Prod

/-! Nonzero finite multivariate polynomials vanish with probability zero
under independent real Gaussian inputs. The proof uses finite univariate
root sets and induction/Fubini, including zero variables. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem gaussian_polynomial_ne_zero_ae (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x ∂gaussianVector n, MvPolynomial.eval x p ≠ 0 := by
  classical
  induction n with
  | zero =>
      apply Filter.Eventually.of_forall
      intro x hx
      have hinj : Function.Injective (MvPolynomial.aeval x : MvPolynomial (Fin 0) ℝ →ₐ[ℝ] ℝ) :=
        MvPolynomial.aeval_injective_iff_of_isEmpty.mpr (by intro a b h; exact h)
      apply hp
      apply hinj
      simpa using hx
  | succ n ih =>
      let q := MvPolynomial.finSuccEquiv ℝ n p
      have hq : q ≠ 0 := (MvPolynomial.finSuccEquiv ℝ n).injective.ne hp
      let i := q.natDegree
      have hqi : q.coeff i ≠ 0 := by
        dsimp only [i]
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hq
      have hcoeff := ih (q.coeff i) hqi
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
      have hpmp := MeasurePreserving.symm e
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0)
      let Z : Set (Fin (n+1) → ℝ) := {x | MvPolynomial.eval x p = 0}
      have hZ : MeasurableSet Z :=
        (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet
      have hZe : MeasurableSet (e.symm ⁻¹' Z) := e.symm.measurable hZ
      have heval (a : ℝ) (x : Fin n → ℝ) :
          MvPolynomial.eval (e.symm (a,x)) p =
            Polynomial.eval a (q.map (MvPolynomial.eval x)) := by
        have heq : e.symm (a,x) = Fin.cons a x := by
          funext j
          refine Fin.cases ?_ (fun j => ?_) j <;>
            simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
              Fin.insertNth_zero]
        rw [heq]
        exact MvPolynomial.eval_eq_eval_mv_eval' x a p
      have hsections : (fun x : Fin n → ℝ =>
          gaussianReal 0 1 ((fun a => (a,x)) ⁻¹' (e.symm ⁻¹' Z))) =ᵐ[gaussianVector n] 0 := by
        letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
        filter_upwards [hcoeff] with x hx
        have hmap : q.map (MvPolynomial.eval x) ≠ 0 := by
          intro hz
          have hzcoeff := congrArg (fun u : Polynomial ℝ => u.coeff i) hz
          rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hzcoeff
          exact hx hzcoeff
        have hroots := (Polynomial.finite_setOf_isRoot hmap).measure_zero (gaussianReal 0 1)
        have hset : ((fun a => (a,x)) ⁻¹' (e.symm ⁻¹' Z)) =
            {a | (q.map (MvPolynomial.eval x)).IsRoot a} := by
          ext a
          simp only [Set.mem_preimage, Z, Set.mem_setOf_eq, heval, Polynomial.IsRoot]
        rw [hset]
        exact hroots
      have hprod : ((gaussianReal 0 1).prod (gaussianVector n)) (e.symm ⁻¹' Z) = 0 := by
        rw [Measure.prod_apply_symm hZe]
        rw [lintegral_congr_ae hsections]
        simp
      have hz : gaussianVector (n+1) Z = 0 := by
        exact (hpmp.measure_preimage_emb e.symm.measurableEmbedding Z).symm.trans hprod
      exact ae_iff.mpr (by simpa only [not_not] using hz)

theorem gaussian_polynomial_reindex_ne_zero_ae {ι : Type*} [Fintype ι]
    (n : ℕ) (e : ι ≃ Fin n) (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    ∀ᵐ x ∂gaussianVector n, MvPolynomial.eval (fun i => x (e i)) p ≠ 0 := by
  have hren : MvPolynomial.rename e p ≠ 0 :=
    (MvPolynomial.rename_injective e e.injective).ne hp
  have h := gaussian_polynomial_ne_zero_ae n (MvPolynomial.rename e p) hren
  simpa only [MvPolynomial.eval_rename, Function.comp_def] using h

end
end HierarchicalAbsoluteSpectral
