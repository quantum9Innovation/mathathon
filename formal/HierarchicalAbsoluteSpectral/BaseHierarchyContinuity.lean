import HierarchicalAbsoluteSpectral.BaseContinuity
import HierarchicalAbsoluteSpectral.FiniteHierarchy
import Mathlib.Topology.Algebra.Polynomial

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Polynomial
variable {X : Type*} [TopologicalSpace X] {k : ℕ}

theorem refinedInverseFactor_continuous (R K : X → Core k)
    (hR : Continuous R) (hK : Continuous K) (ε : ℝ) (p : ℝ[X]) :
    Continuous (fun x => refinedInverseFactor (R x) (K x) ε p) := by
  let Rp := fun x => inflatedInverseFactor (R x) ε
  have hp : Continuous Rp := continuous_const.smul hR
  have hA := (hp.matrix_transpose.matrix_mul hK).matrix_mul hp
  exact hp.matrix_mul (p.continuous_aeval.comp hA)

theorem finiteRefinementFactor_continuous (R K : X → Core k)
    (hR : Continuous R) (hK : Continuous K) (ε h B : ℝ) :
    Continuous (fun x => finiteRefinementFactor (R x) (K x) ε h B) :=
  refinedInverseFactor_continuous R K hR hK ε (refinementPolynomial ε h B)

theorem hierarchicalInverseFactor_continuous
    (R0 : X → Core k) (Kfine : X → ℕ → Core k) (h : ℕ → ℝ)
    (hR : Continuous R0) (hK : ∀ j, Continuous (fun x => Kfine x j)) (j : ℕ) :
    Continuous (fun x => hierarchicalInverseFactor (R0 x) (Kfine x) h j) := by
  induction j with
  | zero => simpa only [hierarchicalInverseFactor] using hR
  | succ j ih =>
    exact finiteRefinementFactor_continuous _ _ ih (hK j)
      (h (j+1)/h j) (h (j+1)) (hierarchyUpper j)

theorem affine_hierarchicalInverseFactor_continuous
    (R0 : X → Core k) (t : X → ℝ) (N Q : ℕ → Core k) (h : ℕ → ℝ)
    (hR : Continuous R0) (ht : Continuous t) (j : ℕ) :
    Continuous (fun x => hierarchicalInverseFactor (R0 x)
      (fun i => t x • N i-Q i) h j) := by
  apply hierarchicalInverseFactor_continuous _ _ _ hR
  intro i
  exact (ht.smul continuous_const).sub continuous_const

theorem coarse_hierarchicalInverseFactor_continuous
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Q0 : Core k) (hQ0 : Q0.PosSemidef) (h0 : ℝ) (hh0 : 0 < h0)
    (N Q : ℕ → Core k) (h : ℕ → ℝ) (j : ℕ) :
    Continuous (fun t : {t : ℝ // 0 < t} =>
      hierarchicalInverseFactor
        (coarseBaseProgram kernels Q0 hQ0 t.val t.property h0 hh0).eval.inverseFactor
        (fun i => t.val • N i-Q i) h j) :=
  affine_hierarchicalInverseFactor_continuous _ _ N Q h
    (coarseBaseProgram_inverseFactor_continuous kernels Q0 hQ0 h0 hh0) continuous_subtype_val j

theorem coarse_threshold_change_continuous
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Q0 : Core k) (hQ0 : Q0.PosSemidef) (h0 : ℝ) (hh0 : 0 < h0)
    (N Q : ℕ → Core k) (h : ℕ → ℝ) (j : ℕ) :
    Continuous (fun t : {t : ℝ // 0 < t} =>
      ((coarseBaseProgram kernels Q0 hQ0 t.val t.property h0 hh0).eval.inverseFactor)⁻¹ *
        hierarchicalInverseFactor
          (coarseBaseProgram kernels Q0 hQ0 t.val t.property h0 hh0).eval.inverseFactor
          (fun i => t.val • N i-Q i) h j) := by
  have hi := continuous_matrix_inverse _
    (coarseBaseProgram_inverseFactor_continuous kernels Q0 hQ0 h0 hh0)
    (fun t => isUnit_iff_ne_zero.mp
      (coarseBaseProgram kernels Q0 hQ0 t.val t.property h0 hh0).eval.inverseFactor_isUnit)
  exact hi.matrix_mul (coarse_hierarchicalInverseFactor_continuous kernels Q0 hQ0 h0 hh0 N Q h j)

theorem coarse_threshold_operator_continuous
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (Q0 : Core k) (hQ0 : Q0.PosSemidef) (h0 : ℝ) (hh0 : 0 < h0)
    (N Q : ℕ → Core k) (h : ℕ → ℝ) (j : ℕ) (Bm Qtrue : Core k) :
    Continuous (fun t : {t : ℝ // 0 < t} =>
      let Rj := hierarchicalInverseFactor
        (coarseBaseProgram kernels Q0 hQ0 t.val t.property h0 hh0).eval.inverseFactor
        (fun i => t.val • N i-Q i) h j
      (1 : Core k)-Rjᵀ*(t.val • Bm-Qtrue)*Rj) := by
  have hj := coarse_hierarchicalInverseFactor_continuous kernels Q0 hQ0 h0 hh0 N Q h j
  have hK : Continuous (fun t : {t : ℝ // 0 < t} => t.val • Bm-Qtrue) :=
    (continuous_subtype_val.smul continuous_const).sub continuous_const
  exact continuous_const.sub ((hj.matrix_transpose.matrix_mul hK).matrix_mul hj)

end
end HierarchicalAbsoluteSpectral
