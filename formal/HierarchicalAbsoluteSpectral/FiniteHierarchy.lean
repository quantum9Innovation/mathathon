import HierarchicalAbsoluteSpectral.BaseTheorem
import HierarchicalAbsoluteSpectral.RefinementAction

/-! The complete finite induction, with the manuscript's literal constants.
The only per-level mathematical inputs are the actual proxy error events. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

def hierarchyConstant : ℕ → ℝ
  | 0 => 36
  | j+1 => 100*(hierarchyConstant j+1)

def hierarchyUpper (j : ℕ) : ℝ := 2^(j+1)
def hierarchyRelaxation : ℕ → ℝ
  | 0 => 1
  | _+1 => 5

theorem hierarchyConstant_ge_one (j : ℕ) : 1≤hierarchyConstant j := by
  induction j with
  | zero => norm_num [hierarchyConstant]
  | succ j ih => simp only [hierarchyConstant]; linarith

theorem hierarchyUpper_nonneg (j : ℕ) : 0≤hierarchyUpper j := by unfold hierarchyUpper; positivity
theorem hierarchyRelaxation_bounds (j : ℕ) : 0≤hierarchyRelaxation j ∧ hierarchyRelaxation j≤5 := by
  cases j <;> norm_num [hierarchyRelaxation]

structure HierarchyInvariant (R K D : Core k) (j : ℕ) (h : ℝ) : Prop where
  isUnit : IsUnit R.det
  floor : (8*h) • D ≤ inverseMetric R
  upper : inverseMetric R≤hierarchyUpper j • D
  lower_pencil : -inverseMetric R≤K
  upper_pencil : K ≤ inverseMetric R
  defect : inverseMetric R-hierarchyRelaxation j • (K*(inverseMetric R)⁻¹*K)≤
    (hierarchyConstant j*h) • D

theorem HierarchyInvariant.step (R K Kj D : Core k) (j : ℕ) (H h ε : ℝ)
    (prev : HierarchyInvariant R K D j H) (hD : D.PosDef)
    (hK : Kᵀ=K) (hKj : Kjᵀ=Kj)
    (hh : 0<h) (hh' : h≤1/64) (hH : 0<H) (hε : 0<ε) (hε' : ε≤1/1024)
    (hscale : h=ε*H)
    (hlo : -((8*h) • D)≤Kj-K) (hup : Kj-K≤(8*h) • D) :
    HierarchyInvariant (finiteRefinementFactor R Kj ε h (hierarchyUpper j)) K D (j+1) h := by
  obtain ⟨hr,hf,hu,hm,hp,hd⟩ := constructed_finite_refinement R K Kj D
    (hierarchyRelaxation j) (hierarchyConstant j) (hierarchyUpper j) h H ε
    prev.isUnit hD hK hKj (hierarchyRelaxation_bounds j).1 (hierarchyRelaxation_bounds j).2
    (hierarchyConstant_ge_one j) (hierarchyUpper_nonneg j) hh hh' hH hε hε' hscale
    prev.floor prev.upper prev.lower_pencil prev.upper_pencil hlo hup prev.defect
  have h0 : (0 : Core k)≤(55*h) • D := smul_nonneg (by positivity) hD.posSemidef.nonneg
  refine ⟨hr,hf,?_,?_,?_,?_⟩
  · simpa only [hierarchyUpper, pow_succ, mul_comm (2:ℝ)] using hu
  · have hs := sub_le_sub_right (h0.trans hp) (inverseMetric (finiteRefinementFactor R Kj ε h (hierarchyUpper j)))
    convert hs using 1 <;> module
  · exact sub_nonneg.mp (h0.trans hm)
  · simpa only [hierarchyRelaxation, hierarchyConstant] using hd

def hierarchicalInverseFactor (R₀ : Core k) (Kfine : ℕ → Core k) (h : ℕ → ℝ) : ℕ → Core k
  | 0 => R₀
  | j+1 => finiteRefinementFactor (hierarchicalInverseFactor R₀ Kfine h j)
      (Kfine j) (h (j+1)/h j) (h (j+1)) (hierarchyUpper j)

theorem constructed_hierarchy_invariant (R₀ K D : Core k) (Kfine : ℕ → Core k)
    (h : ℕ → ℝ) (L : ℕ) (hD : D.PosDef) (hK : Kᵀ=K)
    (base : HierarchyInvariant R₀ K D 0 (h 0))
    (hpositive : ∀ j≤L, 0<h j) (hbounded : ∀ j≤L, h j≤1/64)
    (hratio : ∀ j<L, h (j+1)/h j≤1/1024)
    (hsym : ∀ j<L, (Kfine j)ᵀ=Kfine j)
    (hproxy : ∀ j<L, -((8*h (j+1)) • D)≤Kfine j-K ∧ Kfine j-K≤(8*h (j+1)) • D) :
    ∀ j≤L, HierarchyInvariant (hierarchicalInverseFactor R₀ Kfine h j) K D j (h j) := by
  intro j
  induction j with
  | zero => intro hj; exact base
  | succ j ih =>
      intro hj
      have hjL : j<L := by omega
      have hjle : j≤L := by omega
      rw [hierarchicalInverseFactor]
      apply HierarchyInvariant.step _ _ _ _ j (h j) (h (j+1)) (h (j+1)/h j)
        (ih hjle) hD hK (hsym j hjL) (hpositive (j+1) hj) (hbounded (j+1) hj)
        (hpositive j hjle) (div_pos (hpositive (j+1) hj) (hpositive j hjle))
        (hratio j hjL) _ (hproxy j hjL).1 (hproxy j hjL).2
      field_simp [(hpositive j hjle).ne']

theorem base_hierarchy_invariant (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (G Q Q₀ : Core k) (hQ : Q.PosSemidef) (hQ₀ : Q₀.PosSemidef)
    (h ε t : ℝ) (hh : 0<h) (hh' : h≤1/64) (hε : 0<ε) (hε' : ε≤h/100) (ht : 0<t)
    (hGlo : (1/(1+h)) • (1 : Core k)≤G) (hGup : G≤(1/(1-h)) • (1 : Core k))
    (hQlo : (1-h) • Q≤Q₀) (hQup : Q₀≤(1+h) • Q) :
    HierarchyInvariant (coarseBaseProgram kernels Q₀ hQ₀ t ht h hh).eval.inverseFactor
      (trueNeumannPencil G Q t ε hε) (t • (1 : Core k)+Q₀) 0 h := by
  obtain ⟨hr,he,hp,hf,hu,hm,hpl,hmd,hpd,hn,hd⟩ :=
    finite_weighted_defect kernels G Q Q₀ hQ hQ₀ h ε t hh hh' hε hε' ht hGlo hGup hQlo hQup
  refine ⟨hr,?_,?_,?_,?_,?_⟩
  · rwa [he]
  · simpa [hierarchyUpper, he] using hu
  · have hs := sub_le_sub_right hpd.posSemidef.nonneg
      (coarseBaseProgram kernels Q₀ hQ₀ t ht h hh).eval.metric
    rw [he]
    convert hs using 1 <;> module
  · rw [he]
    exact sub_nonneg.mp hmd.posSemidef.nonneg
  · simpa only [hierarchyConstant, hierarchyRelaxation, one_smul, he] using hd

end
end HierarchicalAbsoluteSpectral
