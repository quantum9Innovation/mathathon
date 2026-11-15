import HierarchicalAbsoluteSpectral.GaussianLeadingMinors
import HierarchicalAbsoluteSpectral.MinMaxProjectorMeasurable
import Mathlib.Topology.Instances.Rat

/-! A jointly Borel, basis-independent sufficient event for Gaussian inertia.
Nonzero determinant polynomials are detected on the countable rational grid;
no measurable choice of a rank-dependent basis is needed. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
local instance matrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance matrixBorelInstance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

def ambientMinorValue (D : Core n) (j : ℕ) (hj : j≤n) (g : Fin (n*n) → ℝ) : ℝ :=
  (leadingPrincipal ((gaussianSquareMatrix n g)ᵀ*D*gaussianSquareMatrix n g) j hj).det

theorem ambientMinorValue_continuous (j : ℕ) (hj : j≤n) :
    Continuous (fun z : Core n × (Fin (n*n) → ℝ) => ambientMinorValue z.1 j hj z.2) := by
  have hG : Continuous (fun z : Core n × (Fin (n*n) → ℝ) => gaussianSquareMatrix n z.2) := by
    apply continuous_matrix
    intro i l
    exact (continuous_apply (finProdFinEquiv (i,l))).comp continuous_snd
  exact (((hG.matrix_transpose.matrix_mul continuous_fst).matrix_mul hG).matrix_submatrix
    (Fin.castLEEmb hj) (Fin.castLEEmb hj)).matrix_det

def ambientMinorActive (D : Core n) (j : ℕ) (hj : j≤n) : Prop :=
  ∃ q : Fin (n*n) → ℚ, ambientMinorValue D j hj (fun i => (q i:ℝ))≠0

theorem ambientMinorActive_iff (D : Core n) (j : ℕ) (hj : j≤n) :
    ambientMinorActive D j hj ↔ congruenceMinorPolynomial D j hj≠0 := by
  constructor
  · rintro ⟨q,hq⟩ hp
    have he := congruenceMinorPolynomial_eval D (gaussianSquareMatrix n (fun i => (q i:ℝ))) j hj
    rw [hp,map_zero] at he
    exact hq he.symm
  · intro hp
    have hg := gaussian_polynomial_reindex_ne_zero_ae (n*n) finProdFinEquiv
      (congruenceMinorPolynomial D j hj) hp
    obtain ⟨g,hg⟩ := hg.exists
    have hvalue : ambientMinorValue D j hj g≠0 := by
      rwa [congruenceMinorPolynomial_eval D (gaussianSquareMatrix n g) j hj] at hg
    by_contra! hnone
    have hdense : DenseRange (fun q : Fin (n*n) → ℚ => fun i => (q i:ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    have hc : Continuous (fun g => ambientMinorValue D j hj g) :=
      (ambientMinorValue_continuous j hj).comp (continuous_const.prodMk continuous_id)
    have he : (fun g => ambientMinorValue D j hj g)=(fun _ => (0:ℝ)) :=
      hdense.equalizer hc continuous_const (funext hnone)
    exact hvalue (congrFun he g)

def jointInertiaGood (D : Core n) (g : Fin (n*n) → ℝ) : Prop :=
  ∀ j : Fin (n+1), ambientMinorActive D j.val (by omega) →
    ambientMinorValue D j.val (by omega) g≠0

theorem jointInertiaGood_measurable :
    MeasurableSet {z : Core n × (Fin (n*n) → ℝ) | jointInertiaGood z.1 z.2} := by
  apply measurableSet_all
  intro j
  have ha : MeasurableSet {z : Core n × (Fin (n*n) → ℝ) |
      ambientMinorActive z.1 j.val (by omega)} := by
    apply measurableSet_exists
    intro q
    have hc := (ambientMinorValue_continuous j.val (by omega)).comp
      (continuous_fst.prodMk (continuous_const (b := fun i => (q i:ℝ))))
    exact (isOpen_ne hc continuous_const).measurableSet
  have hb : MeasurableSet {z : Core n × (Fin (n*n) → ℝ) |
      ambientMinorValue z.1 j.val (by omega) z.2≠0} :=
    (isOpen_ne (ambientMinorValue_continuous j.val (by omega)) continuous_const).measurableSet
  simpa only [imp_iff_not_or] using ha.compl.union hb

theorem jointInertiaGood_polynomial_event (D : Core n) (g : Fin (n*n) → ℝ)
    (hg : jointInertiaGood D g) :
    ∀ j : ℕ, ∀ hj : j≤n, congruenceMinorPolynomial D j hj≠0 →
      MvPolynomial.eval (fun x : Fin n × Fin n => g (finProdFinEquiv x))
        (congruenceMinorPolynomial D j hj)≠0 := by
  intro j hj hp
  have h := hg ⟨j,by omega⟩ ((ambientMinorActive_iff D j hj).mpr hp)
  rwa [congruenceMinorPolynomial_eval D (gaussianSquareMatrix n g) j hj]

theorem jointInertiaGood_ae (D : Core n) :
    ∀ᵐ g ∂gaussianVector (n*n), jointInertiaGood D g := by
  apply ae_all_iff.mpr
  intro j
  by_cases hp : congruenceMinorPolynomial D j.val (by omega)=0
  · exact Filter.Eventually.of_forall (fun g h =>
      False.elim (((ambientMinorActive_iff D j.val (by omega)).mp h) hp))
  · have hg := gaussian_polynomial_reindex_ne_zero_ae (n*n) finProdFinEquiv
      (congruenceMinorPolynomial D j.val (by omega)) hp
    filter_upwards [hg] with g hg
    intro _
    rwa [congruenceMinorPolynomial_eval D (gaussianSquareMatrix n g) j.val (by omega)] at hg

end
end HierarchicalAbsoluteSpectral
