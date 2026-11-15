import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftProgram
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftInertia
import HierarchicalAbsoluteSpectral.CoarseAlgebraGaussianInertia
import HierarchicalAbsoluteSpectral.JointInertiaEvent
import HierarchicalAbsoluteSpectral.ProbabilityJointInertiaProgram

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem exactGramAppendixLift_regular_of_jointGood {k : ℕ}
    (K : Core k) (hK : Kᵀ = K) (hdet : IsUnit K.det) (g : Fin (k*k) → ℝ)
    (hg : jointInertiaGood K g) :
    LeadingPrincipalRegular ((gaussianSquareMatrix k g)ᵀ*K*gaussianSquareMatrix k g) := by
  have hHerm : K.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hK
  have hSymm : K.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  intro j hj
  apply isUnit_iff_ne_zero.mpr
  rw [← congruenceMinorPolynomial_eval]
  exact jointInertiaGood_polynomial_event K g hg j hj
    (congruenceMinorPolynomial_ne_zero K hSymm hdet j hj)

def exactGramAppendixRandomLiftProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (K : Core k) (hK : Kᵀ = K)
    (hnegative : ∀ out : FiniteCongruenceDiagonal K, out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) : ArithmeticProgram (Option (FixedRankOutput n p r)) := do
  let diag? ← congruenceInertiaProgram kernels K hK (gaussianSquareMatrix k g)
  match diag? with
  | none => ArithmeticProgram.pure none
  | some out => do
    let result ← exactGramAppendixLiftProgram kernels A B T out (hnegative out)
    ArithmeticProgram.pure (some result)

theorem exactGramAppendixRandomLiftProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (K : Core k) (hK : Kᵀ = K)
    (hnegative : ∀ out : FiniteCongruenceDiagonal K, out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) : (exactGramAppendixRandomLiftProgram kernels A B T K hK hnegative g).admissible := by
  simp only [exactGramAppendixRandomLiftProgram, admissible_bind,
    congruenceInertiaProgram_admissible, true_and]
  split
  · trivial
  · simp only [admissible_bind, exactGramAppendixLiftProgram_admissible, admissible_pure, and_self]

theorem exactGramAppendixRandomLiftProgram_success
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (K : Core k) (hK : Kᵀ = K)
    (hnegative : ∀ out : FiniteCongruenceDiagonal K, out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ)
    (hregular : LeadingPrincipalRegular ((gaussianSquareMatrix k g)ᵀ*K*gaussianSquareMatrix k g)) :
    ∃ result, (exactGramAppendixRandomLiftProgram kernels A B T K hK hnegative g).eval = some result := by
  obtain ⟨out,ho⟩ := congruenceInertiaProgram_success kernels K hK (gaussianSquareMatrix k g) hregular
  rw [exactGramAppendixRandomLiftProgram, eval_bind, ho, eval_bind, eval_pure]
  exact ⟨_,rfl⟩

theorem exactGramAppendixRandomLiftProgram_success_of_jointGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (K : Core k) (hK : Kᵀ = K)
    (hnegative : ∀ out : FiniteCongruenceDiagonal K, out.negativeCount ≤ r)
    (hdet : IsUnit K.det) (g : Fin (k*k) → ℝ) (hg : jointInertiaGood K g) :
    ∃ result, (exactGramAppendixRandomLiftProgram kernels A B T K hK hnegative g).eval = some result :=
  exactGramAppendixRandomLiftProgram_success kernels A B T K hK hnegative g
    (exactGramAppendixLift_regular_of_jointGood K hK hdet g hg)

theorem exactGramAppendixRandomLiftProgram_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (K : Core k) (hK : Kᵀ = K)
    (hnegative : ∀ out : FiniteCongruenceDiagonal K, out.negativeCount ≤ r) (hdet : IsUnit K.det) :
    ∀ᵐ g ∂gaussianVector (k*k),
      ∃ result, (exactGramAppendixRandomLiftProgram kernels A B T K hK hnegative g).eval = some result := by
  filter_upwards [jointInertiaGood_ae K] with g hg
  exact exactGramAppendixRandomLiftProgram_success_of_jointGood kernels A B T K hK hnegative hdet g hg

theorem exactGramAppendixRandomLiftProgram_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (t : ℝ) (ht : 0 ≤ t)
    (hZ : (A*T)ᵀ*(A*T) = 1) (hcov : (A*B)*(A*B)ᵀ = (A*T)*Hc*(A*T)ᵀ)
    (hK : (t • (1 : Core k)-Hc)ᵀ = t • (1 : Core k)-Hc)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) (result : FixedRankOutput n p r)
    (hresult : (exactGramAppendixRandomLiftProgram kernels A B T (t • (1 : Core k)-Hc)
      hK hnegative g).eval = some result) :
    ‖A*B-result.product‖ ≤ Real.sqrt t := by
  unfold exactGramAppendixRandomLiftProgram at hresult
  rw [eval_bind] at hresult
  split at hresult
  · simp at hresult
  · simp only [eval_bind, eval_pure, Option.some.injEq] at hresult
    rw [← hresult]
    exact exactGramAppendixLiftProgram_error kernels A B T Hc t ht hZ hcov _ _

local instance appendixLiftMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance appendixLiftMatrixBorelSpace (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

theorem exactGramAppendixLift_jointGood_measurable {k : ℕ}
    (Hc : Core k) (time : ℝ → ℝ) (hTime : Continuous time) :
    MeasurableSet {z : ℝ × (Fin (k*k) → ℝ) |
      jointInertiaGood (time z.1 • (1 : Core k)-Hc) z.2} := by
  have hshift : Continuous (fun x : ℝ => time x • (1 : Core k)-Hc) :=
    (hTime.smul continuous_const).sub continuous_const
  exact jointInertiaGood_measurable_comp
    (fun z : ℝ × (Fin (k*k) → ℝ) => time z.1 • (1 : Core k)-Hc) Prod.snd
    (hshift.comp continuous_fst).measurable measurable_snd

theorem exactGramAppendixLift_jointGood_ae {k : ℕ}
    (Hc : Core k) (time : ℝ → ℝ) (hTime : Continuous time) :
    ∀ᵐ z ∂(gaussianReal 0 1).prod (gaussianVector (k*k)),
      jointInertiaGood (time z.1 • (1 : Core k)-Hc) z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (exactGramAppendixLift_jointGood_measurable Hc time hTime)).mpr
  exact Filter.Eventually.of_forall (fun x => jointInertiaGood_ae (time x • (1 : Core k)-Hc))

theorem exactGramAppendixLift_jointCongruence_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {k : ℕ} (Hc : Core k) (hHc : Hc.IsHermitian)
    (time : ℝ → ℝ) (hTime : Continuous time)
    (hdet : ∀ᵐ x ∂gaussianReal 0 1, IsUnit (time x • (1 : Core k)-Hc).det) :
    ∀ᵐ z ∂(gaussianReal 0 1).prod (gaussianVector (k*k)),
      ∃ out, (congruenceInertiaProgram kernels (time z.1 • (1 : Core k)-Hc)
        (by
          have hsym : Hcᵀ = Hc := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hHc.eq
          simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsym])
        (gaussianSquareMatrix k z.2)).eval = some out := by
  have hdetProd : ∀ᵐ z ∂(gaussianReal 0 1).prod (gaussianVector (k*k)),
      IsUnit (time z.1 • (1 : Core k)-Hc).det := by
    exact (measurePreserving_fst (μ := gaussianReal 0 1) (ν := gaussianVector (k*k))).quasiMeasurePreserving.ae hdet
  filter_upwards [exactGramAppendixLift_jointGood_ae Hc time hTime, hdetProd] with z hz hd
  have hsym : Hcᵀ = Hc := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hHc.eq
  have hshift : (time z.1 • (1 : Core k)-Hc)ᵀ = time z.1 • (1 : Core k)-Hc := by
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsym]
  exact congruenceInertiaProgram_success kernels _ hshift (gaussianSquareMatrix k z.2)
    (exactGramAppendixLift_regular_of_jointGood _ hshift hd z.2 hz)

end
end HierarchicalAbsoluteSpectral
