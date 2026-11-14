import HierarchicalAbsoluteSpectral.InverseMetric
import HierarchicalAbsoluteSpectral.Refinement
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

set_option backward.isDefEq.respectTransparency false

/-!
Construction and verification of the analytical ideal absolute-root metric in
Lemma 5. The spectral calculus in this file is used in the proof only. The
algorithmic polynomial replacement is a separate construction.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder
variable {k : ℕ}

def absoluteRootScalar (η x : ℝ) : ℝ := Real.sqrt (x^2 + η^2) + η

def absoluteRootMatrix (A : Core k) (η : ℝ) : Core k :=
  cfc (p := IsSelfAdjoint) (absoluteRootScalar η) A

theorem scalar_absolute_root_pos (η x : ℝ) (hη : 0 < η) :
    0 < absoluteRootScalar η x := by
  unfold absoluteRootScalar
  positivity

theorem scalar_absolute_root_floor (η x : ℝ) (_hη : 0 ≤ η) :
    2 * η ≤ absoluteRootScalar η x := by
  have hsq := Real.sq_sqrt (show 0 ≤ x^2 + η^2 by positivity)
  have hp := Real.sqrt_nonneg (x^2 + η^2)
  unfold absoluteRootScalar
  nlinarith [sq_nonneg x]

theorem scalar_absolute_root_upper (η x : ℝ) (hη : 0 ≤ η)
    (hx : -1 ≤ x) (hx' : x ≤ 1) :
    absoluteRootScalar η x ≤ 1 + 2*η := by
  have hsq := Real.sq_sqrt (show 0 ≤ x^2 + η^2 by positivity)
  have hp := Real.sqrt_nonneg (x^2 + η^2)
  unfold absoluteRootScalar
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1-x) (by linarith : 0 ≤ 1+x)]

theorem scalar_absolute_root_margin (η x : ℝ) :
    |x| + η ≤ absoluteRootScalar η x := by
  have hsq := Real.sq_sqrt (show 0 ≤ x^2 + η^2 by positivity)
  have hp := Real.sqrt_nonneg (x^2 + η^2)
  have hx := abs_nonneg x
  have hx2 := sq_abs x
  unfold absoluteRootScalar
  nlinarith [sq_nonneg η]

theorem finite_spectrum_continuous (A : Core k) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f

theorem absoluteRootMatrix_posDef (A : Core k) (hA : A.IsHermitian)
    (η : ℝ) (hη : 0 < η) : (absoluteRootMatrix A η).PosDef := by
  apply Matrix.IsStrictlyPositive.posDef
  apply (cfc_isStrictlyPositive_iff (p := IsSelfAdjoint) (absoluteRootScalar η) A
    (finite_spectrum_continuous A _) hA).mpr
  intro x hx
  exact scalar_absolute_root_pos η x hη

theorem absoluteRootMatrix_floor (A : Core k) (hA : A.IsHermitian)
    (η : ℝ) (hη : 0 ≤ η) :
    (2*η) • (1 : Core k) ≤ absoluteRootMatrix A η := by
  simpa [absoluteRootMatrix, Algebra.algebraMap_eq_smul_one] using
    algebraMap_le_cfc (p := IsSelfAdjoint) (absoluteRootScalar η) (2*η) A
      (fun x _ => scalar_absolute_root_floor η x hη)
      (finite_spectrum_continuous A _) hA

theorem absoluteRootMatrix_upper (A : Core k) (hA : A.IsHermitian)
    (η : ℝ) (hη : 0 ≤ η)
    (hspec : ∀ x ∈ spectrum ℝ A, -1 ≤ x ∧ x ≤ 1) :
    absoluteRootMatrix A η ≤ (1+2*η) • (1 : Core k) := by
  simpa [absoluteRootMatrix, Algebra.algebraMap_eq_smul_one] using
    cfc_le_algebraMap (p := IsSelfAdjoint) (absoluteRootScalar η) (1+2*η) A
      (fun x hx => scalar_absolute_root_upper η x hη (hspec x hx).1 (hspec x hx).2)
      (finite_spectrum_continuous A _) hA

theorem absoluteRootMatrix_defect (A : Core k) (hA : A.IsHermitian)
    (η : ℝ) (hη : 0 < η) :
    absoluteRootMatrix A η - A * (absoluteRootMatrix A η)⁻¹ * A =
      (2*η) • (1 : Core k) := by
  have hinv : cfc (p := IsSelfAdjoint) (fun x => (absoluteRootScalar η x)⁻¹) A =
      (absoluteRootMatrix A η)⁻¹ := by
    simpa [absoluteRootMatrix, Matrix.nonsing_inv_eq_ringInverse] using
      cfc_inv (p := IsSelfAdjoint) (absoluteRootScalar η) A
        (fun x _ => (scalar_absolute_root_pos η x hη).ne')
        (finite_spectrum_continuous A _) hA
  have hmul : A * (absoluteRootMatrix A η)⁻¹ * A =
      cfc (p := IsSelfAdjoint) (fun x => x * (absoluteRootScalar η x)⁻¹ * x) A := by
    rw [cfc_mul (p := IsSelfAdjoint) _ _ A (finite_spectrum_continuous A _)
      (finite_spectrum_continuous A _)]
    rw [cfc_mul (p := IsSelfAdjoint) _ _ A (finite_spectrum_continuous A _)
      (finite_spectrum_continuous A _), cfc_id' (p := IsSelfAdjoint) ℝ A hA, hinv]
  rw [hmul]
  change cfc (p := IsSelfAdjoint) (absoluteRootScalar η) A - _ = _
  rw [← cfc_sub (p := IsSelfAdjoint) (absoluteRootScalar η) (fun x => x * (absoluteRootScalar η x)⁻¹ * x) A
    (finite_spectrum_continuous A _) (finite_spectrum_continuous A _)]
  calc
    _ = cfc (p := IsSelfAdjoint) (fun _ : ℝ => 2*η) A := by
      apply cfc_congr (p := IsSelfAdjoint)
      intro x hx
      have hi := absolute_root_defect x η hη
      simpa [absoluteRootScalar, div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm] using hi
    _ = (2*η) • (1 : Core k) := by
      rw [cfc_const (p := IsSelfAdjoint) _ _ hA, Algebra.algebraMap_eq_smul_one]

def idealMetric (R K : Core k) (η : ℝ) : Core k :=
  (R⁻¹)ᵀ * absoluteRootMatrix (Rᵀ * K * R) η * R⁻¹

theorem normalized_isHermitian (R K : Core k) (hK : Kᵀ = K) :
    (Rᵀ * K * R).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_mul, hK, Matrix.mul_assoc]

theorem idealMetric_posDef (R K : Core k) (hR : IsUnit R.det) (hK : Kᵀ = K)
    (η : ℝ) (hη : 0 < η) : (idealMetric R K η).PosDef := by
  have hp := absoluteRootMatrix_posDef (Rᵀ * K * R) (normalized_isHermitian R K hK) η hη
  have hi : Function.Injective (R⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_iff_isUnit_det R).mpr hR))
  simpa [idealMetric] using hp.conjTranspose_mul_mul_same hi

/-- The root identity in Lemma 5 for the constructed metric, not a hypothesis. -/
theorem idealMetric_defect (R K : Core k) (hR : IsUnit R.det) (hK : Kᵀ = K)
    (η : ℝ) (hη : 0 < η) :
    idealMetric R K η - K * (idealMetric R K η)⁻¹ * K =
      (2*η) • inverseMetric R := by
  have hRi := Matrix.isUnit_nonsing_inv_det R hR
  have hA := normalized_isHermitian R K hK
  have hroot := absoluteRootMatrix_defect (Rᵀ * K * R) hA η hη
  have hcong := congruence_defect R⁻¹ (Rᵀ * K * R)
    (absoluteRootMatrix (Rᵀ * K * R) η) hRi
  rw [inverseMetric_congruence R K hR] at hcong
  simpa [idealMetric, hroot, Matrix.mul_smul, Matrix.smul_mul, inverseMetric] using hcong

theorem idealMetric_floor (R K : Core k) (hK : Kᵀ = K)
    (η : ℝ) (hη : 0 ≤ η) :
    (2*η) • inverseMetric R ≤ idealMetric R K η := by
  have hroot := absoluteRootMatrix_floor (Rᵀ * K * R)
    (normalized_isHermitian R K hK) η hη
  have hc := star_left_conjugate_le_conjugate hroot R⁻¹
  simpa [idealMetric, inverseMetric, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_smul, Matrix.smul_mul] using hc

theorem idealMetric_upper (R K : Core k) (hK : Kᵀ = K)
    (η : ℝ) (hη : 0 ≤ η)
    (hspec : ∀ x ∈ spectrum ℝ (Rᵀ * K * R), -1 ≤ x ∧ x ≤ 1) :
    idealMetric R K η ≤ (1+2*η) • inverseMetric R := by
  have hroot := absoluteRootMatrix_upper (Rᵀ * K * R)
    (normalized_isHermitian R K hK) η hη hspec
  have hc := star_left_conjugate_le_conjugate hroot R⁻¹
  simpa [idealMetric, inverseMetric, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_smul, Matrix.smul_mul] using hc

theorem normalized_spectrum_of_bounds (R K : Core k) (hR : IsUnit R.det)
    (hK : Kᵀ = K) (hlower : -inverseMetric R ≤ K) (hupper : K ≤ inverseMetric R) :
    ∀ x ∈ spectrum ℝ (Rᵀ * K * R), -1 ≤ x ∧ x ≤ 1 := by
  have hA := normalized_isHermitian R K hK
  have hlo := star_left_conjugate_le_conjugate hlower R
  have hup := star_left_conjugate_le_conjugate hupper R
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_neg, Matrix.neg_mul, inverseMetric_normalized R hR] at hlo hup
  have hspecLo := (algebraMap_le_iff_le_spectrum (R := ℝ) (A := Core k)
    (p := IsSelfAdjoint) (a := Rᵀ * K * R) (r := (-1 : ℝ)) hA).mp
    (by simpa [Algebra.algebraMap_eq_smul_one] using hlo)
  have hspecUp := (CFC.le_one_iff (R := ℝ) (A := Core k)
    (p := IsSelfAdjoint) (Rᵀ * K * R) hA).mp hup
  exact fun x hx => ⟨hspecLo x hx, hspecUp x hx⟩

theorem absoluteRootMatrix_sub_margin (A : Core k) (hA : A.IsHermitian) (η : ℝ) :
    η • (1 : Core k) ≤ absoluteRootMatrix A η - A := by
  have hs : ∀ x : ℝ, η ≤ absoluteRootScalar η x - x := by
    intro x
    have hm := scalar_absolute_root_margin η x
    have hx := le_abs_self x
    linarith
  have hm := algebraMap_le_cfc (p := IsSelfAdjoint)
    (fun x => absoluteRootScalar η x - x) η A (fun x _ => hs x)
    (finite_spectrum_continuous A _) hA
  rw [cfc_sub _ _ A (finite_spectrum_continuous A _) (finite_spectrum_continuous A _),
    cfc_id' (p := IsSelfAdjoint) ℝ A hA] at hm
  simpa [absoluteRootMatrix, Algebra.algebraMap_eq_smul_one] using hm

theorem absoluteRootMatrix_add_margin (A : Core k) (hA : A.IsHermitian) (η : ℝ) :
    η • (1 : Core k) ≤ absoluteRootMatrix A η + A := by
  have hs : ∀ x : ℝ, η ≤ absoluteRootScalar η x + x := by
    intro x
    have hm := scalar_absolute_root_margin η x
    have hx := neg_le_abs x
    linarith
  have hm := algebraMap_le_cfc (p := IsSelfAdjoint)
    (fun x => absoluteRootScalar η x + x) η A (fun x _ => hs x)
    (finite_spectrum_continuous A _) hA
  rw [cfc_add (p := IsSelfAdjoint) (a := A) _ _ (finite_spectrum_continuous A _)
    (finite_spectrum_continuous A _), cfc_id' (p := IsSelfAdjoint) ℝ A hA] at hm
  simpa [absoluteRootMatrix, Algebra.algebraMap_eq_smul_one] using hm

theorem idealMetric_sub_margin (R K : Core k) (hR : IsUnit R.det) (hK : Kᵀ = K)
    (η : ℝ) : η • inverseMetric R ≤ idealMetric R K η - K := by
  have hm := absoluteRootMatrix_sub_margin (Rᵀ * K * R) (normalized_isHermitian R K hK) η
  have hc := star_left_conjugate_le_conjugate hm R⁻¹
  simpa [idealMetric, inverseMetric, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, inverseMetric_congruence R K hR] using hc

theorem idealMetric_add_margin (R K : Core k) (hR : IsUnit R.det) (hK : Kᵀ = K)
    (η : ℝ) : η • inverseMetric R ≤ idealMetric R K η + K := by
  have hm := absoluteRootMatrix_add_margin (Rᵀ * K * R) (normalized_isHermitian R K hK) η
  have hc := star_left_conjugate_le_conjugate hm R⁻¹
  simpa [idealMetric, inverseMetric, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, inverseMetric_congruence R K hR] using hc

end
end HierarchicalAbsoluteSpectral
