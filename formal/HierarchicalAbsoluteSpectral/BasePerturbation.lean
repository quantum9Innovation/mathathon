import HierarchicalAbsoluteSpectral.NewtonMatrix
import HierarchicalAbsoluteSpectral.StrongAction

/-! The actual finite Newton metric tolerates the noncommuting normalized
sketch error and satisfies the complete coarse ordinary-defect invariant. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k : ℕ}

theorem selfAdjoint_bounds_of_norm (E : Core k) (hE : E.IsHermitian) (a : ℝ)
    (_ha : 0 ≤ a) (hnorm : ‖E‖ ≤ a) : -(a • (1 : Core k)) ≤ E ∧ E ≤ a • (1 : Core k) := by
  cases k with
  | zero => constructor <;> exact le_of_eq (Subsingleton.elim _ _)
  | succ k =>
    have hs (x : ℝ) (hx : x ∈ spectrum ℝ E) : -a ≤ x ∧ x ≤ a := by
      have hb := (spectrum.norm_le_norm_of_mem hx).trans hnorm
      rw [Real.norm_eq_abs] at hb
      exact abs_le.mp hb
    have hl := (algebraMap_le_iff_le_spectrum (p := IsSelfAdjoint) hE).mpr
      (fun x hx => (hs x hx).1)
    have hu := (le_algebraMap_iff_spectrum_le (p := IsSelfAdjoint) hE).mpr
      (fun x hx => (hs x hx).2)
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using And.intro hl hu

theorem symmetric_cross_bound (F S E : Core k) (hF : F.PosDef) (hS : Sᵀ = S) (hE : Eᵀ = E)
    (a : ℝ) (ha : 0 ≤ a) (hnorm : ‖E‖ ≤ a) (hcontract : ‖S*F⁻¹‖ ≤ 1) :
    -(2*a) • (1 : Core k) ≤ S*F⁻¹*E+E*F⁻¹*S := by
  have hFi : (F⁻¹)ᵀ = F⁻¹ := hF.inv.isHermitian.eq
  have hcontra : ‖F⁻¹*S‖ ≤ 1 := by
    have heq : (S*F⁻¹)ᵀ = F⁻¹*S := by rw [Matrix.transpose_mul, hFi, hS]
    rw [← heq, spectral_norm_transpose]
    exact hcontract
  have hC : (S*F⁻¹*E+E*F⁻¹*S).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, hFi, hS, hE, Matrix.mul_assoc, add_comm]
  have hCE : ‖S*F⁻¹*E‖ ≤ a := by
    apply (norm_mul_le _ _).trans
    exact (mul_le_mul hcontract hnorm (norm_nonneg _) (by norm_num)).trans (by simp)
  have hEC : ‖E*F⁻¹*S‖ ≤ a := by
    rw [Matrix.mul_assoc]
    apply (norm_mul_le _ _).trans
    exact (mul_le_mul hnorm hcontra (norm_nonneg _) ha).trans (by simp)
  have hnormC : ‖S*F⁻¹*E+E*F⁻¹*S‖ ≤ 2*a :=
    (norm_add_le _ _).trans (by linarith)
  simpa only [neg_smul] using (selfAdjoint_bounds_of_norm _ hC (2*a) (by positivity) hnormC).1

theorem finite_base_normalized (S E : Core k) (hS : S.IsHermitian) (hE : E.IsHermitian)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/64)
    (hspec : ∀ x ∈ spectrum ℝ S, -1 ≤ x ∧ x ≤ 1) (hEnorm : ‖E‖ ≤ 2*h) :
    let F := baseNewtonMetric S h (baseNewtonSteps h hh)
    F.PosDef ∧ (8*h) • (1 : Core k) ≤ F ∧ F ≤ (2:ℝ) • (1 : Core k) ∧
      (6*h) • (1 : Core k) ≤ F-(S+E) ∧ (6*h) • (1 : Core k) ≤ F+(S+E) ∧
      (F-(S+E)).PosDef ∧ (F+(S+E)).PosDef ∧
      (0 : Core k) ≤ F-(S+E)*F⁻¹*(S+E) ∧
      F-(S+E)*F⁻¹*(S+E) ≤ (36*h) • (1 : Core k) := by
  let F := baseNewtonMetric S h (baseNewtonSteps h hh)
  have hn := baseNewtonSteps_accuracy h hh
  have hF : F.PosDef := baseNewtonMetric_posDef S hS h hh _
  have hb := baseNewtonMetric_bounds S hS h _ hh hh' hspec hn
  have hd := baseNewtonMetric_defect S hS h _ hh hh' hspec hn
  have hc := baseNewtonMetric_contraction S hS h _ hh hh' hspec hn
  have hEband := selfAdjoint_bounds_of_norm E hE (2*h) (by positivity) hEnorm
  have hminus : (6*h) • (1 : Core k) ≤ F-(S+E) := by
    convert sub_le_sub hb.2.2.1 hEband.2 using 1 <;> module
  have hplus : (6*h) • (1 : Core k) ≤ F+(S+E) := by
    have hsum := add_le_add hb.2.2.2 hEband.1
    convert hsum using 1 <;> module
  have hfloor : ((6*h) • (1 : Core k)).PosDef := Matrix.PosDef.one.smul (by positivity)
  have hminusPD : (F-(S+E)).PosDef := by
    simpa using hfloor.add_posSemidef (show (F-(S+E)-(6*h) • (1 : Core k)).PosSemidef from hminus)
  have hplusPD : (F+(S+E)).PosDef := by
    simpa using hfloor.add_posSemidef (show (F+(S+E)-(6*h) • (1 : Core k)).PosSemidef from hplus)
  have hSt : Sᵀ = S := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.eq
  have hEt : Eᵀ = E := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hE.eq
  have hK : (S+E)ᵀ = S+E := by simp [hSt, hEt]
  have hKlo : -F ≤ S+E := by
    have hp : (F+(S+E)).PosSemidef := hplusPD.posSemidef
    simpa only [Matrix.le_iff, sub_neg_eq_add, add_comm] using hp
  have hKup : S+E ≤ F := hminusPD.posSemidef
  have hsq := weighted_error_square F (S+E) 1 hF hK (by norm_num)
    (by simpa using hKlo) (by simpa using hKup)
  have hlow : (0 : Core k) ≤ F-(S+E)*F⁻¹*(S+E) := by simpa using hsq
  have hcross := symmetric_cross_bound F S E hF hSt hEt (2*h)
    (by positivity) hEnorm hc
  have hEE : (E*F⁻¹*E).PosSemidef := by
    simpa only [hE.eq] using hF.posSemidef.inv.conjTranspose_mul_mul_same E
  have hupp : F-(S+E)*F⁻¹*(S+E) ≤ (36*h) • (1 : Core k) := by
    calc
      _ = (F-S*F⁻¹*S)-(S*F⁻¹*E+E*F⁻¹*S)-E*F⁻¹*E := by noncomm_ring
      _ ≤ (F-S*F⁻¹*S)-(S*F⁻¹*E+E*F⁻¹*S) := sub_le_self _ hEE.nonneg
      _ ≤ (32*h) • (1 : Core k)-(-(2*(2*h)) • (1 : Core k)) := sub_le_sub hd.2 hcross
      _ = _ := by module
  exact ⟨hF, hb.1, hb.2.1, hminus, hplus, hminusPD, hplusPD, hlow, hupp⟩

end
end HierarchicalAbsoluteSpectral
