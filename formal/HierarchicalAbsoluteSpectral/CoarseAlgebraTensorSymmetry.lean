import HierarchicalAbsoluteSpectral.FastKernels

/-! Cyclic symmetry of actual integer matrix-tensor decompositions.
This rotates certified inner-wide schemes to output-wide schemes without
postulating a multiplication exponent or a new algorithmic primitive. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matmul.IntegerBilinear Matmul.UniversalRecursiveAlgorithm
open OAI.MatrixMultiplication.Foundation

def rotateMatrixScheme {a b c ρ : ℕ} (alg : Scheme a b c ρ) : Scheme c a b ρ where
  left := alg.output
  right := alg.left
  output := alg.right

theorem rotateMatrixScheme_tensor {a b c ρ : ℕ} (alg : Scheme a b c ρ)
    (x : Fin c × Fin a) (y : Fin a × Fin b) (z : Fin b × Fin c) :
    (rotateMatrixScheme alg).tensor x y z = alg.tensor y z x := by
  simp only [Algorithm.tensor,rotateMatrixScheme,Tensor.rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rotateMatrixScheme_correct {a b c ρ : ℕ} (alg : Scheme a b c ρ)
    (h : alg.tensor = matrixTensor a b c) :
    (rotateMatrixScheme alg).tensor = matrixTensor c a b := by
  funext x y z
  rw [rotateMatrixScheme_tensor,h]
  simp only [matrixTensor,and_assoc,and_left_comm,and_comm]

theorem rotate_blockVolume (a b c : ℕ) :
    Matmul.RecursiveCost.blockVolume c a b = Matmul.RecursiveCost.blockVolume a b c := by
  simp only [Matmul.RecursiveCost.blockVolume,Nat.mul_comm c a,Nat.mul_comm c b]
  omega

structure OuterSchemeCertificate (κ E : ℝ) where
  a : ℕ
  b : ℕ
  ρ : ℕ
  alg : Scheme a a b ρ
  a_ge_two : 2 ≤ a
  b_pos : 0 < b
  correct : alg.tensor = matrixTensor a a b
  shape : (a:ℝ)^κ ≤ (b:ℝ)
  volume : Matmul.RecursiveCost.blockVolume a a b ≤ ρ
  rankExponent_lt : Real.log (ρ:ℝ)/Real.log (a:ℝ) < E

theorem exists_outer_scheme_certificate (κ ζ : ℝ) (hκ : 0 ≤ κ) (hζ : 0 < ζ) :
    Nonempty (OuterSchemeCertificate κ (Matmul.RectangularOptimization.rectangularBound κ+ζ)) := by
  obtain ⟨cert⟩ := Matmul.RectangularRankBridge.exists_scheme_certificate hκ hζ
  exact ⟨{
    a := cert.a
    b := cert.b
    ρ := cert.ρ
    alg := rotateMatrixScheme cert.alg
    a_ge_two := cert.a_ge_two
    b_pos := cert.b_pos
    correct := rotateMatrixScheme_correct cert.alg cert.correct
    shape := cert.shape
    volume := by rw [rotate_blockVolume]; exact cert.volume
    rankExponent_lt := cert.rankExponent_lt }⟩

end
end HierarchicalAbsoluteSpectral
