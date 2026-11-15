import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

namespace StructuralDefects

open Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def portResponse (D : Matrix ι ι ℝ) [Invertible D] (b : ι → ℝ) : ℝ :=
  b ⬝ᵥ (⅟D *ᵥ b)

def portProfile (D : Matrix ι ι ℝ) [Invertible D] (b : ι → ℝ) : ι → ℝ :=
  (portResponse D b)⁻¹ • (⅟D *ᵥ b)

def portRemainder (D : Matrix ι ι ℝ) [Invertible D] (b y : ι → ℝ) : ι → ℝ :=
  y - (b ⬝ᵥ y) • portProfile D b

theorem portProfile_equation (D : Matrix ι ι ℝ) [Invertible D] (b : ι → ℝ) :
    D *ᵥ portProfile D b = (portResponse D b)⁻¹ • b := by
  simp only [portProfile, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    mul_invOf_self, Matrix.one_mulVec]

theorem portProfile_boundary (D : Matrix ι ι ℝ) [Invertible D] (b : ι → ℝ)
    (hf : portResponse D b ≠ 0) :
    b ⬝ᵥ portProfile D b = 1 := by
  simp only [portProfile, dotProduct_smul, smul_eq_mul]
  exact inv_mul_cancel₀ hf

theorem portRemainder_boundary (D : Matrix ι ι ℝ) [Invertible D] (b y : ι → ℝ)
    (hf : portResponse D b ≠ 0) :
    b ⬝ᵥ portRemainder D b y = 0 := by
  simp [portRemainder, dotProduct_sub, dotProduct_smul, portProfile_boundary D b hf]

theorem port_decomposition (D : Matrix ι ι ℝ) [Invertible D] (b y : ι → ℝ) :
    y = (b ⬝ᵥ y) • portProfile D b + portRemainder D b y := by
  simp [portRemainder]

theorem port_energy_orthogonal (D : Matrix ι ι ℝ) [Invertible D]
    (hD : D.transpose = D) (b w : ι → ℝ) (hw : b ⬝ᵥ w = 0) :
    portProfile D b ⬝ᵥ (D *ᵥ w) = 0 := by
  calc
    portProfile D b ⬝ᵥ (D *ᵥ w) = w ⬝ᵥ (D *ᵥ portProfile D b) := by
      simpa only [hD] using dotProduct_transpose_mulVec D (portProfile D b) w
    _ = 0 := by rw [portProfile_equation, dotProduct_smul, dotProduct_comm, hw, smul_zero]

theorem portProfile_energy (D : Matrix ι ι ℝ) [Invertible D] (b : ι → ℝ)
    (hf : portResponse D b ≠ 0) :
    portProfile D b ⬝ᵥ (D *ᵥ portProfile D b) = (portResponse D b)⁻¹ := by
  rw [portProfile_equation, dotProduct_smul, dotProduct_comm,
    portProfile_boundary D b hf, smul_eq_mul, mul_one]

theorem port_energy_split (D : Matrix ι ι ℝ) [Invertible D]
    (hD : D.transpose = D) (b w : ι → ℝ)
    (hf : portResponse D b ≠ 0) (hw : b ⬝ᵥ w = 0) (t : ℝ) :
    (t • portProfile D b + w) ⬝ᵥ (D *ᵥ (t • portProfile D b + w)) =
      (portResponse D b)⁻¹ * t ^ 2 + w ⬝ᵥ (D *ᵥ w) := by
  have hcross : w ⬝ᵥ (D *ᵥ portProfile D b) = 0 := by
    rw [portProfile_equation, dotProduct_smul, dotProduct_comm, hw, smul_zero]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, portProfile_energy D b hf,
    port_energy_orthogonal D hD b w hw, hcross, smul_eq_mul]
  ring

theorem actual_port_energy_decomposition (D : Matrix ι ι ℝ) [Invertible D]
    (hD : D.transpose = D) (b y : ι → ℝ) (hf : portResponse D b ≠ 0) :
    y ⬝ᵥ (D *ᵥ y) = (portResponse D b)⁻¹ * (b ⬝ᵥ y) ^ 2 +
      portRemainder D b y ⬝ᵥ (D *ᵥ portRemainder D b y) := by
  have h := port_energy_split D hD b (portRemainder D b y) hf
    (portRemainder_boundary D b y hf) (b ⬝ᵥ y)
  rwa [← port_decomposition D b y] at h

theorem portProfile_nonzero (D : Matrix ι ι ℝ) [Invertible D] (b : ι → ℝ)
    (hf : portResponse D b ≠ 0) : portProfile D b ≠ 0 := by
  intro h
  have hb := portProfile_boundary D b hf
  rw [h, dotProduct_zero] at hb
  exact zero_ne_one hb

theorem portProfile_gram (D : Matrix ι ι ℝ) [Invertible D] (b : ι → ℝ) :
    portProfile D b ⬝ᵥ portProfile D b =
      (portResponse D b)⁻¹ ^ 2 * ((⅟D *ᵥ b) ⬝ᵥ (⅟D *ᵥ b)) := by
  simp only [portProfile, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

#print axioms portProfile_equation
#print axioms portProfile_boundary
#print axioms portRemainder_boundary
#print axioms port_decomposition
#print axioms port_energy_orthogonal
#print axioms portProfile_energy
#print axioms port_energy_split
#print axioms actual_port_energy_decomposition
#print axioms portProfile_nonzero
#print axioms portProfile_gram

end

end StructuralDefects
