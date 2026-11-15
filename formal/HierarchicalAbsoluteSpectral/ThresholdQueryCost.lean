import HierarchicalAbsoluteSpectral.ThresholdQueryProgram
import HierarchicalAbsoluteSpectral.ThresholdKrylovCost

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure
variable {k : ℕ}

theorem shiftedSingularEigenvalueTestProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0<C) (hp : 2≤p)
    (hK : ∀ a b c N : ℕ, 1≤N → a≤N → b≤N → c≤N →
      ((kernels a b c).cost:ℝ)≤C*(N:ℝ)^p)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k)
    (hk : 1≤k) (g : Fin (k*k) → ℝ) :
    ((shiftedSingularEigenvalueTestProgram kernels A hA c j g).work:ℝ)≤
      105*(C+1)*(k:ℝ)^p := by
  let D := (shiftedMatrixProgram A c).certify.eval.val
  have hD : D.IsHermitian := by
    dsimp only [D]
    rw [(shiftedMatrixProgram A c).certify.eval.property,shiftedMatrixProgram_eval]
    exact shifted_isHermitian A hA c
  have hi := projectedSingularInertiaProgram_work_bound kernels C p hC hp hK D
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq) hk g
  have hinertia : ((singularInertiaFamily kernels k g k D hD).work:ℝ)≤100*(C+1)*(k:ℝ)^p := by
    simpa only [singularInertiaFamily,initialCoordinates_self] using hi
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hkp : (k:ℝ)^2≤(k:ℝ)^p := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hk1 hp
  have hkp0 : 0≤(k:ℝ)^p := Real.rpow_nonneg (by positivity) p
  have hkp1 : 1≤(k:ℝ)^p := by nlinarith
  dsimp only [D] at hinertia
  simp only [shiftedSingularEigenvalueTestProgram,shiftedEigenvalueTestOptionProgram,
    work_bind,certify_work,shiftedMatrixProgram_work,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  split
  · simp only [work_pure,Nat.cast_zero]
    nlinarith
  · simp only [work_bind,certify_work,ArithmeticProgram.work,work_pure,Nat.cast_add,
      Nat.cast_zero,Nat.cast_one]
    nlinarith

theorem fixedRitzTestsProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C p : ℝ) (hC : 0<C) (hp : 2≤p)
    (hK : ∀ a b c N : ℕ, 1≤N → a≤N → b≤N → c≤N →
      ((kernels a b c).cost:ℝ)≤C*(N:ℝ)^p)
    (A : Core k) (hA : A.IsHermitian) (j : Fin k) (ε : ℝ)
    (hk : 1≤k) (g : Fin 2 → Fin (k*k) → ℝ) :
    ((fixedRitzTestsProgram kernels A hA j ε g).work:ℝ)≤212*(C+1)*(k:ℝ)^p := by
  have h0 := shiftedSingularEigenvalueTestProgram_work_bound kernels C p hC hp hK A hA 1 j hk (g 0)
  have h1 := shiftedSingularEigenvalueTestProgram_work_bound kernels C p hC hp hK A hA
    (lowThresholdProgram ε).certify.eval.val j hk (g 1)
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hkp1 : 1≤(k:ℝ)^p := Real.one_le_rpow hk1 (by linarith)
  simp only [fixedRitzTestsProgram,work_bind,Nat.cast_add]
  split
  · simp only [work_pure,Nat.cast_zero]; nlinarith
  · simp only [work_bind,certify_work,lowThresholdProgram_work,Nat.cast_add,Nat.cast_ofNat]
    split
    · simp only [work_pure,Nat.cast_zero]; nlinarith
    · simp only [work_pure,Nat.cast_zero]; nlinarith

end
end HierarchicalAbsoluteSpectral
