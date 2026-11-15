import Matmul.RectangularRankBridge

/-!
Finite integer matrix multiplication schemes for three independently rounded
shape exponents. The input to the bridge is a proved inequality for actual
integral characters; the output includes the coefficient arrays and their
matrix tensor identity.
-/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Matmul
open Matmul.IntegralSpectrum Matmul.UniversalRecursiveAlgorithm
open Matmul.IntegerBilinear Matmul.RectangularRankBridge

structure ScaleneSchemeCertificate (u v w E : ℝ) where
  q : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  ρ : ℕ
  alg : Scheme a b c ρ
  q_ge_two : 2 ≤ q
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  correct : alg.tensor = matrixTensor a b c
  rowShape : (q : ℝ) ^ u ≤ (a : ℝ)
  innerShape : (q : ℝ) ^ v ≤ (b : ℝ)
  columnShape : (q : ℝ) ^ w ≤ (c : ℝ)
  volume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ
  rankExponent_lt : Real.log (ρ : ℝ) / Real.log (q : ℝ) < E

theorem scalene_ceil_pos {q : ℕ} (hq : 2 ≤ q) {u : ℝ} (hu : 0 ≤ u) :
    0 < Nat.ceil ((q : ℝ) ^ u) := by
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hpow := Real.one_le_rpow hqR hu
  have hc := Nat.le_ceil ((q : ℝ) ^ u)
  by_contra hz
  have hz' : Nat.ceil ((q : ℝ) ^ u) = 0 := by omega
  rw [hz', Nat.cast_zero] at hc
  linarith

theorem scalene_ceil_power_bound {q : ℕ} (hq : 2 ≤ q) {u p : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Nat.ceil ((q : ℝ) ^ u) : ℝ) ^ p ≤ 2 * (q : ℝ) ^ (u * p) := by
  simpa only [Real.rpow_zero, one_mul, zero_add] using
    (Matmul.MatrixPowerBound.ceil_rpow_bound hq hu hp hp1
      (show (0 : ℝ) + u * p ≤ u * p by simp))

theorem scalene_value_ceil_matrixTensor_le (φ : IntegralCharacter) {q : ℕ}
    (hq : 2 ≤ q) {u v w F : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hobj : u * φ.pY + v * φ.pZ + w * φ.pX ≤ F) :
    φ.value (matrixTensor (Nat.ceil ((q : ℝ) ^ u))
      (Nat.ceil ((q : ℝ) ^ v)) (Nat.ceil ((q : ℝ) ^ w))) ≤
      8 * (q : ℝ) ^ F := by
  rw [Matmul.MatrixCharacter.value_matrixTensor φ
    (scalene_ceil_pos hq hu) (scalene_ceil_pos hq hv) (scalene_ceil_pos hq hw)]
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have h1 := scalene_ceil_power_bound hq hu φ.pY_nonneg φ.pY_le_one
  have h2 := scalene_ceil_power_bound hq hv φ.pZ_nonneg φ.pZ_le_one
  have h3 := scalene_ceil_power_bound hq hw φ.pX_nonneg φ.pX_le_one
  calc
    _ ≤ (2 * (q : ℝ) ^ (u * φ.pY)) *
        (2 * (q : ℝ) ^ (v * φ.pZ)) * (2 * (q : ℝ) ^ (w * φ.pX)) := by
      gcongr <;> assumption
    _ = 8 * (q : ℝ) ^ (u * φ.pY + v * φ.pZ + w * φ.pX) := by
      rw [Real.rpow_add hqpos, Real.rpow_add hqpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hqR hobj) (by norm_num)

theorem scalene_matrix_asymptoticRank_ceil_le {q : ℕ} (hq : 2 ≤ q)
    {u v w F : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hF : 0 ≤ F)
    (hobj : ∀ φ : IntegralCharacter, u * φ.pY + v * φ.pZ + w * φ.pX ≤ F) :
    asymptoticRank (UnitTensorClass.matrixClass (Nat.ceil ((q : ℝ) ^ u))
      (Nat.ceil ((q : ℝ) ^ v)) (Nat.ceil ((q : ℝ) ^ w))) ≤
      8 * (q : ℝ) ^ F := by
  apply asymptoticRank_le_of_character_bound
  · have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    have hp := Real.one_le_rpow hqR hF
    linarith
  · intro χ hχ
    rw [← Matmul.MatrixCharacter.value_matrixClass χ hχ]
    exact scalene_value_ceil_matrixTensor_le _ hq hu hv hw (hobj _)

theorem scalene_exists_large_power_two {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 2 ≤ q ∧ 8 < (q : ℝ) ^ δ := by
  have hp : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (8 : ℝ) hp
  have htpos : 0 < t := by
    by_contra hz
    have hz' : t = 0 := by omega
    simp [hz'] at ht
  refine ⟨2 ^ t, Nat.le_pow htpos, ?_⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat,
    pow_rpow_comm (by norm_num : (0 : ℝ) ≤ 2)] using ht

/-- Spectral inequalities are converted to an exact finite coefficient scheme.
The dimensions and coefficients are chosen independently of an evaluation ring. -/
theorem exists_scalene_scheme_certificate_of_objective {u v w F ε : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hF : 0 ≤ F)
    (hobj : ∀ φ : IntegralCharacter, u * φ.pY + v * φ.pZ + w * φ.pX ≤ F)
    (hε : 0 < ε) : Nonempty (ScaleneSchemeCertificate u v w (F + ε)) := by
  classical
  obtain ⟨q, hq, hlarge⟩ := scalene_exists_large_power_two hε
  let row := Nat.ceil ((q : ℝ) ^ u)
  let inner := Nat.ceil ((q : ℝ) ^ v)
  let col := Nat.ceil ((q : ℝ) ^ w)
  have hr : 0 < row := scalene_ceil_pos hq hu
  have hi : 0 < inner := scalene_ceil_pos hq hv
  have hc : 0 < col := scalene_ceil_pos hq hw
  have hqpos : 0 < q := by omega
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hstrict : asymptoticRank (UnitTensorClass.matrixClass row inner col) <
      (q : ℝ) ^ (F + ε) := by
    have hupper := scalene_matrix_asymptoticRank_ceil_le hq hu hv hw hF hobj
    have hmul := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hqR F)
    rw [Real.rpow_add hqR]
    exact hupper.trans_lt (by simpa only [mul_comm] using hmul)
  obtain ⟨m, hm, hrank⟩ := exists_rank_power_lt
    (UnitTensorClass.matrixClass_ne_zero hr hi hc) hstrict
  let Q := q ^ m
  let a := row ^ m
  let b := inner ^ m
  let c := col ^ m
  let ρ := UnitTensorClass.rank (UnitTensorClass.matrixClass a b c)
  have hQ : 2 ≤ Q := hq.trans (Nat.le_pow hm)
  have ha : 0 < a := pow_pos hr m
  have hb : 0 < b := pow_pos hi m
  have hcp : 0 < c := pow_pos hc m
  have hρeq : ρ = UnitTensorClass.rank (UnitTensorClass.matrixClass row inner col ^ m) := by
    dsimp [ρ, a, b, c]
    rw [UnitTensorClass.matrixClass_pow]
  have hρlt : (ρ : ℝ) < (Q : ℝ) ^ (F + ε) := by
    rw [hρeq]
    simpa only [Q, Nat.cast_pow, pow_rpow_comm hqR.le] using hrank
  have hvolume : Matmul.RecursiveCost.blockVolume a b c ≤ ρ := by
    have h := UnitTensorClass.rank_matrixClass_lower ha hb hcp
    dsimp [Matmul.RecursiveCost.blockVolume]
    dsimp [ρ] at h ⊢
    simpa only [max_assoc, Nat.mul_comm] using h
  have hρpos : 0 < ρ := by
    have hp : 0 < Matmul.RecursiveCost.blockVolume a b c :=
      lt_of_lt_of_le (Nat.mul_pos ha hb) (le_max_left _ _)
    omega
  obtain ⟨alg, halg⟩ := rankAtMost_iff_exists_algorithm.mp
    (show Tensor.RankAtMost (matrixTensor a b c) ρ by
      simpa only [ρ, UnitTensorClass.rank_matrixClass] using exactRank_spec (matrixTensor a b c))
  refine ⟨⟨Q, a, b, c, ρ, alg, hQ, ha, hb, hcp, halg, ?_, ?_, ?_, hvolume, ?_⟩⟩
  · have hp := pow_le_pow_left₀ (Real.rpow_nonneg hqR.le u)
      (Nat.le_ceil ((q : ℝ) ^ u)) m
    simpa only [Q, a, row, Nat.cast_pow, pow_rpow_comm hqR.le] using hp
  · have hp := pow_le_pow_left₀ (Real.rpow_nonneg hqR.le v)
      (Nat.le_ceil ((q : ℝ) ^ v)) m
    simpa only [Q, b, inner, Nat.cast_pow, pow_rpow_comm hqR.le] using hp
  · have hp := pow_le_pow_left₀ (Real.rpow_nonneg hqR.le w)
      (Nat.le_ceil ((q : ℝ) ^ w)) m
    simpa only [Q, c, col, Nat.cast_pow, pow_rpow_comm hqR.le] using hp
  · have hQR : 1 < (Q : ℝ) := by exact_mod_cast (show 1 < Q by omega)
    have hρR : 0 < (ρ : ℝ) := by exact_mod_cast hρpos
    have hlog := Real.log_lt_log hρR hρlt
    rw [Real.log_rpow (by linarith : 0 < (Q : ℝ))] at hlog
    exact (div_lt_iff₀ (Real.log_pos hQR)).mpr (by simpa only [mul_comm] using hlog)

#print axioms exists_scalene_scheme_certificate_of_objective

end
end HierarchicalAbsoluteSpectral
