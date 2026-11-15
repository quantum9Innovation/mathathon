import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftRandom
import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open ArithmeticProgram hiding pure

theorem exactGramAppendixCongruence_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (C exponent : ℝ) (hC : 0 < C) (hexponent : 2 ≤ exponent)
    (hcore : ∀ a b c N : ℕ, 1 ≤ N → a ≤ N → b ≤ N → c ≤ N →
      ((kernels a b c).cost : ℝ) ≤ C*(N:ℝ)^exponent)
    {k : ℕ} (K : Core k) (hK : Kᵀ = K) (S : Core k)
    (m : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    ((congruenceInertiaProgram kernels K hK S).work : ℝ) ≤ 24*(C+1)*(m:ℝ)^exponent := by
  have hldl : (fastLDLCost kernels k : ℝ) ≤ 18*(C+1)*(m:ℝ)^exponent := by
    by_cases hk1 : 1 ≤ k
    · apply (fastLDLCost_bound kernels C exponent hC hexponent
        (fun a b c N _ => hcore a b c N) k hk1).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk) (by linarith)
    · have hk0 : k = 0 := by omega
      rw [hk0, fastLDLCost]
      simp only [Nat.cast_zero]
      positivity
  have hkernel := hcore k k k m hm hk hk hk
  have hkpow : (k:ℝ) ≤ (m:ℝ)^exponent := by
    have hmreal : (1:ℝ) ≤ m := by exact_mod_cast hm
    calc
      _ ≤ (m:ℝ) := by exact_mod_cast hk
      _ = (m:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hmreal (by linarith)
  have hh : ((congruenceInertiaProgram kernels K hK S).work : ℝ) ≤
      (fastLDLCost kernels k : ℝ)+5*((kernels k k k).cost : ℝ)+(k:ℝ) := by
    exact_mod_cast congruenceInertiaProgram_work_le kernels K hK S
  have hpow := Real.rpow_nonneg (Nat.cast_nonneg m) exponent
  nlinarith

theorem exactGramAppendixRandomLiftProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η ζ C : ℝ) (hκ : 1/2 ≤ κ) (hζ : 0 ≤ ζ) (hC : 0 < C)
    {N n m p k r : ℕ} (hEnv : HierarchyKernelEnvelopes κ η ζ N m kernels C)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (K : Core k) (hK : Kᵀ = K)
    (hnegative : ∀ out : FiniteCongruenceDiagonal K, out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) (hm : 1 ≤ m) (hNm : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hk : k ≤ m) (hwr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    ((exactGramAppendixRandomLiftProgram kernels A B T K hK hnegative g).work : ℝ) ≤
      34*(C+1)*(m:ℝ)^(9/4+ζ) + 5*C*(N:ℝ)*(m:ℝ)^(1+η) + C*(N:ℝ)^(2+ζ) := by
  have hcong := exactGramAppendixCongruence_work_bound kernels C (9/4+ζ) hC
    (by linarith) hEnv.core K hK (gaussianSquareMatrix k g) m hm hk
  have hlift (out : FiniteCongruenceDiagonal K) := exactGramAppendixLiftProgram_work_bound
    kernels κ η ζ C hκ hζ hC hEnv A B T out (hnegative out) hm hNm hn hp hk hwr
  have hpow : 0 ≤ (C+1)*(m:ℝ)^(9/4+ζ) := by positivity
  have ha : 0 ≤ C*(N:ℝ)*(m:ℝ)^(1+η) := by positivity
  have ho : 0 ≤ C*(N:ℝ)^(2+ζ) := by positivity
  simp only [exactGramAppendixRandomLiftProgram, work_bind, Nat.cast_add]
  split
  · simp only [work_pure, Nat.cast_zero, add_zero]
    nlinarith
  · simp only [work_bind, work_pure, add_zero, Nat.cast_add]
    have hh := hlift (by assumption)
    linarith

def exactGramAppendixShiftProgram {k : ℕ} (Hc : Core k) (t : ℝ) : ArithmeticProgram (Core k) :=
  blockSubProgram (Matrix.diagonal (fun _ => t)) Hc

@[simp] theorem exactGramAppendixShiftProgram_eval {k : ℕ} (Hc : Core k) (t : ℝ) :
    (exactGramAppendixShiftProgram Hc t).eval = t • (1 : Core k)-Hc := by
  rw [exactGramAppendixShiftProgram, blockSubProgram_eval]
  congr 1
  ext i j
  by_cases hij : i=j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

@[simp] theorem exactGramAppendixShiftProgram_work {k : ℕ} (Hc : Core k) (t : ℝ) :
    (exactGramAppendixShiftProgram Hc t).work = k*k := blockSubProgram_work _ _

theorem exactGramAppendixShiftProgram_admissible {k : ℕ} (Hc : Core k) (t : ℝ) :
    (exactGramAppendixShiftProgram Hc t).admissible := blockSubProgram_admissible _ _

theorem exactGramAppendixShiftProgram_fieldOnly {k : ℕ} (Hc : Core k) (t : ℝ) :
    (exactGramAppendixShiftProgram Hc t).rankProfileFieldOnly := blockSubProgram_rankProfileFieldOnly _ _

/-- All field/positive-root instructions, the fresh `k²` Gaussian draws,
the `k²` shifted-core subtractions, and every final product entry. -/
theorem exactGramAppendixRandomLiftProgram_total_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η ζ C : ℝ) (hκ : 1/2 ≤ κ) (hζ : 0 ≤ ζ) (hC : 0 < C)
    {N n m p k r : ℕ} (hEnv : HierarchyKernelEnvelopes κ η ζ N m kernels C)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (t : ℝ)
    (hK : (t • (1 : Core k)-Hc)ᵀ = t • (1 : Core k)-Hc)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) (hm : 1 ≤ m) (hNm : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hk : k ≤ m) (hwr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    ((k*k+(exactGramAppendixShiftProgram Hc t).work+
      (exactGramAppendixRandomLiftProgram kernels A B T (t • (1 : Core k)-Hc) hK hnegative g).work+n*p : ℕ) : ℝ) ≤
      (n*p : ℕ)+36*(C+1)*(m:ℝ)^(9/4+ζ) +
        5*C*(N:ℝ)*(m:ℝ)^(1+η) + C*(N:ℝ)^(2+ζ) := by
  have hh := exactGramAppendixRandomLiftProgram_work_bound kernels κ η ζ C hκ hζ hC hEnv
    A B T (t • (1 : Core k)-Hc) hK hnegative g hm hNm hn hp hk hwr
  have hsq : (k:ℝ)*(k:ℝ) ≤ (m:ℝ)^(9/4+ζ) := by
    calc
      _ ≤ (m:ℝ)*(m:ℝ) := by gcongr <;> exact_mod_cast hk
      _ = (m:ℝ)^(2:ℝ) := by rw [Real.rpow_two, pow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  rw [exactGramAppendixShiftProgram_work]
  push_cast
  have hpos : 0 ≤ C*(m:ℝ)^(9/4+ζ) := by positivity
  nlinarith

end
end HierarchicalAbsoluteSpectral
