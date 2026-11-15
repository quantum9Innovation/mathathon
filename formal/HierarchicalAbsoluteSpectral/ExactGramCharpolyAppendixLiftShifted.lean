import HierarchicalAbsoluteSpectral.ExactGramCharpolyAppendixLiftRandomCost

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open ArithmeticProgram hiding pure
open scoped MatrixOrder Matrix.Norms.L2Operator

def exactGramAppendixDiagonalCast {k : ℕ} {D E : Core k} (h : D=E)
    (out : FiniteCongruenceDiagonal D) : FiniteCongruenceDiagonal E := h ▸ out

@[simp] theorem exactGramAppendixDiagonalCast_negativeCount {k : ℕ} {D E : Core k} (h : D=E)
    (out : FiniteCongruenceDiagonal D) :
    (exactGramAppendixDiagonalCast h out).negativeCount = out.negativeCount := by
  cases h
  rfl

def exactGramAppendixShiftedRandomLiftProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) : ArithmeticProgram (Option (FixedRankOutput n p r)) := do
  let K ← certify (exactGramAppendixShiftProgram Hc t)
  have hval : K.val = t • (1 : Core k)-Hc := K.property.trans (exactGramAppendixShiftProgram_eval Hc t)
  have hsym : K.valᵀ = K.val := by
    rw [hval]
    have hHcsym : Hcᵀ = Hc := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hHc.eq
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hHcsym]
  have hbudget : ∀ out : FiniteCongruenceDiagonal K.val, out.negativeCount ≤ r := by
    intro out
    have hh := hnegative (exactGramAppendixDiagonalCast hval out)
    simpa only [exactGramAppendixDiagonalCast_negativeCount] using hh
  exactGramAppendixRandomLiftProgram kernels A B T K.val hsym hbudget g

theorem exactGramAppendixShiftedRandomLiftProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) :
    (exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc t hnegative g).admissible := by
  simp only [exactGramAppendixShiftedRandomLiftProgram, admissible_bind, certify_admissible,
    exactGramAppendixShiftProgram_admissible, exactGramAppendixRandomLiftProgram_admissible, and_self]

theorem exactGramAppendixRandomLiftProgram_error_of_eq
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (t : ℝ) (ht : 0 ≤ t)
    (hZ : (A*T)ᵀ*(A*T) = 1) (hcov : (A*B)*(A*B)ᵀ = (A*T)*Hc*(A*T)ᵀ)
    (K : Core k) (hK : Kᵀ = K)
    (hnegative : ∀ out : FiniteCongruenceDiagonal K, out.negativeCount ≤ r)
    (heq : K = t • (1 : Core k)-Hc) (g : Fin (k*k) → ℝ) (result : FixedRankOutput n p r)
    (hresult : (exactGramAppendixRandomLiftProgram kernels A B T K hK hnegative g).eval = some result) :
    ‖A*B-result.product‖ ≤ Real.sqrt t := by
  subst K
  exact exactGramAppendixRandomLiftProgram_error kernels A B T Hc t ht hZ hcov hK hnegative g result hresult

theorem exactGramAppendixShiftedRandomLiftProgram_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ) (ht : 0 ≤ t)
    (hZ : (A*T)ᵀ*(A*T) = 1) (hcov : (A*B)*(A*B)ᵀ = (A*T)*Hc*(A*T)ᵀ)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) (result : FixedRankOutput n p r)
    (hresult : (exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc t hnegative g).eval = some result) :
    ‖A*B-result.product‖ ≤ Real.sqrt t := by
  rw [exactGramAppendixShiftedRandomLiftProgram, eval_bind] at hresult
  exact exactGramAppendixRandomLiftProgram_error_of_eq kernels A B T Hc t ht hZ hcov _ _ _
    ((certify (exactGramAppendixShiftProgram Hc t)).eval.property.trans
      (exactGramAppendixShiftProgram_eval Hc t)) g result hresult

theorem exactGramAppendixShiftedRandomLiftProgram_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (hdet : IsUnit (t • (1 : Core k)-Hc).det) :
    ∀ᵐ g ∂gaussianVector (k*k),
      ∃ result, (exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc t hnegative g).eval = some result := by
  simp only [exactGramAppendixShiftedRandomLiftProgram, eval_bind]
  apply exactGramAppendixRandomLiftProgram_success_ae
  have hval := (certify (exactGramAppendixShiftProgram Hc t)).eval.property.trans
    (exactGramAppendixShiftProgram_eval Hc t)
  rwa [hval]

theorem exactGramAppendixShiftedRandomLiftProgram_success_of_jointGood
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (hdet : IsUnit (t • (1 : Core k)-Hc).det) (g : Fin (k*k) → ℝ)
    (hg : jointInertiaGood (t • (1 : Core k)-Hc) g) :
    ∃ result, (exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc t hnegative g).eval = some result := by
  rw [exactGramAppendixShiftedRandomLiftProgram, eval_bind]
  apply exactGramAppendixRandomLiftProgram_success_of_jointGood
  · have hval := (certify (exactGramAppendixShiftProgram Hc t)).eval.property.trans
      (exactGramAppendixShiftProgram_eval Hc t)
    rwa [hval]
  · have hval := (certify (exactGramAppendixShiftProgram Hc t)).eval.property.trans
      (exactGramAppendixShiftProgram_eval Hc t)
    rwa [hval]

theorem exactGramAppendixShiftedRandomLiftProgram_joint_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian)
    (time : ℝ → ℝ) (hTime : Continuous time)
    (hnegative : ∀ x, ∀ out : FiniteCongruenceDiagonal (time x • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (hdet : ∀ᵐ x ∂gaussianReal 0 1, IsUnit (time x • (1 : Core k)-Hc).det) :
    ∀ᵐ z ∂(gaussianReal 0 1).prod (gaussianVector (k*k)),
      ∃ result, (exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc
        (time z.1) (hnegative z.1) z.2).eval = some result := by
  have hdetProd : ∀ᵐ z ∂(gaussianReal 0 1).prod (gaussianVector (k*k)),
      IsUnit (time z.1 • (1 : Core k)-Hc).det :=
    (measurePreserving_fst (μ := gaussianReal 0 1) (ν := gaussianVector (k*k))).quasiMeasurePreserving.ae hdet
  filter_upwards [exactGramAppendixLift_jointGood_ae Hc time hTime, hdetProd] with z hz hd
  exact exactGramAppendixShiftedRandomLiftProgram_success_of_jointGood kernels A B T Hc hHc
    (time z.1) (hnegative z.1) hd z.2 hz

theorem exactGramAppendixShiftedRandomLiftProgram_joint_error_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k r : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian)
    (hZ : (A*T)ᵀ*(A*T) = 1) (hcov : (A*B)*(A*B)ᵀ = (A*T)*Hc*(A*T)ᵀ)
    (time : ℝ → ℝ) (hTime : Continuous time) (htime : ∀ x, 0 ≤ time x)
    (hnegative : ∀ x, ∀ out : FiniteCongruenceDiagonal (time x • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (hdet : ∀ᵐ x ∂gaussianReal 0 1, IsUnit (time x • (1 : Core k)-Hc).det) :
    ∀ᵐ z ∂(gaussianReal 0 1).prod (gaussianVector (k*k)),
      ∃ result, (exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc
        (time z.1) (hnegative z.1) z.2).eval = some result ∧
          ‖A*B-result.product‖ ≤ Real.sqrt (time z.1) := by
  filter_upwards [exactGramAppendixShiftedRandomLiftProgram_joint_success_ae kernels A B T Hc hHc
    time hTime hnegative hdet] with z hz
  obtain ⟨result,he⟩ := hz
  exact ⟨result,he,exactGramAppendixShiftedRandomLiftProgram_error kernels A B T Hc hHc
    (time z.1) (htime z.1) hZ hcov (hnegative z.1) z.2 result he⟩

theorem exactGramAppendixShiftedRandomLiftProgram_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η ζ C : ℝ) (hκ : 1/2 ≤ κ) (hζ : 0 ≤ ζ) (hC : 0 < C)
    {N n m p k r : ℕ} (hEnv : HierarchyKernelEnvelopes κ η ζ N m kernels C)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) (hm : 1 ≤ m) (hNm : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hk : k ≤ m) (hwr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    ((exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc t hnegative g).work : ℝ) ≤
      35*(C+1)*(m:ℝ)^(9/4+ζ) + 5*C*(N:ℝ)*(m:ℝ)^(1+η) + C*(N:ℝ)^(2+ζ) := by
  simp only [exactGramAppendixShiftedRandomLiftProgram, work_bind, certify_work,
    exactGramAppendixShiftProgram_work, Nat.cast_add]
  have hsq : (k:ℝ)*(k:ℝ) ≤ (m:ℝ)^(9/4+ζ) := by
    calc
      _ ≤ (m:ℝ)*(m:ℝ) := by gcongr <;> exact_mod_cast hk
      _ = (m:ℝ)^(2:ℝ) := by rw [Real.rpow_two, pow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  calc
    _ ≤ ((k*k : ℕ) : ℝ)+(34*(C+1)*(m:ℝ)^(9/4+ζ)+
        5*C*(N:ℝ)*(m:ℝ)^(1+η)+C*(N:ℝ)^(2+ζ)) := by
      gcongr
      exact exactGramAppendixRandomLiftProgram_work_bound kernels κ η ζ C hκ hζ hC hEnv
        A B T _ _ _ g hm hNm hn hp hk hwr
    _ ≤ _ := by
      push_cast
      nlinarith [show 0 ≤ C*(m:ℝ)^(9/4+ζ) by positivity]

theorem exactGramAppendixShiftedRandomLiftProgram_total_work_bound
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (κ η ζ C : ℝ) (hκ : 1/2 ≤ κ) (hζ : 0 ≤ ζ) (hC : 0 < C)
    {N n m p k r : ℕ} (hEnv : HierarchyKernelEnvelopes κ η ζ N m kernels C)
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (hnegative : ∀ out : FiniteCongruenceDiagonal (t • (1 : Core k)-Hc), out.negativeCount ≤ r)
    (g : Fin (k*k) → ℝ) (hm : 1 ≤ m) (hNm : m ≤ N) (hn : n ≤ N) (hp : p ≤ N)
    (hk : k ≤ m) (hwr : (r:ℝ) ≤ Real.sqrt (m:ℝ)) :
    ((k*k+(exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc t hnegative g).work+n*p : ℕ) : ℝ) ≤
      (n*p : ℕ)+36*(C+1)*(m:ℝ)^(9/4+ζ) +
        5*C*(N:ℝ)*(m:ℝ)^(1+η) + C*(N:ℝ)^(2+ζ) := by
  have hh := exactGramAppendixShiftedRandomLiftProgram_work_bound kernels κ η ζ C hκ hζ hC hEnv
    A B T Hc hHc t hnegative g hm hNm hn hp hk hwr
  have hsq : (k:ℝ)*(k:ℝ) ≤ (m:ℝ)^(9/4+ζ) := by
    calc
      _ ≤ (m:ℝ)*(m:ℝ) := by gcongr <;> exact_mod_cast hk
      _ = (m:ℝ)^(2:ℝ) := by rw [Real.rpow_two, pow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  push_cast
  nlinarith [show 0 ≤ C*(m:ℝ)^(9/4+ζ) by positivity]

def exactGramAppendixEigenvalueLiftProgram
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (r : ℕ) (hr : r < k) (heigen : orderedEigenvalue Hc hHc ⟨r,hr⟩ ≤ t)
    (g : Fin (k*k) → ℝ) : ArithmeticProgram (Option (FixedRankOutput n p r)) :=
  exactGramAppendixShiftedRandomLiftProgram kernels A B T Hc hHc t
    (fun out => exactGramAppendixLift_negativeCount_le Hc hHc t out r hr heigen) g

theorem exactGramAppendixEigenvalueLiftProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ)
    (r : ℕ) (hr : r < k) (heigen : orderedEigenvalue Hc hHc ⟨r,hr⟩ ≤ t)
    (g : Fin (k*k) → ℝ) :
    (exactGramAppendixEigenvalueLiftProgram kernels A B T Hc hHc t r hr heigen g).admissible :=
  exactGramAppendixShiftedRandomLiftProgram_admissible kernels A B T Hc hHc t _ g

theorem exactGramAppendixEigenvalueLiftProgram_error
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    {n m p k : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin k) ℝ) (Hc : Core k) (hHc : Hc.IsHermitian) (t : ℝ) (ht : 0 ≤ t)
    (hZ : (A*T)ᵀ*(A*T) = 1) (hcov : (A*B)*(A*B)ᵀ = (A*T)*Hc*(A*T)ᵀ)
    (r : ℕ) (hr : r < k) (heigen : orderedEigenvalue Hc hHc ⟨r,hr⟩ ≤ t)
    (g : Fin (k*k) → ℝ) (result : FixedRankOutput n p r)
    (hresult : (exactGramAppendixEigenvalueLiftProgram kernels A B T Hc hHc t r hr heigen g).eval = some result) :
    ‖A*B-result.product‖ ≤ Real.sqrt t :=
  exactGramAppendixShiftedRandomLiftProgram_error kernels A B T Hc hHc t ht hZ hcov _ g result hresult

end
end HierarchicalAbsoluteSpectral
