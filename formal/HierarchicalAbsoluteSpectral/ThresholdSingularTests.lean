import HierarchicalAbsoluteSpectral.ThresholdOptionalInertia
import HierarchicalAbsoluteSpectral.CoarseAlgebraProjectedInertiaCost
import HierarchicalAbsoluteSpectral.ThresholdRepetitions

set_option backward.isDefEq.respectTransparency false

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open ArithmeticProgram hiding pure
open scoped MatrixOrder
variable {k : ℕ}

/-- Reuse a fixed ambient random array only through its initial coordinates.
The fallback is relevant only to unused larger sizes in the compiler family. -/
def initialCoordinates {a b : ℕ} (g : Fin a → ℝ) : Fin b → ℝ :=
  fun i => if hi : i.val < a then g ⟨i.val,hi⟩ else 0

@[simp] theorem initialCoordinates_self {a : ℕ} (g : Fin a → ℝ) :
    (initialCoordinates g : Fin a → ℝ) = g := by
  funext i
  simp only [initialCoordinates,dif_pos i.isLt]

def singularInertiaFamily (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (ambient : ℕ) (g : Fin (ambient*ambient) → ℝ) : OptionalInertiaProgramFamily :=
  fun n D hD => projectedSingularInertiaProgram kernels n D (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq) (initialCoordinates g)

theorem singularInertiaFamily_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (ambient : ℕ) (g : Fin (ambient*ambient) → ℝ) (n : ℕ) (D : Core n) (hD : D.IsHermitian) :
    (singularInertiaFamily kernels ambient g n D hD).admissible :=
  projectedSingularInertiaProgram_admissible kernels n D _ _

def shiftedSingularEigenvalueTestProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) (g : Fin (k*k) → ℝ) :
    ArithmeticProgram (Option (CertifiedEigenvalueTest A hA c j)) :=
  shiftedEigenvalueTestOptionProgram (singularInertiaFamily kernels k g) A hA c j

theorem shiftedSingularEigenvalueTestProgram_admissible
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) (g : Fin (k*k) → ℝ) :
    (shiftedSingularEigenvalueTestProgram kernels A hA c j g).admissible :=
  shiftedEigenvalueTestOptionProgram_admissible _ (singularInertiaFamily_admissible kernels k g) A hA c j

def ShiftedInertiaPolynomialGood (A : Core k) (c : ℝ) (g : Fin (k*k) → ℝ) : Prop :=
  ∀ (j : ℕ) (hjk : j ≤ k), congruenceMinorPolynomial (A-c • (1 : Core k)) j hjk ≠ 0 →
    MvPolynomial.eval (fun x : Fin k × Fin k => g (finProdFinEquiv x))
      (congruenceMinorPolynomial (A-c • (1 : Core k)) j hjk) ≠ 0

theorem shiftedSingularEigenvalueTestProgram_success_of_polynomial_event
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) (g : Fin (k*k) → ℝ)
    (hg : ShiftedInertiaPolynomialGood A c g) : ∃ out,
      (shiftedSingularEigenvalueTestProgram kernels A hA c j g).eval = some out := by
  let D := (shiftedMatrixProgram A c).certify.eval.val
  have hDvalue : D = A-c • (1 : Core k) :=
    (shiftedMatrixProgram A c).certify.eval.property.trans (shiftedMatrixProgram_eval A c)
  have hD : D.IsHermitian := by rw [hDvalue]; exact shifted_isHermitian A hA c
  have hgood : ∀ (i : ℕ) (hik : i ≤ k), congruenceMinorPolynomial D i hik ≠ 0 →
      MvPolynomial.eval (fun x : Fin k × Fin k => g (finProdFinEquiv x))
        (congruenceMinorPolynomial D i hik) ≠ 0 := by
    simpa only [hDvalue,ShiftedInertiaPolynomialGood] using hg
  obtain ⟨out,hout⟩ := projectedSingularInertiaProgram_success_of_polynomial_event kernels k D (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq) g hgood
  have hfamily : (singularInertiaFamily kernels k g k D hD).eval = some out := by
    simpa only [singularInertiaFamily,initialCoordinates_self] using hout
  unfold shiftedSingularEigenvalueTestProgram shiftedEigenvalueTestOptionProgram
  simp only [eval_bind]
  rw [show (singularInertiaFamily kernels k g k
      (shiftedMatrixProgram A c).certify.eval.val _).eval = some out from hfamily]
  simp only [eval_bind,eval_pure]
  exact ⟨_,rfl⟩

theorem shiftedSingularEigenvalueTestProgram_success_ae
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core k) (hA : A.IsHermitian) (c : ℝ) (j : Fin k) :
    ∀ᵐ g ∂gaussianVector (k*k), ∃ out,
      (shiftedSingularEigenvalueTestProgram kernels A hA c j g).eval = some out := by
  let D := (shiftedMatrixProgram A c).certify.eval.val
  have hD : D.IsHermitian := by
    dsimp only [D]
    rw [(shiftedMatrixProgram A c).certify.eval.property,shiftedMatrixProgram_eval]
    exact shifted_isHermitian A hA c
  have hh := projectedSingularInertiaProgram_success_ae kernels k D (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.eq)
  filter_upwards [hh] with g hg
  obtain ⟨out,hout⟩ := hg
  unfold shiftedSingularEigenvalueTestProgram shiftedEigenvalueTestOptionProgram
  simp only [eval_bind]
  have hfamily : (singularInertiaFamily kernels k g k D hD).eval = some out := by
    simpa only [singularInertiaFamily,initialCoordinates_self] using hout
  rw [show (singularInertiaFamily kernels k g k
      (shiftedMatrixProgram A c).certify.eval.val _).eval = some out from hfamily]
  simp only [eval_bind,eval_pure]
  exact ⟨_,rfl⟩

/-- Two exact tests of the same fixed-size Ritz matrix. Every returned value
is certified; the exceptional Gaussian zero-pivot outcomes return `none`. -/
def fixedRitzTestsProgram (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core k) (hA : A.IsHermitian) (j : Fin k) (ε : ℝ)
    (g : Fin 2 → Fin (k*k) → ℝ) :
    ArithmeticProgram (Option (CertifiedRitzTests (orderedEigenvalue A hA j) ε)) := do
  let one? ← shiftedSingularEigenvalueTestProgram kernels A hA 1 j (g 0)
  match one? with
  | none => .pure none
  | some one => do
    let low ← (lowThresholdProgram ε).certify
    let two? ← shiftedSingularEigenvalueTestProgram kernels A hA low.val j (g 1)
    match two? with
    | none => .pure none
    | some two => .pure (some {
      aboveOne := one.answer
      aboveLow := two.answer
      one_correct := one.correct
      low_correct := by rw [← low.property.trans (lowThresholdProgram_eval ε)]; exact two.correct })

theorem fixedRitzTestsProgram_admissible (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core k) (hA : A.IsHermitian) (j : Fin k) (ε : ℝ)
    (g : Fin 2 → Fin (k*k) → ℝ) : (fixedRitzTestsProgram kernels A hA j ε g).admissible := by
  simp only [fixedRitzTestsProgram,admissible_bind,shiftedSingularEigenvalueTestProgram_admissible,true_and]
  split
  · trivial
  · simp only [admissible_bind,certify_admissible,lowThresholdProgram_admissible,
      shiftedSingularEigenvalueTestProgram_admissible,true_and]
    split <;> trivial

theorem fixedRitzTestsProgram_success_of_polynomial_events
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core k) (hA : A.IsHermitian) (j : Fin k) (ε : ℝ)
    (g : Fin 2 → Fin (k*k) → ℝ)
    (h0 : ShiftedInertiaPolynomialGood A 1 (g 0))
    (h1 : ShiftedInertiaPolynomialGood A (1-2*ε) (g 1)) : ∃ out,
      (fixedRitzTestsProgram kernels A hA j ε g).eval = some out := by
  obtain ⟨one,hOne⟩ := shiftedSingularEigenvalueTestProgram_success_of_polynomial_event kernels A hA 1 j (g 0) h0
  have hl : (lowThresholdProgram ε).certify.eval.val = 1-2*ε :=
    (lowThresholdProgram ε).certify.eval.property.trans (lowThresholdProgram_eval ε)
  have h1' : ShiftedInertiaPolynomialGood A (lowThresholdProgram ε).certify.eval.val (g 1) := by
    simpa only [hl] using h1
  obtain ⟨two,hTwo⟩ := shiftedSingularEigenvalueTestProgram_success_of_polynomial_event kernels A hA _ j (g 1) h1'
  unfold fixedRitzTestsProgram
  rw [eval_bind,hOne,eval_bind,eval_bind,hTwo,eval_pure]
  exact ⟨_,rfl⟩

theorem fixedRitzTestsProgram_success_ae (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (A : Core k) (hA : A.IsHermitian) (j : Fin k) (ε : ℝ) :
    ∀ᵐ g ∂Measure.pi (fun _ : Fin 2 => gaussianVector (k*k)), ∃ out,
      (fixedRitzTestsProgram kernels A hA j ε g).eval = some out := by
  have h0 : ∀ᵐ g ∂Measure.pi (fun _ : Fin 2 => gaussianVector (k*k)), ∃ out,
      (shiftedSingularEigenvalueTestProgram kernels A hA 1 j (g 0)).eval = some out :=
    (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin 2 => gaussianVector (k*k)) (i:= (0 : Fin 2))).eventually
      (shiftedSingularEigenvalueTestProgram_success_ae kernels A hA 1 j)
  have h1 : ∀ᵐ g ∂Measure.pi (fun _ : Fin 2 => gaussianVector (k*k)), ∃ out,
      (shiftedSingularEigenvalueTestProgram kernels A hA
        (lowThresholdProgram ε).certify.eval.val j (g 1)).eval = some out :=
    (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin 2 => gaussianVector (k*k)) (i:= (1 : Fin 2))).eventually
      (shiftedSingularEigenvalueTestProgram_success_ae kernels A hA _ j)
  filter_upwards [h0,h1] with g hg0 hg1
  obtain ⟨one,hOne⟩ := hg0
  obtain ⟨two,hTwo⟩ := hg1
  unfold fixedRitzTestsProgram
  rw [eval_bind,hOne,eval_bind,eval_bind,hTwo,eval_pure]
  exact ⟨_,rfl⟩

end
end HierarchicalAbsoluteSpectral
