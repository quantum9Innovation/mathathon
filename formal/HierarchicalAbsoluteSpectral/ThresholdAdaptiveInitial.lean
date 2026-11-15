import HierarchicalAbsoluteSpectral.MainInertiaAdaptive

/-! Adaptive Ritz histories with measurable, source-dependent initial
endpoints.  The source may include a fresh initializer draw as well as the
query samples. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k r N cap : ℕ}
local instance initialMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance initialMatrixBorelInstance (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩
attribute [local irreducible] krylovRitzFixedMatrix krylovSpanProjector

/-- The common varying-endpoint theorem, specialized to the initializer
interface. The history proof is shared with the inertia event. -/
theorem idealRitzThresholdParameter_initial_measurable {X : Type*} [MeasurableSpace X]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hml : Measurable l) (hmu : Measurable u)
    (hl : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (samples : X → Fin cap → Fin N → Fin r → Fin k → ℝ)
    (hmsamples : Measurable samples) (i : Fin cap) :
    Measurable (fun x => idealRitzThresholdParameter kernels T S q j ε searchAccuracy
      (l x) (u x) (hl x) (hlu x) (samples x) i) :=
  idealRitzThresholdParameter_measurable_with_endpoints kernels T hT S hS q j ε searchAccuracy
    l u hml hmu hl hlu samples hmsamples i

/-- A source-dependent initial interval, followed by adaptive query draws. -/
def idealRitzInitialThresholdParameter {X : Type*}
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k) (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hl : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (x : X × (Fin cap → Fin N → Fin r → Fin k → ℝ))
    (i : Fin cap) : {t : ℝ // 0 < t} :=
  idealRitzThresholdParameter kernels T S q j ε searchAccuracy
    (l x.1) (u x.1) (hl x.1) (hlu x.1) x.2 i

theorem idealRitzInitialThresholdParameter_measurable {X : Type*} [MeasurableSpace X]
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian}) (hT : Measurable T)
    (S : {t : ℝ // 0 < t} → Core k) (hS : Measurable S)
    (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hml : Measurable l) (hmu : Measurable u)
    (hl : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x) (i : Fin cap) :
    Measurable (fun x : X × (Fin cap → Fin N → Fin r → Fin k → ℝ) =>
      idealRitzInitialThresholdParameter kernels T S q j ε searchAccuracy l u hl hlu x i) :=
  idealRitzThresholdParameter_initial_measurable
    (X:=X × (Fin cap → Fin N → Fin r → Fin k → ℝ)) (r:=r) (N:=N) (cap:=cap)
    kernels T hT S hS q j ε searchAccuracy
    (fun x => l x.1) (fun x => u x.1) (hml.comp measurable_fst) (hmu.comp measurable_fst)
    (fun x => hl x.1) (fun x => hlu x.1) Prod.snd measurable_snd i

/-- Replacing the current query block leaves its threshold unchanged,
while the initializer and its endpoints are kept fixed. -/
theorem idealRitzInitialThresholdParameter_update {X : Type*}
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : {t : ℝ // 0 < t} → {T : Core k // T.IsHermitian})
    (S : {t : ℝ // 0 < t} → Core k) (q : ℕ) (j : Fin k) (ε searchAccuracy : ℝ)
    (l u : X → ℝ) (hl : ∀ x, 0 < l x) (hlu : ∀ x, l x ≤ u x)
    (x : X) (samples : Fin cap → Fin N → Fin r → Fin k → ℝ)
    (i : Fin cap) (fresh : Fin N → Fin r → Fin k → ℝ) :
    idealRitzInitialThresholdParameter kernels T S q j ε searchAccuracy l u hl hlu
      (x,Function.update samples i fresh) i =
    idealRitzInitialThresholdParameter kernels T S q j ε searchAccuracy l u hl hlu (x,samples) i :=
  idealRitzThresholdParameter_update kernels T S q j ε searchAccuracy
    (l x) (u x) (hl x) (hlu x) samples i fresh

end
end HierarchicalAbsoluteSpectral
