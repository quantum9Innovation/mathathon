import HierarchicalAbsoluteSpectral.MainInitializerObservable

/-! Total positive initial intervals for the adaptive search.  On a
positive initializer branch these are exactly the executed endpoints.
On a zero residual the positive lift supplies a Borel extension. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {k r : ℕ}
local instance endpointMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) := matrixBorelSpace a b
local instance endpointMatrixBorelInstance (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) := ⟨rfl⟩

def mainInitializerTauPlus
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) : ℝ :=
  if 0 < mainInitializerObservable kernels T Ξ then
    mainInitializerObservable kernels T Ξ else 1

def mainInitializerLowerEndpoint
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ) : ℝ :=
  mainInitializerTauPlus kernels T Ξ/(4*initializerRatio k β)

def mainInitializerUpperEndpoint
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) : ℝ :=
  4*mainInitializerTauPlus kernels T Ξ

theorem mainAdaptiveInitializerRatio_ge_one (β : ℝ) (hk : 1 ≤ k) (hβ : 0 < β) :
    1 ≤ initializerRatio k β := by
  have hs : (1 : ℝ) ≤ Real.sqrt k := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have hc : 0 ≤ gaussianCaptureRadius k 1 β := by
    unfold gaussianCaptureRadius
    positivity
  unfold initializerRatio
  calc
    (1 : ℝ) = 1*1 := by norm_num
    _ ≤ Real.sqrt k*(1+gaussianCaptureRadius k 1 β) :=
      mul_le_mul hs (by linarith) (by norm_num) (Real.sqrt_nonneg _)

theorem mainInitializerTauPlus_pos
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    0 < mainInitializerTauPlus kernels T Ξ := by
  unfold mainInitializerTauPlus
  split_ifs with h
  · exact h
  · norm_num

theorem mainInitializerLowerEndpoint_pos
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ)
    (hk : 1 ≤ k) (hβ : 0 < β) :
    0 < mainInitializerLowerEndpoint kernels T Ξ β :=
  div_pos (mainInitializerTauPlus_pos kernels T Ξ)
    (mul_pos (by norm_num) (initializerRatio_pos k β hk hβ))

theorem mainInitializerUpperEndpoint_pos
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) :
    0 < mainInitializerUpperEndpoint kernels T Ξ :=
  mul_pos (by norm_num) (mainInitializerTauPlus_pos kernels T Ξ)

theorem mainInitializerEndpoints_ordered
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ)
    (hk : 1 ≤ k) (hβ : 0 < β) :
    mainInitializerLowerEndpoint kernels T Ξ β ≤ mainInitializerUpperEndpoint kernels T Ξ := by
  have ht := mainInitializerTauPlus_pos kernels T Ξ
  have hC := initializerRatio_pos k β hk hβ
  have hCone := mainAdaptiveInitializerRatio_ge_one β hk hβ
  have hprod := mul_le_mul_of_nonneg_left hCone ht.le
  unfold mainInitializerLowerEndpoint mainInitializerUpperEndpoint
  apply (div_le_iff₀ (mul_pos (by norm_num) hC)).mpr
  nlinarith

theorem mainInitializerTauPlus_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ =>
      mainInitializerTauPlus kernels x.1 x.2) :=
  Measurable.ite
    (measurableSet_lt measurable_const (mainInitializerObservable_joint_measurable kernels))
    (mainInitializerObservable_joint_measurable kernels) measurable_const

theorem mainInitializerLowerEndpoint_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (β : ℝ) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ =>
      mainInitializerLowerEndpoint kernels x.1 x.2 β) :=
  (mainInitializerTauPlus_joint_measurable kernels).div_const _

theorem mainInitializerUpperEndpoint_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    Measurable (fun x : Core k × Matrix (Fin k) (Fin r) ℝ =>
      mainInitializerUpperEndpoint kernels x.1 x.2) :=
  measurable_const.mul (mainInitializerTauPlus_joint_measurable kernels)

theorem mainInitializerTauPlus_gaussian_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    Measurable (fun x : Core k × (Fin r → Fin k → ℝ) =>
      mainInitializerTauPlus kernels x.1 (columnsMatrix x.2)) := by
  have ht : Measurable (fun x : Core k × (Fin r → Fin k → ℝ) =>
      mainInitializerObservable kernels x.1 (columnsMatrix x.2)) := by
    simpa only [gaussianInitializerProgram_value_eq_observable] using
      gaussianInitializerProgram_value_gaussian_joint_measurable (k:=k) (r:=r) kernels 1
  exact Measurable.ite (measurableSet_lt measurable_const ht) ht measurable_const

theorem mainInitializerLowerEndpoint_gaussian_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (β : ℝ) :
    Measurable (fun x : Core k × (Fin r → Fin k → ℝ) =>
      mainInitializerLowerEndpoint kernels x.1 (columnsMatrix x.2) β) :=
  (mainInitializerTauPlus_gaussian_joint_measurable kernels).div_const _

theorem mainInitializerUpperEndpoint_gaussian_joint_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) :
    Measurable (fun x : Core k × (Fin r → Fin k → ℝ) =>
      mainInitializerUpperEndpoint kernels x.1 (columnsMatrix x.2)) :=
  measurable_const.mul (mainInitializerTauPlus_gaussian_joint_measurable kernels)

theorem mainInitializerLowerEndpoint_gaussian_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (T : Core k) (β : ℝ) :
    Measurable (fun G : Fin r → Fin k → ℝ =>
      mainInitializerLowerEndpoint kernels T (columnsMatrix G) β) := by
  have ht : Measurable (fun G : Fin r → Fin k → ℝ =>
      mainInitializerObservable kernels T (columnsMatrix G)) := by
    simpa only [gaussianInitializerProgram_value_eq_observable] using
      gaussianInitializerProgram_value_gaussian_measurable (k:=k) (r:=r) kernels T 1
  have hp : Measurable (fun G : Fin r → Fin k → ℝ =>
      mainInitializerTauPlus kernels T (columnsMatrix G)) :=
    Measurable.ite (measurableSet_lt measurable_const ht) ht measurable_const
  exact hp.div_const _

theorem mainInitializerUpperEndpoint_gaussian_measurable
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (T : Core k) :
    Measurable (fun G : Fin r → Fin k → ℝ =>
      mainInitializerUpperEndpoint kernels T (columnsMatrix G)) := by
  have ht : Measurable (fun G : Fin r → Fin k → ℝ =>
      mainInitializerObservable kernels T (columnsMatrix G)) := by
    simpa only [gaussianInitializerProgram_value_eq_observable] using
      gaussianInitializerProgram_value_gaussian_measurable (k:=k) (r:=r) kernels T 1
  have hp : Measurable (fun G : Fin r → Fin k → ℝ =>
      mainInitializerTauPlus kernels T (columnsMatrix G)) :=
    Measurable.ite (measurableSet_lt measurable_const ht) ht measurable_const
  exact measurable_const.mul hp

theorem mainInitializerTauPlus_eq_of_positive
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ)
    (hpos : 0 < (gaussianInitializerProgram kernels T Ξ β).eval.value) :
    mainInitializerTauPlus kernels T Ξ = (gaussianInitializerProgram kernels T Ξ β).eval.value := by
  rw [gaussianInitializerProgram_value_eq_observable] at hpos ⊢
  exact if_pos hpos

/-- The lifted endpoints agree exactly with the division and
multiplication executed after a positive initializer result. -/
theorem mainInitializerEndpoints_eq_of_positive
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β : ℝ)
    (hpos : 0 < (gaussianInitializerProgram kernels T Ξ β).eval.value) :
    mainInitializerLowerEndpoint kernels T Ξ β =
        ((gaussianInitializerProgram kernels T Ξ β).eval.value/initializerRatio k β)/4 ∧
      mainInitializerUpperEndpoint kernels T Ξ =
        4*(gaussianInitializerProgram kernels T Ξ β).eval.value := by
  have ht := mainInitializerTauPlus_eq_of_positive kernels T Ξ β hpos
  constructor
  · unfold mainInitializerLowerEndpoint
    rw [ht,div_div,mul_comm (initializerRatio k β) 4]
  · exact congrArg (fun t : ℝ => 4*t) ht

theorem mainInitializerEndpoints_eq_of_bracket
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c)
    (T : Core k) (Ξ : Matrix (Fin k) (Fin r) ℝ) (β lower upper : ℝ)
    (hresult : (gaussianInitializerProgram kernels T Ξ β).eval.result = .bracket lower upper) :
    mainInitializerLowerEndpoint kernels T Ξ β = lower/4 ∧
      mainInitializerUpperEndpoint kernels T Ξ = 4*upper := by
  let out := (gaussianInitializerProgram kernels T Ξ β).eval
  have hpos : 0 < out.value := by
    by_contra hn
    have heq := out.result_eq
    rw [if_pos (le_of_not_gt hn)] at heq
    have hcontra : InitializerResult.bracket lower upper = .exact := hresult.symm.trans heq
    cases hcontra
  have hbracket : InitializerResult.bracket lower upper =
      .bracket (out.value/initializerRatio k β) out.value := by
    exact hresult.symm.trans (out.result_eq.trans (if_neg (not_le.mpr hpos)))
  have hends := InitializerResult.bracket.inj hbracket
  rw [hends.1,hends.2]
  exact mainInitializerEndpoints_eq_of_positive kernels T Ξ β hpos

end
end HierarchicalAbsoluteSpectral
