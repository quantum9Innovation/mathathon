import HierarchicalAbsoluteSpectral.CorollaryOptimizedRuntimeOutput

/-! Ambient small-core bounds for every actual support dimension, including
dimension zero.  These are additive charges in the comparator runtime. -/

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
variable {m k w : ℕ}

theorem comparator_kernel_envelope_ambient
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C E : ℝ) (hC : 0 < C)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 1 ≤ m) (hk : k ≤ m) :
    (kernelEnvelope kernels k:ℝ) ≤ C*(m:ℝ)^E := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ:Finset
    (Fin (k+1) × Fin (k+1) × Fin (k+1))) Finset.univ_nonempty (kernelEnvelopeEntry kernels k)
  change ((Finset.univ.sup (kernelEnvelopeEntry kernels k):ℕ):ℝ) ≤ _
  rw [hi]
  unfold kernelEnvelopeEntry
  split_ifs with hz
  · simp only [Nat.cast_zero]
    positivity
  · exact hK _ _ _ m hm (by omega) (by omega) (by omega)

theorem comparator_cholesky_cost_ambient
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C E : ℝ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 1 ≤ m) (hk : k ≤ m) :
    (choleskyCost kernels k:ℝ) ≤ 9*(C+1)*(m:ℝ)^E := by
  by_cases hk1 : 1 ≤ k
  · apply (choleskyCost_bound kernels C E hC hE (fun a b c D _ => hK a b c D) k hk1).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast hk) (by linarith)
  · have hk0 : k=0 := by omega
    rw [hk0,choleskyCost]
    simp only [Nat.cast_zero]
    positivity

theorem comparator_base_cost_ambient
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C E : ℝ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 1 ≤ m) (hk : k ≤ m) (h : ℝ) (hh : 0 < h) :
    (baseConstructionCost kernels k h hh:ℝ) ≤
      100*(baseNewtonSteps h hh+1:ℕ)*(C+1)*(m:ℝ)^E := by
  let P : ℝ := (m:ℝ)^E
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hm) (by linarith)
  have hCP : 0 ≤ C*P := mul_nonneg hC.le (by linarith)
  have hchol := comparator_cholesky_cost_ambient kernels C E hC hE hK hm hk
  have hkernel := hK k k k m hm hk hk hk
  have hkR : (k:ℝ) ≤ m := by exact_mod_cast hk
  have hsquare : (k:ℝ)*(k:ℝ) ≤ P := by
    have h1 := mul_le_mul hkR hkR (Nat.cast_nonneg k) (Nat.cast_nonneg m)
    have h2 : (m:ℝ)*(m:ℝ) ≤ P := by
      simpa only [Real.rpow_two,pow_two] using
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm : (1:ℝ) ≤ m) hE
    exact h1.trans h2
  have hfixed : 2*(choleskyCost kernels k:ℝ)+5*((kernels k k k).cost:ℝ)+2+2*(k:ℝ)*k ≤
      30*(C+1)*P := by dsimp [P] at hP1 hsquare hCP ⊢; nlinarith
  have hstep : (choleskyCost kernels k:ℝ)+2*((kernels k k k).cost:ℝ)+2*(k:ℝ)*k ≤
      20*(C+1)*P := by dsimp [P] at hsquare hCP ⊢; nlinarith
  have hloop := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg (baseNewtonSteps h hh))
  unfold baseConstructionCost
  push_cast
  dsimp [P] at hfixed hloop ⊢
  nlinarith [mul_nonneg (show (0:ℝ) ≤ baseNewtonSteps h hh by positivity)
    (show 0 ≤ (C+1)*(m:ℝ)^E by positivity)]

theorem comparator_range_algebra_ambient
    (kernels : ∀ a b c : ℕ, ArithmeticKernel a b c) (C E : ℝ) (hC : 0 < C) (hE : 2 ≤ E)
    (hK : ∀ a b c D : ℕ, 1 ≤ D → a ≤ D → b ≤ D → c ≤ D →
      ((kernels a b c).cost:ℝ) ≤ C*(D:ℝ)^E)
    (hm : 1 ≤ m) (hk : k ≤ m) (hw : w ≤ m) :
    (algebraRangeWorkCap kernels k w:ℝ) ≤ 11*(C+1)*(m:ℝ)^E := by
  have he := comparator_kernel_envelope_ambient kernels C E hC hK hm (max_le hk hw)
  have hp := comparator_psd_cost_ambient kernels C E hC hE hK hm hw
  unfold algebraRangeWorkCap
  push_cast
  have hpow : 0 ≤ (m:ℝ)^E := by positivity
  nlinarith

theorem comparator_inertia_ceiling_ambient
    (C E : ℝ) (hC : 0 < C) (hE : 2 ≤ E) (hm : 1 ≤ m) (hk : k ≤ m) :
    (⌈212*(C+1)*(k:ℝ)^E⌉₊:ℝ) ≤ 213*(C+1)*(m:ℝ)^E := by
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast hk : (k:ℝ) ≤ m)
    (show 0 ≤ E by linarith)
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 212*(C+1)*(k:ℝ)^E by positivity)).le
  have hP1 : (1:ℝ) ≤ (m:ℝ)^E := Real.one_le_rpow (by exact_mod_cast hm) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 212*(C+1) by positivity)
  nlinarith

end
end HierarchicalAbsoluteSpectral
