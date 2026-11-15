import HierarchicalAbsoluteSpectral.InterpolationError

/-! Finite dyadic degree selection for Lemma 4. The stopping predicate
uses only field operations, positive square roots and comparisons. Logs
are used to bound the stopping time, never to construct coefficients. -/

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
noncomputable section
open Set Polynomial

def squaredDecay (r : ℝ) : ℕ → ℝ := Nat.rec r (fun _ u => u*u)

theorem squaredDecay_eq_pow (r : ℝ) (s : ℕ) : squaredDecay r s = r^(2^s) := by
  induction s with
  | zero => simp [squaredDecay]
  | succ s ih =>
    change squaredDecay r s * squaredDecay r s = _
    rw [ih, ← pow_two, ← pow_mul, pow_succ]

theorem dyadic_stopping_exists (r δ : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (hδ : 0 < δ) :
    ∃ s : ℕ, r^(2^s) ≤ δ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hr'
  exact ⟨n, (pow_le_pow_of_le_one hr hr'.le Nat.lt_two_pow_self.le).trans hn.le⟩

def inverseRootLevel (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) : ℕ :=
  Nat.find (dyadic_stopping_exists (1+η/4)⁻¹ (τ*η*Real.sqrt η/1000)
    (by positivity) ((inv_lt_one₀ (by positivity)).mpr (by linarith)) (by positivity))

theorem inverseRootLevel_stops (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    ((1+η/4)⁻¹)^(2^(inverseRootLevel η τ hη hτ)) ≤ τ*η*Real.sqrt η/1000 := by
  unfold inverseRootLevel
  exact Nat.find_spec (p := fun s : ℕ => ((1+η/4)⁻¹)^(2^s) ≤ τ*η*Real.sqrt η/1000) _

theorem inverseRootLevel_minimal (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ)
    (s : ℕ) (hs : s < inverseRootLevel η τ hη hτ) :
    τ*η*Real.sqrt η/1000 < ((1+η/4)⁻¹)^(2^s) := by
  unfold inverseRootLevel at hs
  exact lt_of_not_ge (Nat.find_min _ hs)

theorem inverseRootLevel_degree_bound (η τ : ℝ) (hη : 0 < η) (hη' : η ≤ 1/8)
    (hτ : 0 < τ) (hτ' : τ < 1/4) :
    (2^(inverseRootLevel η τ hη hτ) : ℝ) ≤
      1 + (16/η)*Real.log (1000/(τ*η*Real.sqrt η)) := by
  let L : ℝ := Real.log (1000/(τ*η*Real.sqrt η))
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hs1 : Real.sqrt η ≤ 1 := by
    nlinarith [Real.sq_sqrt hη.le, Real.sqrt_nonneg η]
  have htη : τ*η < 1 := by nlinarith
  have hsmall : τ*η*Real.sqrt η < 1 := by
    calc
      τ*η*Real.sqrt η ≤ τ*η*1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ < 1 := by simpa using htη
  have harg : 1 < 1000/(τ*η*Real.sqrt η) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  have hL : 0 < L := Real.log_pos harg
  have hlog : η/8 ≤ Real.log (1+η/4) := by
    have hl := Real.le_log_one_add_of_nonneg (show 0 ≤ η/4 by positivity)
    have hl' : η/8 ≤ 2*(η/4)/(η/4+2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    exact hl'.trans hl
  cases heq : inverseRootLevel η τ hη hτ with
  | zero =>
    simp only [pow_zero]
    have : 0 ≤ (16/η)*L := by positivity
    change 1 ≤ 1+(16/η)*L
    linarith
  | succ s =>
    have hm := inverseRootLevel_minimal η τ hη hτ s (by omega)
    have hlogm := Real.log_lt_log (by positivity : 0 < τ*η*Real.sqrt η/1000) hm
    rw [Real.log_pow, Real.log_inv] at hlogm
    have he : Real.log (τ*η*Real.sqrt η/1000) = -L := by
      dsimp [L]
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [he] at hlogm
    push_cast at hlogm
    have hp : (0:ℝ) ≤ 2^s := by positivity
    have hprod := mul_le_mul_of_nonneg_left hlog hp
    have hnum : (2:ℝ)^s*η < 8*L := by nlinarith
    rw [pow_succ]
    change (2:ℝ)^s*2 ≤ 1+(16/η)*L
    apply (mul_le_mul_iff_right₀ hη).mp
    have hid : η*(1+(16/η)*L) = η+16*L := by field_simp
    rw [hid]
    nlinarith

theorem inverseRootInterpolant_relative_error (s : ℕ) (η τ : ℝ)
    (hη : 0 < η) (hη' : η ≤ 1/8) (hτ : 0 < τ)
    (hstop : ((1+η/4)⁻¹)^(2^s) ≤ τ*η*Real.sqrt η/1000)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    |(inverseRootInterpolant s η).eval x * Real.sqrt (absoluteRootScalar η x) - 1| ≤ τ := by
  have herr := inverseRootInterpolant_uniform_error s η x hη hη' hx
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have habs : |(inverseRootInterpolant s η).eval x-inverseRootValue η x| ≤ τ/2 := by
    calc
      _ ≤ (24/(η*Real.sqrt η))*((1+η/4)⁻¹)^(2^s) := herr
      _ ≤ (24/(η*Real.sqrt η))*(τ*η*Real.sqrt η/1000) :=
        mul_le_mul_of_nonneg_left hstop (by positivity)
      _ = 24*τ/1000 := by field_simp
      _ ≤ τ/2 := by linarith
  have hf := scalar_absolute_root_upper η x hη.le hx.1 hx.2
  have hf0 := scalar_absolute_root_pos η x hη
  have hfs : 0 ≤ Real.sqrt (absoluteRootScalar η x) := Real.sqrt_nonneg _
  have hfs' : Real.sqrt (absoluteRootScalar η x) ≤ 2 := by
    nlinarith [Real.sq_sqrt hf0.le]
  have heq : (inverseRootInterpolant s η).eval x * Real.sqrt (absoluteRootScalar η x) - 1 =
      ((inverseRootInterpolant s η).eval x-inverseRootValue η x)*
        Real.sqrt (absoluteRootScalar η x) := by
    rw [sub_mul, inverseRootValue_exact η x hη]
  rw [heq, abs_mul, abs_of_nonneg hfs]
  calc
    _ ≤ (τ/2)*2 := mul_le_mul habs hfs' hfs (by positivity)
    _ = τ := by ring

theorem inverseRootPolynomial_exists (η τ : ℝ) (hη : 0 < η) (hη' : η ≤ 1/8)
    (hτ : 0 < τ) (hτ' : τ < 1/4) :
    ∃ s : ℕ, (2^s : ℝ) ≤ 1+(16/η)*Real.log (1000/(τ*η*Real.sqrt η)) ∧
      (inverseRootInterpolant s η).degree < (2^s : ℕ) ∧
      ∀ x ∈ Icc (-1:ℝ) 1,
        |(inverseRootInterpolant s η).eval x * Real.sqrt (absoluteRootScalar η x)-1| ≤ τ := by
  refine ⟨inverseRootLevel η τ hη hτ,
    inverseRootLevel_degree_bound η τ hη hη' hτ hτ', inverseRootInterpolant_degree _ _, ?_⟩
  exact inverseRootInterpolant_relative_error _ η τ hη hη' hτ
    (inverseRootLevel_stops η τ hη hτ)

theorem inverseRoot_log_budget (η τ : ℝ) (hη : 0 < η) (hη' : η ≤ 1/8)
    (hτ : 0 < τ) (hτ' : τ < 1/4) :
    1 ≤ Real.log (1/(τ*η)) ∧
      Real.log (1000/(τ*η*Real.sqrt η)) ≤ 1001*Real.log (1/(τ*η)) := by
  have hτη : 0 < τ*η := mul_pos hτ hη
  have hτη' : τ*η < 1/32 := by nlinarith
  have harg : 32 ≤ 1/(τ*η) := by
    apply (le_div_iff₀ hτη).mpr
    linarith
  have h32 : (1:ℝ) ≤ Real.log 32 := by
    have h := Real.le_log_one_add_of_nonneg (by norm_num : (0:ℝ) ≤ 31)
    norm_num at h
    linarith
  have hW : 1 ≤ Real.log (1/(τ*η)) :=
    h32.trans (Real.log_le_log (by norm_num) harg)
  have hηlog : Real.log η ≤ 0 := Real.log_nonpos hη.le (by linarith)
  have hτlog : Real.log τ ≤ 0 := Real.log_nonpos hτ.le (by linarith)
  have h1000 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1000)
  have hsplit : Real.log (1000/(τ*η*Real.sqrt η)) =
      Real.log 1000 - Real.log τ - (3/2)*Real.log η := by
    rw [Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by positivity : τ*η ≠ 0) (Real.sqrt_pos.mpr hη).ne',
      Real.log_mul hτ.ne' hη.ne', Real.log_sqrt hη.le]
    ring
  have hsplitW : Real.log (1/(τ*η)) = -Real.log τ - Real.log η := by
    rw [Real.log_div one_ne_zero hτη.ne', Real.log_one, Real.log_mul hτ.ne' hη.ne']
    ring
  refine ⟨hW, ?_⟩
  rw [hsplit, hsplitW]
  rw [hsplitW] at hW
  nlinarith

/-- An explicit uniform constant makes the paper's degree bound unambiguous.
The larger constant here is only an upper bound for the same stopping rule. -/
theorem inverseRootLevel_degree_bound_simple (η τ : ℝ) (hη : 0 < η) (hη' : η ≤ 1/8)
    (hτ : 0 < τ) (hτ' : τ < 1/4) :
    (2^(inverseRootLevel η τ hη hτ) : ℝ) ≤
      (17000/η)*Real.log (1/(τ*η)) := by
  have hn := inverseRootLevel_degree_bound η τ hη hη' hτ hτ'
  have hL := inverseRoot_log_budget η τ hη hη' hτ hτ'
  have hmul := mul_le_mul_of_nonneg_left hL.2 (show 0 ≤ 16/η by positivity)
  have hcombine : 1+(16/η)*Real.log (1000/(τ*η*Real.sqrt η)) ≤
      (17000/η)*Real.log (1/(τ*η)) := by
    apply (mul_le_mul_iff_right₀ hη).mp
    have he1 : η*(1+(16/η)*Real.log (1000/(τ*η*Real.sqrt η))) =
        η+16*Real.log (1000/(τ*η*Real.sqrt η)) := by field_simp
    have he2 : η*((17000/η)*Real.log (1/(τ*η))) = 17000*Real.log (1/(τ*η)) := by
      field_simp
    rw [he1, he2]
    nlinarith [hL.1, hL.2]
  exact hn.trans hcombine

/-- A specific finite polynomial, including total behavior outside the
positive parameter domain. Every value is obtained by interpolation. -/
def inverseRootPolynomial (η τ : ℝ) : ℝ[X] :=
  if hη : 0 < η then
    if hτ : 0 < τ then inverseRootInterpolant (inverseRootLevel η τ hη hτ) η
    else 0
  else 0

theorem inverseRootPolynomial_eq (η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    inverseRootPolynomial η τ = inverseRootInterpolant (inverseRootLevel η τ hη hτ) η := by
  simp only [inverseRootPolynomial, dif_pos hη, dif_pos hτ]

theorem inverseRootPolynomial_relative_error (η τ : ℝ) (hη : 0 < η) (hη' : η ≤ 1/8)
    (hτ : 0 < τ) (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    |(inverseRootPolynomial η τ).eval x * Real.sqrt (absoluteRootScalar η x)-1| ≤ τ := by
  rw [inverseRootPolynomial_eq η τ hη hτ]
  exact inverseRootInterpolant_relative_error _ η τ hη hη' hτ
    (inverseRootLevel_stops η τ hη hτ) x hx

theorem inverseRootPolynomial_degree (η τ : ℝ) (hη : 0 < η) (hη' : η ≤ 1/8)
    (hτ : 0 < τ) (hτ' : τ < 1/4) :
    ∃ n : ℕ, (inverseRootPolynomial η τ).degree < n ∧
      (n : ℝ) ≤ (17000/η)*Real.log (1/(τ*η)) := by
  refine ⟨2^(inverseRootLevel η τ hη hτ), ?_,
    by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      inverseRootLevel_degree_bound_simple η τ hη hη' hτ hτ'⟩
  rw [inverseRootPolynomial_eq η τ hη hτ]
  exact inverseRootInterpolant_degree _ _

end
end HierarchicalAbsoluteSpectral
