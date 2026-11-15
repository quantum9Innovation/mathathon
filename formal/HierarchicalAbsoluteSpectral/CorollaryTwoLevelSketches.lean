import HierarchicalAbsoluteSpectral.CorollaryTwoLevelBudgets
import HierarchicalAbsoluteSpectral.MainSketchFiniteCore
import HierarchicalAbsoluteSpectral.RuntimeFamilyLogBudgets

/-! The actual stored sketch row counts, including their identity fallback,
and the two-level exponent bounds for these computed integers. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Matrix
open ArithmeticProgram hiding pure
variable {n m p r N : ℕ}

theorem twoLevel_boundedSketch_rows {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (g : SketchGaussianInput (dyadicPaddingLevel n)) :
    (boundedSketchProgram A ε δ hε hδ g).eval.rows =
      min n (embeddingComputedRowCount (2^dyadicPaddingLevel n) m ε δ) := by
  rw [boundedSketchProgram_eval]
  unfold boundedSketchFromSample
  split_ifs with h
  · exact (Nat.min_eq_left h).symm
  · dsimp only [sampledStoredSketchFactor]
    rw [Nat.min_eq_right (le_of_not_ge h)]
    simpa using (gaussianSRHTSample (dyadicPaddingLevel n)
      (embeddingComputedRowCount (2^dyadicPaddingLevel n) m ε δ) (min_le_left _ _) g).2.2.property

theorem TwoLevelProblem.sketchFailure_log_bound (I : TwoLevelProblem N m r)
    (c : ℝ) (hm : Real.log 2 ≤ Real.log (m:ℝ)) (hδ : (m:ℝ)^(-c) ≤ I.delta) :
    Real.log (1/I.fixed.sketchFailure) ≤ (c+6)*Real.log m := by
  have hl := I.failure_log_bound c hδ
  have h40 : Real.log (40:ℝ) ≤ 6*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 40)
      (by norm_num : (40:ℝ) ≤ (2:ℝ)^6)
    rwa [Real.log_pow] at hh
  simp only [FixedProblem.sketchFailure,Nat.cast_one]
  change Real.log (1/(I.delta/(20*((1:ℝ)+1)))) ≤ _
  norm_num only [show (20:ℝ)*(1+1)=40 by norm_num]
  have he : Real.log (1/(I.delta/40)) = Real.log 40+Real.log (1/I.delta) := by
    rw [one_div,Real.log_inv,Real.log_div I.delta_positive.ne' (by norm_num),one_div,Real.log_inv]
    ring
  rw [he]
  nlinarith only [hl,h40,hm]

theorem twoLevel_rounded_inverse_bound (x : ℝ) (a b : ℕ) (hx : 1 ≤ x) (hb : 1 ≤ b) :
    1/twoLevelRoundedPower x a b ≤ 4*x^((a:ℝ)/(b:ℝ)) := by
  have hx0 : 0 < x := by linarith
  have h := (twoLevelRoundedPower_bounds x a b hx hb).1
  calc
    _ ≤ 1/(x^(-(a:ℝ)/(b:ℝ))/4) := div_le_div_of_nonneg_left (by norm_num) (by positivity) h
    _ = _ := by rw [neg_div,Real.rpow_neg hx0.le]; field_simp

/-- Uniform in the ambient dimension and every failure probability with
the stated logarithmic budget. This bounds the executed rounded row count. -/
theorem twoLevel_embedding_rows_eventually (a b : ℕ) (hb : 1 ≤ b)
    (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (n : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      Real.log (1/δ) ≤ D*Real.log (m:ℝ) →
      (embeddingComputedRowCount n m (twoLevelRoundedPower m a b) δ:ℝ) ≤
        (m:ℝ)^(1+2*(a:ℝ)/(b:ℝ)+ε) := by
  let K : ℝ := (D+5)/Real.log 2
  let t : ℝ := 2*(a:ℝ)/(b:ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hlog := family_core_polylog_absorbed (27*K^3) 3 1 0 (by positivity) (by norm_num)
  have hpower := family_core_polylog_absorbed 262145 0 (1+t+ε) (1+t) (by norm_num) (by linarith)
  have hcast : Tendsto (fun m:ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually hlog,hcast.eventually hpower,eventually_ge_atTop (2:ℕ)]
    with m hsmall hlarge hm n δ hδ hδ1 hconfidence
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hm0 : (0:ℝ) < m := by linarith
  have hh := twoLevelRoundedPower_positive (m:ℝ) a b
  have hrow := family_embedding_rows_uniform_bound n m (twoLevelRoundedPower m a b) δ D
    hm hh hδ hδ1 hD hconfidence
  have heff : (m:ℝ)+27*(K*Real.log m)^3 ≤ 2*m := by
    have he : 27*(K*Real.log (m:ℝ))^3 = (27*K^3)*(Real.log (m:ℝ))^3 := by ring
    rw [he]
    norm_num only [Real.rpow_zero,Real.rpow_one,mul_one,Real.rpow_ofNat] at hsmall
    linarith
  have hinv := twoLevel_rounded_inverse_bound (m:ℝ) a b hm1 hb
  have hinv2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1/twoLevelRoundedPower m a b) hinv 2
  have hepow : (4*(m:ℝ)^((a:ℝ)/(b:ℝ)))^2 = 16*(m:ℝ)^t := by
    rw [mul_pow,← Real.rpow_two ((m:ℝ)^((a:ℝ)/(b:ℝ))),← Real.rpow_mul hm0.le]
    have hexp : ((a:ℝ)/(b:ℝ))*2 = t := by dsimp [t]; ring
    rw [hexp]
    norm_num
  rw [hepow] at hinv2
  have hpow : 1 ≤ (m:ℝ)^(1+t) := Real.one_le_rpow hm1 (by linarith)
  have heprod : (m:ℝ)*(m:ℝ)^t = (m:ℝ)^(1+t) := by
    calc
      _ = (m:ℝ)^(1:ℝ)*(m:ℝ)^t := by rw [Real.rpow_one]
      _ = _ := (Real.rpow_add hm0 1 t).symm
  have hbound : (embeddingComputedRowCount n m (twoLevelRoundedPower m a b) δ:ℝ) ≤
      262145*(m:ℝ)^(1+t) := by
    calc
      _ ≤ 1+8192*((m:ℝ)+27*(K*Real.log m)^3)/(twoLevelRoundedPower m a b)^2 := hrow
      _ ≤ 1+8192*(2*(m:ℝ))/(twoLevelRoundedPower m a b)^2 := by
        exact add_le_add le_rfl
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left heff (by norm_num)) (sq_nonneg _))
      _ = 1+16384*(m:ℝ)*(1/twoLevelRoundedPower m a b)^2 := by ring
      _ ≤ 1+16384*(m:ℝ)*(16*(m:ℝ)^t) := by gcongr
      _ = 1+262144*(m:ℝ)^(1+t) := by rw [← heprod]; ring
      _ ≤ 262145*(m:ℝ)^(1+t) := by nlinarith only [hpow]
  apply hbound.trans
  simpa only [Real.rpow_zero,mul_one,t] using hlarge

theorem twoLevel_sketch_row_exponents (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → ∀ n : ℕ,
      (embeddingComputedRowCount n m (twoLevelH0 m) I.fixed.sketchFailure:ℝ) ≤ (m:ℝ)^((57/50:ℝ)+ε) ∧
      (embeddingComputedRowCount n m (twoLevelH1 m) I.fixed.sketchFailure:ℝ) ≤ (m:ℝ)^((7/6:ℝ)+ε) := by
  have h0 := twoLevel_embedding_rows_eventually 7 100 (by norm_num) (c+6) ε (by linarith) hε
  have h1 := twoLevel_embedding_rows_eventually 1 12 (by norm_num) (c+6) ε (by linarith) hε
  filter_upwards [h0,h1,eventually_ge_atTop (2:ℕ)] with m h0 h1 hm N r I hδ n
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 2) hmR
  have hβ := mainSketchFailure_positive I.fixed
  have hβ1 : I.fixed.sketchFailure ≤ 1 := by
    simp only [FixedProblem.sketchFailure,Nat.cast_one]
    change I.delta/(20*((1:ℝ)+1)) ≤ 1
    linarith [I.delta_lt_one]
  have hconfidence := I.sketchFailure_log_bound c hlog hδ
  have ha := h0 n I.fixed.sketchFailure hβ hβ1 hconfidence
  have hb := h1 n I.fixed.sketchFailure hβ hβ1 hconfidence
  norm_num only [Nat.cast_ofNat,show (1+2*(7:ℝ)/100)=(57/50:ℝ) by norm_num,
    show (1+2*(1:ℝ)/12)=(7/6:ℝ) by norm_num] at ha hb
  exact ⟨ha,hb⟩

theorem twoLevel_sketch_no_identity_eventually (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ m : ℕ in atTop, ∀ (N r : ℕ) (I : TwoLevelProblem N m r),
      (m:ℝ)^(-c) ≤ I.delta → (m:ℝ)^(353/300:ℝ) ≤ N → ∀ n : ℕ,
      embeddingComputedRowCount n m (twoLevelH0 m) I.fixed.sketchFailure < N ∧
      embeddingComputedRowCount n m (twoLevelH1 m) I.fixed.sketchFailure < N := by
  filter_upwards [twoLevel_sketch_row_exponents c (1/300) hc (by norm_num),
    eventually_ge_atTop (2:ℕ)] with m hm hm2 N r I hδ hN n
  have hrows := hm N r I hδ n
  have hmR : (1:ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have h0 : (m:ℝ)^((57/50:ℝ)+1/300) < (m:ℝ)^(353/300:ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hmR (by norm_num)
  have h1 : (m:ℝ)^((7/6:ℝ)+1/300) < (m:ℝ)^(353/300:ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hmR (by norm_num)
  constructor
  · exact_mod_cast hrows.1.trans_lt (h0.trans_le hN)
  · exact_mod_cast hrows.2.trans_lt (h1.trans_le hN)

end
end HierarchicalAbsoluteSpectral
