import HierarchicalAbsoluteSpectral.MainFamilyProgramSequences

/-! The fixed input and explicit-output circuit overheads remain
subpolynomial on every admissible integer dimension family. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

def familyCombinedKernelOverhead (χ χOut : ℕ → ℝ) (m N : ℕ) : ℝ := max (χ m) (χOut N)

theorem familyKernelOverhead_sequence {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hcore : ∀ i, m i ≤ N i)
    (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d)))
    (χ : ℕ → ℝ)
    (hχ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, χ n ≤ (n : ℝ)^ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, χ (N i) ≤ (m i : ℝ)^ε := by
  have hNreal : Tendsto (fun i => (N i : ℝ)) l atTop :=
    tendsto_atTop_mono (fun i => by exact_mod_cast hcore i) hm
  have hNnat : Tendsto N l atTop := tendsto_natCast_atTop_iff.mp hNreal
  have hb := family_sequence_dimension_powers l (fun i => (m i : ℝ)) (fun i => (N i : ℝ))
    d 1 (by norm_num) hm (hN.mono (fun i hi => by exact_mod_cast hi)) hgrowth
  intro ε hε
  have ha : 0 < 2+d := by linarith
  filter_upwards [hNnat.eventually (hχ (ε/(2+d)) (by positivity)),hb,
    hm.eventually (eventually_gt_atTop (0 : ℝ))] with i hχi hNi hmi
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ N i) hNi.2
    (by positivity : 0 ≤ ε/(2+d))
  have he : ((m i : ℝ)^(1+d+1))^(ε/(2+d)) = (m i : ℝ)^ε := by
    rw [← Real.rpow_mul hmi.le]
    congr 1
    field_simp
    <;> ring
  exact hχi.trans (hpow.trans_eq he)

theorem familyCombinedKernelOverhead_sequence {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hcore : ∀ i, m i ≤ N i)
    (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d)))
    (χ χOut : ℕ → ℝ)
    (hχ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, χ n ≤ (n : ℝ)^ε)
    (hχOut : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, χOut n ≤ (n : ℝ)^ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
      familyCombinedKernelOverhead χ χOut (m i) (N i) ≤ (m i : ℝ)^ε := by
  have hmNat : Tendsto m l atTop := tendsto_natCast_atTop_iff.mp hm
  intro ε hε
  filter_upwards [hmNat.eventually (hχ ε hε),
    familyKernelOverhead_sequence l m N d hd hm hcore hN hgrowth χOut hχOut ε hε] with i hrow hout
  exact max_le hrow hout

theorem family_degree_sequence_subpolynomial_slack {ι : Type*} (l : Filter ι)
    (m N q : ι → ℕ) (d C : ℝ) (hd : 0 < d) (hC : 0 ≤ C)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hN : ∀ᶠ i in l, 0 < N i)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d)))
    (hq : ∀ᶠ i in l, (q i : ℝ) ≤ C*((N i : ℝ)/m i)*(Real.log (m i : ℝ))^5+1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, (q i : ℝ) ≤ (m i : ℝ)^(d+ε) := by
  intro ε hε
  have hdim := family_sequence_dimension_powers l (fun i => (m i : ℝ)) (fun i => (N i : ℝ))
    d (ε/4) (by positivity) hm (hN.mono (fun i hi => by exact_mod_cast hi)) hgrowth
  have hpoly := hm.eventually (family_core_polylog_absorbed C 5 (ε/4) 0 hC (by positivity))
  have hlarge := ((tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp hm).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hq,hdim,hpoly,hlarge,hm.eventually (eventually_ge_atTop (1 : ℝ))]
    with i hqi hNi hpolyi hlargei hmi
  have hm0 : (0 : ℝ) < m i := by linarith
  have hratio : (N i : ℝ)/m i ≤ (m i : ℝ)^(d+ε/4) := by
    apply (div_le_iff₀ hm0).mpr
    apply hNi.2.trans_eq
    rw [show 1+d+ε/4 = (d+ε/4)+1 by ring,Real.rpow_add hm0,Real.rpow_one]
  have hp : C*(Real.log (m i : ℝ))^5 ≤ (m i : ℝ)^(ε/4) := by
    have he : (Real.log (m i : ℝ))^(5 : ℝ) = (Real.log (m i : ℝ))^(5 : ℕ) :=
      Real.rpow_natCast _ _
    simpa only [Real.rpow_zero,mul_one,he] using hpolyi
  have hterm := mul_le_mul hratio hp (by positivity : 0 ≤ C*(Real.log (m i : ℝ))^5)
    (Real.rpow_nonneg hm0.le _)
  have hone : 1 ≤ (m i : ℝ)^(d+ε/2) := Real.one_le_rpow hmi (by positivity)
  calc
    _ ≤ C*((N i : ℝ)/m i)*(Real.log (m i : ℝ))^5+1 := hqi
    _ = ((N i : ℝ)/m i)*(C*(Real.log (m i : ℝ))^5)+1 := by ring
    _ ≤ (m i : ℝ)^(d+ε/4)*(m i : ℝ)^(ε/4)+1 := add_le_add hterm le_rfl
    _ = (m i : ℝ)^(d+ε/2)+1 := by rw [← Real.rpow_add hm0]; congr 2 <;> ring
    _ ≤ 2*(m i : ℝ)^(d+ε/2) := by linarith
    _ ≤ (m i : ℝ)^(ε/2)*(m i : ℝ)^(d+ε/2) :=
      mul_le_mul_of_nonneg_right hlargei (Real.rpow_nonneg hm0.le _)
    _ = _ := by rw [← Real.rpow_add hm0]; congr 1 <;> ring

theorem family_raw_width_sequence {ι : Type*} (l : Filter ι)
    (m q r : ι → ℕ) (d : ℝ) (hd : FamilyExponentAdmissible d)
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hq : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, (q i : ℝ) ≤ (m i : ℝ)^(d+ε))
    (hr : ∀ᶠ i in l, (r i : ℝ) ≤ Real.sqrt (m i : ℝ)) :
    ∀ᶠ i in l, (2*q i+1)*(r i+1) < m i := by
  let ε : ℝ := (1/2-d)/2
  have hε : 0 < ε := by dsimp [ε]; linarith [hd.lt_half]
  have ha : 1/2+d+ε < 1 := by dsimp [ε]; linarith [hd.lt_half]
  filter_upwards [hq ε hε,hr,hm.eventually (family_const_mul_rpow_lt_linear 6 (1/2+d+ε) ha),
    hm.eventually (eventually_ge_atTop (1 : ℝ))] with i hqi hri hcap hmi
  have hm0 : (0 : ℝ) < m i := by linarith
  have hX : 1 ≤ (m i : ℝ)^(d+ε) := Real.one_le_rpow hmi (by linarith [hd.positive])
  have hY : 1 ≤ Real.sqrt (m i : ℝ) := (Real.le_sqrt (by norm_num) hm0.le).mpr (by linarith)
  have hfirst : 2*(q i : ℝ)+1 ≤ 3*(m i : ℝ)^(d+ε) := by linarith
  have hsecond : (r i : ℝ)+1 ≤ 2*Real.sqrt (m i : ℝ) := by linarith
  have hprod := mul_le_mul hfirst hsecond (by positivity : 0 ≤ (r i : ℝ)+1) (by positivity)
  have he : (3*(m i : ℝ)^(d+ε))*(2*Real.sqrt (m i : ℝ)) = 6*(m i : ℝ)^(1/2+d+ε) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = 6*((m i : ℝ)^(d+ε)*(m i : ℝ)^(1/2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hm0]; congr 2 <;> ring
  rw [he] at hprod
  exact_mod_cast hprod.trans_lt hcap

end
end HierarchicalAbsoluteSpectral
