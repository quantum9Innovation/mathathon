import HierarchicalAbsoluteSpectral.CorollaryTwoLevelRuntimeFinalKernels
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelUniformExponents
import HierarchicalAbsoluteSpectral.CorollaryTwoLevelProbability

/-! The actual dense expansion kernel uses the same fixed arithmetic
family as construction. All bounds are uniform in the returned width. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Matmul.RectangularPrograms
open scoped Topology
attribute [local irreducible] twoLevelRuntimeFinalKernels twoLevelConstructionProgram
  twoLevelConstructionExplicitWork twoLevelFullExplicitWork

theorem twoLevel_expansion_cost_shape (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop, ∀ N r : ℕ,
      (N:ℝ) ≤ (m:ℝ)^((59/50:ℝ)+δ) → r ≤ ⌈(m:ℝ)^(14/25:ℝ)⌉₊ →
      ∀ w ≤ r, ((twoLevelRuntimeFinalKernels m N w N).cost:ℝ) ≤
        (m:ℝ)^((59/25:ℝ)+ε) := by
  obtain ⟨δ,hδ,hK⟩ := twoLevelRuntimeFinalKernels_scalene ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hK,eventually_ge_atTop (1:ℕ)] with m hm hm1 N r hN hr w hw
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hside : N ≤ width ((59/50:ℝ)+δ) m := by
    exact_mod_cast hN.trans (Nat.le_ceil ((m:ℝ)^((59/50:ℝ)+δ)))
  have hwidth : w ≤ width ((14/25:ℝ)+δ) m := by
    apply hw.trans
    apply hr.trans
    exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hmR (by linarith))
  have hfit : twoLevelFullOutputShape.Fits δ m N w N := ⟨hside,hwidth,hside⟩
  have hcost := hm twoLevelFullOutputShape twoLevelRuntimeFinalShapes_fullOutput N w N hfit
  simpa only [twoLevelFullOutputShape_bound] using hcost

theorem twoLevel_expansion_cost_family {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (hm : Tendsto m l atTop) (hN : ∀ᶠ i in l, 0 < N i)
    (hr : ∀ᶠ i in l, r i ≤ ⌈(m i:ℝ)^(14/25:ℝ)⌉₊)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ w ≤ r i,
      ((twoLevelRuntimeFinalKernels (m i) (N i) w (N i)).cost:ℝ) ≤ (N i:ℝ)^((2:ℝ)+ε) := by
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hm
  have hNR : ∀ᶠ i in l, (0:ℝ) < N i := hN.mono (fun i hi => by exact_mod_cast hi)
  have hg : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+(9/50:ℝ))) := by
    convert hgrowth using 1 <;> norm_num
  have hcost : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, ∀ w : {w:ℕ // w ≤ r i},
      ((twoLevelRuntimeFinalKernels (m i) (N i) w.val (N i)).cost:ℝ) ≤ (m i:ℝ)^((59/25:ℝ)+η) := by
    intro η hη
    obtain ⟨δ,hδ,hK⟩ := twoLevel_expansion_cost_shape η hη
    have hdim := family_sequence_dimension_powers l (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
      (9/50) δ hδ hmR hNR hg
    filter_upwards [hm.eventually hK,hdim,hr] with i hKi hdi hri w
    exact hKi (N i) (r i) (by convert hdi.2 using 1 <;> norm_num) hri w.val w.property
  have h := twoLevel_exponent_transfer_uniform (α := fun i => {w:ℕ // w ≤ r i}) l
    (fun i => (m i:ℝ)) (fun i => (N i:ℝ))
    (fun i w => ((twoLevelRuntimeFinalKernels (m i) (N i) w.val (N i)).cost:ℝ))
    (59/25) 2 (by norm_num) (by norm_num) hmR hNR hgrowth hcost
  intro ε hε
  filter_upwards [h ε hε] with i hi w hw
  exact hi ⟨w,hw⟩

theorem twoLevel_constructed_expansion_cost_family {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, TwoLevelProblem (N i) (m i) (r i))
    (hm : Tendsto m l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      ((twoLevelRuntimeFinalKernels (m i) (N i)
        (twoLevelConstructionProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.width (N i)).cost:ℝ) ≤
          (N i:ℝ)^((2:ℝ)+ε) := by
  have hN : ∀ᶠ i in l, 0 < N i := Eventually.of_forall (fun i =>
    lt_of_lt_of_le (show 0 < m i from (I i).core_positive) (I i).core_le_side)
  have hr : ∀ᶠ i in l, r i ≤ ⌈(m i:ℝ)^(14/25:ℝ)⌉₊ := Eventually.of_forall (fun i => (I i).rank_le_power)
  intro ε hε
  filter_upwards [twoLevel_expansion_cost_family l m N r hm hN hr hgrowth ε hε] with i hi g
  exact hi _ (twoLevelConstructionProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.width_le

/-- Analytic assembly lemma. The construction premise is discharged by
the actual finite-cap asymptotic theorem in the final caller. -/
theorem twoLevel_full_cost_of_construction_bound {ι : Type*} (l : Filter ι)
    (m N r : ι → ℕ) (I : ∀ i, TwoLevelProblem (N i) (m i) (r i))
    (hm : Tendsto m l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (59/50:ℝ)))
    (hconstruction : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤
        (N i:ℝ)^((6724/3363:ℝ)+η)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : MainRandomTape (I i).fixed,
      (twoLevelFullExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤ (N i:ℝ)^((2:ℝ)+ε) := by
  intro ε hε
  let η : ℝ := (2-(6724/3363:ℝ))/2
  have hη : 0 < η := by norm_num [η]
  have hη2 : (6724/3363:ℝ)+η ≤ 2 := by norm_num [η]
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hm
  have hlarge := ((tendsto_rpow_atTop (show 0 < ε/2 by positivity)).comp hmR).eventually
    (eventually_ge_atTop (3:ℝ))
  filter_upwards [hconstruction η hη,twoLevel_constructed_expansion_cost_family l m N r I hm hgrowth
    (ε/2) (by positivity),hlarge,hmR.eventually (eventually_ge_atTop (1:ℝ))]
    with i hc hk hlarge hmi g
  have hm0 : (0:ℝ) < m i := by linarith
  have hmN : (m i:ℝ) ≤ N i := by exact_mod_cast (I i).core_le_side
  have hNi : (1:ℝ) ≤ N i := hmi.trans hmN
  have hN0 : (0:ℝ) < N i := by linarith
  have hC : (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) ≤ (N i:ℝ)^2 :=
    (hc g).trans (by simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hNi hη2)
  have hNpow : (N i:ℝ)^2 ≤ (N i:ℝ)^((2:ℝ)+ε/2) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hNi (show (2:ℝ) ≤ 2+ε/2 by linarith)
  have hthree : 3 ≤ (N i:ℝ)^(ε/2) := hlarge.trans (Real.rpow_le_rpow hm0.le hmN (by positivity))
  have he := twoLevelFullExplicitWork_split (twoLevelRuntimeFinalKernels (m i)) (I i) g
  have heR : (twoLevelFullExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ) =
      (twoLevelConstructionExplicitWork (twoLevelRuntimeFinalKernels (m i)) (I i) g:ℝ)+(N i:ℝ)^2+
        ((twoLevelRuntimeFinalKernels (m i) (N i)
          (twoLevelConstructionProgram (twoLevelRuntimeFinalKernels (m i)) (I i) g).eval.width (N i)).cost:ℝ) := by
    have hcast := congrArg (fun x:ℕ => (x:ℝ)) he
    simpa only [Nat.cast_add,Nat.cast_mul,pow_two] using hcast
  rw [heR]
  calc
    _ ≤ (N i:ℝ)^2+(N i:ℝ)^2+(N i:ℝ)^((2:ℝ)+ε/2) := add_le_add (add_le_add hC le_rfl) (hk g)
    _ ≤ 3*(N i:ℝ)^((2:ℝ)+ε/2) := by linarith only [hNpow]
    _ ≤ (N i:ℝ)^(ε/2)*(N i:ℝ)^((2:ℝ)+ε/2) :=
      mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [← Real.rpow_add hN0]; congr 1 <;> ring

end
end HierarchicalAbsoluteSpectral
