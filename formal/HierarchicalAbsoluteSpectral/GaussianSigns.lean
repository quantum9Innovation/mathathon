import HierarchicalAbsoluteSpectral.GaussianBasics
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

def gaussianSignBit (x : ℝ) : ZMod 2 := if x ≤ 0 then 0 else 1

theorem gaussianSignBit_measurable : Measurable gaussianSignBit :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem gaussianReal_zero_half : (gaussianReal 0 1).real (Iic (0 : ℝ)) = 1/2 := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have hp : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, by simpa using gaussianReal_map_neg (μ := 0) (v := 1)⟩
  have heq : (fun x : ℝ => -x) ⁻¹' Iic (0 : ℝ) = Ici 0 := by ext x; simp
  have hm := hp.measureReal_preimage (s := Iic 0) measurableSet_Iic.nullMeasurableSet
  rw [heq] at hm
  have hpos : (gaussianReal 0 1).real (Ioi (0 : ℝ)) = (gaussianReal 0 1).real (Iic (0 : ℝ)) :=
    (measureReal_congr Ioi_ae_eq_Ici).trans hm
  have ht := probReal_add_probReal_compl (μ := gaussianReal 0 1) (s := Iic (0 : ℝ)) measurableSet_Iic
  rw [Set.compl_Iic, hpos] at ht
  linarith

theorem gaussianSignBit_probability (b : ZMod 2) :
    (gaussianReal 0 1).real {x | gaussianSignBit x = b} = 1/2 := by
  have hzero : {x | gaussianSignBit x = (0 : ZMod 2)} = Iic (0 : ℝ) := by
    ext x
    by_cases hx : x ≤ 0 <;> simp [gaussianSignBit, hx]
  have hone : {x | gaussianSignBit x = (1 : ZMod 2)} = (Iic (0 : ℝ))ᶜ := by
    ext x
    by_cases hx : x ≤ 0 <;> simp [gaussianSignBit, hx]
  have hb : b = 0 ∨ b = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b
  rcases hb with rfl | rfl
  · rw [hzero]
    exact gaussianReal_zero_half
  · rw [hone, measureReal_compl measurableSet_Iic, probReal_univ, gaussianReal_zero_half]
    norm_num

def gaussianSignAssignment (n : ℕ) (g : Fin n → ℝ) : Fin n → ZMod 2 :=
  fun i => gaussianSignBit (g i)

theorem gaussianSignAssignment_measurable (n : ℕ) : Measurable (gaussianSignAssignment n) := by
  apply measurable_pi_lambda
  intro i
  exact gaussianSignBit_measurable.comp (measurable_pi_apply i)

/-- Every bit assignment has the exact independent-product probability. -/
theorem gaussianSignAssignment_probability (n : ℕ) (b : Fin n → ZMod 2) :
    (gaussianVector n).real {g | gaussianSignAssignment n g = b} = (1/2 : ℝ)^n := by
  have heq : {g | gaussianSignAssignment n g = b} =
      Set.univ.pi (fun i : Fin n => {x | gaussianSignBit x = b i}) := by
    ext g
    simp [gaussianSignAssignment, funext_iff]
  rw [heq, measureReal_def, gaussianVector, Measure.pi_pi, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, gaussianSignBit_probability]
  simp

theorem gaussianSignAssignment_reindex_probability {ι : Type*} [Fintype ι]
    (n : ℕ) (e : ι ≃ Fin n) (b : ι → ZMod 2) :
    (gaussianVector n).real {g | (fun i : ι => gaussianSignBit (g (e i))) = b} = (1/2 : ℝ)^n := by
  have heq : {g : Fin n → ℝ | (fun i : ι => gaussianSignBit (g (e i))) = b} =
      {g | gaussianSignAssignment n g = (fun j => b (e.symm j))} := by
    ext g
    simp only [Set.mem_setOf_eq, funext_iff, gaussianSignAssignment]
    constructor
    · intro h j
      simpa using h (e.symm j)
    · intro h i
      simpa using h (e i)
  rw [heq]
  exact gaussianSignAssignment_probability _ _

end
end HierarchicalAbsoluteSpectral
