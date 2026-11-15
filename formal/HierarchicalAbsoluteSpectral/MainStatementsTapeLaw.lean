import HierarchicalAbsoluteSpectral.GaussianRestriction
import Mathlib.Probability.ProductMeasure

namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

theorem gaussianTape_injection_measurePreserving {Ω J : Type*} [Fintype Ω] [Fintype J]
    (e : J ↪ Ω) :
    MeasurePreserving (fun g : Ω → ℝ => fun j => g (e j))
      (Measure.pi (fun _ : Ω => gaussianReal 0 1))
      (Measure.pi (fun _ : J => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun j : Ω => fun g : Ω → ℝ => g j)
      (Measure.pi (fun _ : Ω => gaussianReal 0 1)) :=
    iIndepFun_pi (X:=fun _ => id) (μ:=fun _ : Ω => gaussianReal 0 1) (fun _ => aemeasurable_id)
  have his := hi.precomp e.injective
  refine ⟨by fun_prop,?_⟩
  rw [his.map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)]
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : Ω => gaussianReal 0 1) (e j)).map_eq

theorem gaussianFiniteCurry_measurePreserving {A B : Type*} [Fintype A] [Fintype B] :
    MeasurePreserving (MeasurableEquiv.curry A B ℝ)
      (Measure.pi (fun _ : A × B => gaussianReal 0 1))
      (Measure.pi (fun _ : A => Measure.pi (fun _ : B => gaussianReal 0 1))) := by
  refine ⟨(MeasurableEquiv.curry A B ℝ).measurable,?_⟩
  simpa only [Measure.infinitePi_eq_pi] using
    Measure.infinitePi_map_curry (fun _ : A => fun _ : B => gaussianReal 0 1)

theorem gaussianTape_array3_measurePreserving {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] (e : (A × (B × C)) ↪ Ω) :
    MeasurePreserving (fun g : Ω → ℝ => fun a b c => g (e (a,(b,c))))
      (Measure.pi (fun _ : Ω => gaussianReal 0 1))
      (Measure.pi (fun _ : A => Measure.pi (fun _ : B => Measure.pi (fun _ : C => gaussianReal 0 1)))) := by
  have h₁ := (gaussianFiniteCurry_measurePreserving (A:=A) (B:=B × C)).comp
    (gaussianTape_injection_measurePreserving e)
  have h₂ := measurePreserving_pi
    (fun _ : A => Measure.pi (fun _ : B × C => gaussianReal 0 1))
    (fun _ : A => Measure.pi (fun _ : B => Measure.pi (fun _ : C => gaussianReal 0 1)))
    (fun _ => gaussianFiniteCurry_measurePreserving (A:=B) (B:=C))
  exact h₂.comp h₁

theorem gaussianTape_array4_measurePreserving {Ω A B C D : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (e : (A × (B × (C × D))) ↪ Ω) :
    MeasurePreserving (fun g : Ω → ℝ => fun a b c d => g (e (a,(b,(c,d)))))
      (Measure.pi (fun _ : Ω => gaussianReal 0 1))
      (Measure.pi (fun _ : A => Measure.pi (fun _ : B => Measure.pi (fun _ : C =>
        Measure.pi (fun _ : D => gaussianReal 0 1))))) := by
  have h₁ := (gaussianFiniteCurry_measurePreserving (A:=A) (B:=B × (C × D))).comp
    (gaussianTape_injection_measurePreserving e)
  have h₂ := measurePreserving_pi
    (fun _ : A => Measure.pi (fun _ : B × (C × D) => gaussianReal 0 1))
    (fun _ : A => Measure.pi (fun _ : B => Measure.pi (fun _ : C => Measure.pi (fun _ : D => gaussianReal 0 1))))
    (fun _ => gaussianTape_array3_measurePreserving (Function.Embedding.refl (B × (C × D))))
  exact h₂.comp h₁

theorem gaussianTape_blocks_measurePreserving {Ω : Type*} [Fintype Ω]
    (a b : ℕ) (e : (Fin a × Fin b) ↪ Ω) :
    MeasurePreserving (fun g : Ω → ℝ => fun i j => g (e (i,j)))
      (Measure.pi (fun _ : Ω => gaussianReal 0 1)) (gaussianColumns b a) := by
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin a) (Fin b) ℝ)
      (Measure.pi (fun _ : Fin a × Fin b => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin a => Measure.pi (fun _ : Fin b => gaussianReal 0 1))) := by
    refine ⟨(MeasurableEquiv.curry (Fin a) (Fin b) ℝ).measurable,?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun _ : Fin a => fun _ : Fin b => gaussianReal 0 1)
  exact hc.comp (gaussianTape_injection_measurePreserving e)

theorem gaussianThreeBlocks_measurePreserving (b : ℕ) :
    MeasurePreserving (fun G : Fin 3 → Fin b → ℝ => (G 0,(G 1,G 2)))
      (gaussianColumns b 3) ((gaussianVector b).prod ((gaussianVector b).prod (gaussianVector b))) := by
  have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => gaussianVector b) (0 : Fin 3)
  have htwo := measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianVector b)
  have hp := (MeasurePreserving.id (gaussianVector b)).prod htwo
  convert hp.comp hsplit using 1 <;> first | rfl | (ext G i <;> rfl)

theorem gaussianTape_threeBlocks_measurePreserving {Ω : Type*} [Fintype Ω]
    (b : ℕ) (e : (Fin 3 × Fin b) ↪ Ω) :
    MeasurePreserving (fun g : Ω → ℝ =>
      (fun j => g (e (0,j)),(fun j => g (e (1,j)),fun j => g (e (2,j)))))
      (Measure.pi (fun _ : Ω => gaussianReal 0 1))
      ((gaussianVector b).prod ((gaussianVector b).prod (gaussianVector b))) :=
  (gaussianThreeBlocks_measurePreserving b).comp (gaussianTape_blocks_measurePreserving 3 b e)

end
end HierarchicalAbsoluteSpectral
