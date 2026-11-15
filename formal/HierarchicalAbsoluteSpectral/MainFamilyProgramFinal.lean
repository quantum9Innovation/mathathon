import HierarchicalAbsoluteSpectral.MainFamilyProgramVerified
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinal

/-! The complete growing-depth original-input caller. The kernel family
is fixed from d before the dimension sequence or the asymptotic slack is
supplied. The same counted program supplies the factors, dense output,
probability guarantee, computed schedule and explicit-output runtime. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator

def growingFamilySlack (d : ℝ) : ℝ := (2+2*d-9/4)/2

theorem growingFamilySlack_positive (d : ℝ) (hd : (1/8 : ℝ) < d) :
    0 < growingFamilySlack d := by unfold growingFamilySlack; linarith

def growingFamilyKernelImplementation (d : ℝ) (hd : (1/8 : ℝ) < d) :
    FamilyFinalKernelImplementation (growingFamilySlack d) :=
  familyFinalKernelImplementation (growingFamilySlack d) (growingFamilySlack_positive d hd)

/-- `tailSingularValue (A*B) r` is zero-indexed, hence the paper's sigma_(r+1).
No sketch, hierarchy, threshold, capture, or runtime certificate is an input. -/
theorem growingDepthProgram_family_theorem {ι : Type*}
    (d c : ℝ) (hdlo : (1/8 : ℝ) < d) (hdhi : d < (Real.sqrt 2-1)/2) (hc : 0 < c)
    (l : Filter ι) (m N r : ι → ℕ) (I : ∀ i, FamilyProblem (N i) (m i) (r i))
    (hm : Tendsto (fun i => (m i : ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i : ℝ)/Real.log (m i : ℝ)) l (𝓝 (1+d)))
    (hδ : ∀ᶠ i in l, (m i : ℝ)^(-c) ≤ (I i).delta) :
    let K := growingFamilyKernelImplementation d hdlo
    (∀ (i : ι) (g : FamilyRandomTape (I i)),
      let program := growingDepthProgram (K.kernels (N i) (m i) (I i).core_positive) (I i) g
      program.admissible ∧ program.eval.width ≤ r i ∧ program.eval.product.rank ≤ r i ∧
        program.eval.product = program.eval.left*program.eval.right) ∧
    (∀ i : ι, (familyRandomLaw (I i)).real {g : FamilyRandomTape (I i) |
      ‖(I i).A*(I i).B-(growingDepthProgram (K.kernels (N i) (m i) (I i).core_positive) (I i) g).eval.product‖ ≤
        (1+(m i/N i : ℝ)^2*Real.sqrt (m i/N i : ℝ))*tailSingularValue ((I i).A*(I i).B) (r i)} ≥
        1-(I i).delta) ∧
    (∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ i in l,
      1 ≤ (I i).prepared.depth ∧
      (I i).prepared.fixed.theta = (m i/N i : ℝ)^2*Real.sqrt (m i/N i : ℝ) ∧
      ((I i).prepared.depth : ℝ) ≤ 1+(Real.log D+Real.log (Real.log (m i : ℝ)))/Real.log 2 ∧
      Real.sqrt (m i/N i : ℝ) ≤ (I i).prepared.fixed.accuracy (I i).prepared.depth ∧
      (I i).prepared.fixed.accuracy (I i).prepared.depth < 1024*Real.sqrt (m i/N i : ℝ) ∧
      r i+1 ≤ 2*⌈Real.sqrt (m i : ℝ)⌉₊) ∧
    (∀ η : ℝ, 0 < η → ∀ᶠ i in l,
      max (K.overhead (m i)) (K.outputOverhead (N i)) ≤ (m i : ℝ)^η) ∧
    (∃ Cdepth γ Ccore : ℝ, 0 ≤ Ccore ∧ ∀ᶠ i in l, ∀ g : FamilyRandomTape (I i),
      (growingDepthExplicitWork (K.kernels (N i) (m i) (I i).core_positive) (I i) g : ℝ) ≤
        (N i : ℝ)^2*max (K.overhead (m i)) (K.outputOverhead (N i))*
          Real.exp (Cdepth*(1+Real.log (Real.log (2*(m i : ℝ))))^2)+
        Ccore*(m i : ℝ)^(9/4+growingFamilySlack d)*(Real.log (m i : ℝ))^γ) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ g : FamilyRandomTape (I i),
      (growingDepthExplicitWork (K.kernels (N i) (m i) (I i).core_positive) (I i) g : ℝ) ≤
        (N i : ℝ)^(2+ε)) := by
  intro K
  have hd : FamilyExponentAdmissible d := ⟨hdlo,hdhi⟩
  have hζ := growingFamilySlack_positive d hdlo
  have hζbudget : growingFamilySlack d < 2+2*d-9/4 := by unfold growingFamilySlack; linarith
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i g
    exact ⟨growingDepthProgram_admissible _ (I i) g,(growingDepthProgram_rank_cap _ (I i) g).1,
      (growingDepthProgram_rank_cap _ (I i) g).2,(growingDepthProgram _ (I i) g).eval.product_eq⟩
  · intro i
    exact growingDepthProgram_error_probability _ (I i)
  · obtain ⟨D,hD,hparams⟩ := familyPreparationProgram_sequence_parameters l m N r I d c hd hc hm hgrowth hδ
    refine ⟨D,hD,?_⟩
    filter_upwards [hparams] with i hi
    rcases hi with ⟨hdepthEq,htheta,hdepthle,hdepth,hlo,hhi,hrReal,hrNat,hconfidence⟩
    exact ⟨(I i).prepared.fixed.depth_positive,htheta,hdepth,hlo,hhi,hrNat⟩
  · exact family_final_kernel_overhead_sequence l m N K.overhead K.outputOverhead d hd.positive hm
      (fun i => (I i).core_le_side) (fun i => (I i).side_positive) hgrowth
      K.overhead_subpolynomial K.output_overhead_subpolynomial
  · exact growingDepthProgram_sequence_log_bound l m N r I (growingFamilySlack d) d c hζ hd hc hm hgrowth hδ
  · exact growingDepthProgram_quadratic_runtime l m N r I (growingFamilySlack d) d c hζ hd hc hζbudget hm hgrowth hδ

end
end HierarchicalAbsoluteSpectral
