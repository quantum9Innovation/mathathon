import HierarchicalAbsoluteSpectral.RuntimeFamilyOneLevel
import HierarchicalAbsoluteSpectral.RuntimeFamilyRecurrence

namespace HierarchicalAbsoluteSpectral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators
variable {k b : ℕ}

def FactorActions.maxCost {R : Core k} (P : FactorActions R b) : ℕ :=
  max P.forward.cost P.transpose.cost

/-- The actual recursive forward and transpose compilers satisfy the
weighted unfolded recurrence, including scalar table preparation at each
invocation. Fine actions remain actual programme witnesses in this local
composition theorem. -/
theorem compiled_family_action_cost_unfold
    (R0 : Core k) (Kfine : ℕ → Core k)
    {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024))
    (hsym : ∀ j < out.depth, (Kfine j)ᵀ = Kfine j)
    (base : FactorActions R0 b) (fine : ∀ j, MatrixAction (Kfine j) b)
    (hD : 1 ≤ D) (hm : 1 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m) :
    let H := fun j => familyScheduleValue (1/1024) (s/1024) j
    let hpos : ∀ j ≤ out.depth, 0 < H j :=
      fun j _ => familyScheduleValue_pos _ _ (by norm_num) (by positivity) j
    let P := hierarchicalFactorActions R0 Kfine H out.depth hpos hsym base fine
    H out.depth*(P out.depth le_rfl).maxCost ≤
      (2*familyActionCostConstant D*(Real.log m)^2)^out.depth*
        (H 0*base.maxCost+∑ j ∈ Finset.range out.depth,
          H j*((fine j).cost+k*b+1)) := by
  intro H hpos P
  let a := 2*familyActionCostConstant D*(Real.log m)^2
  let c := fun j : ℕ => if hj : j ≤ out.depth then ((P j hj).maxCost:ℝ) else 0
  let leaf := fun j => ((fine j).cost:ℝ)+(k:ℝ)*b+1
  have hConst := familyActionCostConstant_ge_one D hD
  have ha : 1 ≤ a := by dsimp [a]; nlinarith [sq_nonneg (Real.log m-1)]
  have hleaf : ∀ j < out.depth, 0 ≤ leaf j := by intro j _; dsimp [leaf]; positivity
  have hstep : ∀ j < out.depth, c (j+1) ≤ a*(H j/H (j+1))*(c j+leaf j) := by
    intro j hj
    have hjle : j ≤ out.depth := by omega
    have hjnext : j+1 ≤ out.depth := by omega
    let prev := P j hjle
    obtain ⟨hε,hh,hB,hbound⟩ := family_refinement_envelope_bound hs out (by omega)
      hD hm hscale j hj prev.forward.cost prev.transpose.cost (fine j).cost k b
    have hNat : (P (j+1) hjnext).maxCost ≤
        refinementActionEnvelope prev.forward.cost prev.transpose.cost (fine j).cost
          (H (j+1)/H j) (H (j+1)) (hierarchyUpper j) hε hh hB k b := by
      change max (hierarchicalFactorActions R0 Kfine H out.depth hpos hsym base fine (j+1) hjnext).forward.cost
        (hierarchicalFactorActions R0 Kfine H out.depth hpos hsym base fine (j+1) hjnext).transpose.cost ≤ _
      rw [hierarchicalFactorActions]
      exact FactorActions.refine_cost _ _ _ _ _ _ _ _ _
    have hNatR : ((P (j+1) hjnext).maxCost:ℝ) ≤
        (refinementActionEnvelope prev.forward.cost prev.transpose.cost (fine j).cost
          (H (j+1)/H j) (H (j+1)) (hierarchyUpper j) hε hh hB k b:ℝ) := by exact_mod_cast hNat
    have hNext : ((P (j+1) hjnext).maxCost:ℝ) ≤
        familyActionCostConstant D*(H j/H (j+1))*(Real.log m)^2*
          ((prev.forward.cost:ℝ)+(prev.transpose.cost:ℝ)+(fine j).cost+(k:ℝ)*b+1) :=
      hNatR.trans hbound
    have hsumNat : prev.forward.cost+prev.transpose.cost+(fine j).cost+k*b+1 ≤
        2*(prev.maxCost+((fine j).cost+k*b+1)) := by
      have hp := le_max_left prev.forward.cost prev.transpose.cost
      have ht := le_max_right prev.forward.cost prev.transpose.cost
      dsimp [FactorActions.maxCost]
      omega
    have hsum : (prev.forward.cost:ℝ)+(prev.transpose.cost:ℝ)+(fine j).cost+(k:ℝ)*b+1 ≤
        2*((prev.maxCost:ℝ)+leaf j) := by dsimp [leaf]; exact_mod_cast hsumNat
    have hprod := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ familyActionCostConstant D*(H j/H (j+1))*(Real.log m)^2 by
        have hH := hpos j hjle
        have hh' := hpos (j+1) hjnext
        positivity)
    simp only [c,dif_pos hjle,dif_pos hjnext]
    exact hNext.trans (by convert hprod using 1 <;> dsimp [a,prev] <;> ring)
  have hu := family_cost_recurrence_unfold a H c leaf out.depth ha hpos hleaf hstep
  convert hu using 1 <;> simp only [c,dif_pos le_rfl,dif_pos (Nat.zero_le out.depth),P,
    hierarchicalFactorActions,leaf,a,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  congr 2

theorem compiled_family_action_cost_shared
    (R0 : Core k) (Kfine : ℕ → Core k)
    {s m D : ℝ} (hs : 0 < s)
    (out : FamilyScheduleOutput (1/1024) (s/1024))
    (hsym : ∀ j < out.depth, (Kfine j)ᵀ = Kfine j)
    (base : FactorActions R0 b) (fine : ∀ j, MatrixAction (Kfine j) b)
    (hD : 1 ≤ D) (hm : 1 ≤ Real.log m) (hscale : Real.log (1/s) ≤ D*Real.log m)
    (χ : ℝ)
    (hbase : familyScheduleValue (1/1024) (s/1024) 0*base.maxCost ≤ χ)
    (hleaf : ∀ j < out.depth, familyScheduleValue (1/1024) (s/1024) j*
      ((fine j).cost+k*b+1) ≤ χ) :
    let H := fun j => familyScheduleValue (1/1024) (s/1024) j
    let hpos : ∀ j ≤ out.depth, 0 < H j :=
      fun j _ => familyScheduleValue_pos _ _ (by norm_num) (by positivity) j
    let P := hierarchicalFactorActions R0 Kfine H out.depth hpos hsym base fine
    H out.depth*(P out.depth le_rfl).maxCost ≤
      (2*familyActionCostConstant D*(Real.log m)^2)^out.depth*(out.depth+1:ℕ)*χ := by
  intro H hpos P
  have hu := compiled_family_action_cost_unfold R0 Kfine hs out hsym base fine hD hm hscale
  have hsum : (∑ j ∈ Finset.range out.depth, H j*((fine j).cost+k*b+1)) ≤ (out.depth:ℝ)*χ := by
    calc
      _ ≤ ∑ _j ∈ Finset.range out.depth, χ :=
        Finset.sum_le_sum (fun j hj => hleaf j (Finset.mem_range.mp hj))
      _ = _ := by simp
  have ha : 0 ≤ 2*familyActionCostConstant D*(Real.log m)^2 := by
    have hh := familyActionCostConstant_ge_one D hD
    positivity
  calc
    _ ≤ (2*familyActionCostConstant D*(Real.log m)^2)^out.depth*
        (H 0*base.maxCost+∑ j ∈ Finset.range out.depth, H j*((fine j).cost+k*b+1)) := hu
    _ ≤ (2*familyActionCostConstant D*(Real.log m)^2)^out.depth*(χ+(out.depth:ℝ)*χ) :=
      mul_le_mul_of_nonneg_left (add_le_add hbase hsum) (pow_nonneg ha _)
    _ = _ := by push_cast; ring

end
end HierarchicalAbsoluteSpectral
