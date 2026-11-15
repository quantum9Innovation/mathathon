import HierarchicalAbsoluteSpectral.CorollaryAbsoluteFamily
import HierarchicalAbsoluteSpectral.MainFamilyRuntimeFinalWidth

/-! The raw Krylov condition holds uniformly up to the largest allowed
attempt, rather than only at the rank-one schedule seed. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

theorem absolute_family_prescribed_width {ι : Type*} (l : Filter ι)
    (m N : ι → ℕ) (I : ∀ i, AbsoluteFamilyProblem (N i) (m i))
    (d : ℝ) (hd : FamilyExponentAdmissible d)
    (hm : Tendsto (fun i => (m i:ℝ)) l atTop)
    (hgrowth : Tendsto (fun i => Real.log (N i:ℝ)/Real.log (m i:ℝ)) l (𝓝 (1+d)))
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) :
    ∀ᶠ i in l, (familyCombinedDegreeCeiling (I i).seed D c+1)*(Nat.sqrt (m i)+1) ≤ m i := by
  have hmLog := (Real.tendsto_log_atTop.comp hm).eventually (eventually_ge_atTop (1:ℝ))
  have hC : 0 ≤ familyCombinedDegreeCoefficient D c := by
    unfold familyCombinedDegreeCoefficient familyQueryDegreeCoefficient familyStrongDegreeCoefficient
    positivity
  have hqpoly : ∀ᶠ i in l, (familyCombinedDegreeCeiling (I i).seed D c:ℝ) ≤
      familyCombinedDegreeCoefficient D c*((N i:ℝ)/m i)*(Real.log (m i:ℝ))^5+1 := by
    filter_upwards [hmLog] with i hi
    exact familyCombinedDegreeCeiling_bound (I i).seed D c hD hc hi
  have hq := family_degree_sequence_subpolynomial_slack l m N
    (fun i => familyCombinedDegreeCeiling (I i).seed D c) d (familyCombinedDegreeCoefficient D c)
    hd.positive hC hm (Eventually.of_forall (fun i => (I i).seed.side_positive)) hgrowth hqpoly
  have hrank : ∀ᶠ i in l, (Nat.sqrt (m i):ℝ) ≤ Real.sqrt (m i:ℝ) :=
    Eventually.of_forall (fun i => by
      rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
      exact Nat.floor_le (Real.sqrt_nonneg _))
  have hraw := family_raw_width_sequence l m (fun i => familyCombinedDegreeCeiling (I i).seed D c)
    (fun i => Nat.sqrt (m i)) d hd hm hq hrank
  filter_upwards [hraw] with i hi
  have hh : (familyCombinedDegreeCeiling (I i).seed D c+1)*(Nat.sqrt (m i)+1) ≤
      (2*familyCombinedDegreeCeiling (I i).seed D c+1)*(Nat.sqrt (m i)+1) :=
    Nat.mul_le_mul_right _ (by omega)
  exact hh.trans hi.le

end
end HierarchicalAbsoluteSpectral
