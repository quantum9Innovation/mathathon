import HierarchicalAbsoluteSpectral.ProbabilityFiniteLaw

/-! The imported SRHT finite law is generated exactly by Gaussian draws,
comparisons for signs, and counted Gaussian-priority sorting for row sets. -/
namespace HierarchicalAbsoluteSpectral
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set SparseFock SRHT

instance srhtRowSet_measurableSpace (k M : ℕ) : MeasurableSpace (RowSet k M) := ⊤

instance srhtRowSet_measurableSingleton (k M : ℕ) : MeasurableSingletonClass (RowSet k M) := by
  constructor
  intro s
  trivial

def gaussianWalshEquiv (k : ℕ) : WalshIndex k ≃ Fin (2^k) :=
  Fintype.equivFinOfCardEq (walshIndex_card k)

def gaussianRowSetEquiv (k M : ℕ) : PriorityRowSet (2^k) M ≃ RowSet k M :=
  Equiv.subtypeEquiv (gaussianWalshEquiv k).symm.finsetCongr
    (fun s => by simp [Equiv.finsetCongr_apply])

def gaussianSRHTSigns (k : ℕ) (g : Fin (2^k) → ℝ) : SignAssignment k :=
  fun i => gaussianSignBit (g (gaussianWalshEquiv k i))

def gaussianSRHTRows (k M : ℕ) (hM : M ≤ 2^k) (g : Fin (2^k) → ℝ) : RowSet k M :=
  gaussianRowSetEquiv k M (priorityRowSet (2^k) M hM g)

theorem gaussianSRHTSigns_measurable (k : ℕ) : Measurable (gaussianSRHTSigns k) := by
  apply measurable_pi_lambda
  intro i
  exact gaussianSignBit_measurable.comp (measurable_pi_apply _)

theorem gaussianSRHTRows_measurable (k M : ℕ) (hM : M ≤ 2^k) : Measurable (gaussianSRHTRows k M hM) :=
  (measurable_of_countable (gaussianRowSetEquiv k M)).comp (priorityRowSet_measurable _ _ hM)

theorem gaussianSRHTSigns_fiber_probability (k : ℕ) (x : SignAssignment k) :
    (gaussianVector (2^k)).real {g | gaussianSRHTSigns k g = x} = (signLaw k).weight x := by
  rw [signLaw_weight]
  exact gaussianSignAssignment_reindex_probability _ (gaussianWalshEquiv k) x

theorem gaussianSRHTRows_fiber_probability (k M : ℕ) (hM : M ≤ 2^k) (T : RowSet k M) :
    (gaussianVector (2^k)).real {g | gaussianSRHTRows k M hM g = T} = (uniformRowLaw hM).weight T := by
  have heq : {g | gaussianSRHTRows k M hM g = T} =
      {g | priorityRowSet (2^k) M hM g = (gaussianRowSetEquiv k M).symm T} := by
    ext g
    exact (gaussianRowSetEquiv k M).apply_eq_iff_eq_symm_apply
  rw [heq, gaussian_priority_singleton_probability, uniformRowLaw_weight,
    ← Fintype.card_congr (gaussianRowSetEquiv k M)]

def gaussianSRHTInputLaw (k : ℕ) :
    Measure ((Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))) :=
  (gaussianVector (2^k)).prod ((gaussianVector (2^k)).prod (gaussianVector (2^k)))

instance gaussianSRHTInputLaw_isProbability (k : ℕ) : IsProbabilityMeasure (gaussianSRHTInputLaw k) := by
  unfold gaussianSRHTInputLaw
  infer_instance

def gaussianSRHTSample (k M : ℕ) (hM : M ≤ 2^k)
    (g : (Fin (2^k) → ℝ) × ((Fin (2^k) → ℝ) × (Fin (2^k) → ℝ))) :
    SignAssignment k × (SignAssignment k × RowSet k M) :=
  (gaussianSRHTSigns k g.1, (gaussianSRHTSigns k g.2.1, gaussianSRHTRows k M hM g.2.2))

theorem gaussianSRHTSample_measurable (k M : ℕ) (hM : M ≤ 2^k) :
    Measurable (gaussianSRHTSample k M hM) :=
  ((gaussianSRHTSigns_measurable k).comp measurable_fst).prodMk
    (((gaussianSRHTSigns_measurable k).comp (measurable_fst.comp measurable_snd)).prodMk
      ((gaussianSRHTRows_measurable k M hM).comp (measurable_snd.comp measurable_snd)))

/-- Exact equality with the imported SRHT sketch law for every event.
All randomness on the left consists of finite independent real Gaussians. -/
theorem gaussian_srht_sampling_probability (k M : ℕ) (hM : M ≤ 2^k)
    (E : Set (SignAssignment k × (SignAssignment k × RowSet k M))) :
    (gaussianSRHTInputLaw k).real (gaussianSRHTSample k M hM ⁻¹' E) = (sketchLaw hM).prob E := by
  apply probability_eq_finiteLaw_of_fibers _ _ _ (gaussianSRHTSample_measurable k M hM) _ E
  rintro ⟨x,y,T⟩
  change (gaussianSRHTInputLaw k).real {g | gaussianSRHTSample k M hM g = (x,(y,T))} =
    (sketchLaw hM).weight (x,(y,T))
  have heq : {g | gaussianSRHTSample k M hM g = (x,(y,T))} =
      {g | gaussianSRHTSigns k g = x} ×ˢ
        ({g | gaussianSRHTSigns k g = y} ×ˢ {g | gaussianSRHTRows k M hM g = T}) := by
    ext g
    simp [gaussianSRHTSample]
  rw [heq, gaussianSRHTInputLaw, measureReal_prod_prod, measureReal_prod_prod,
    gaussianSRHTSigns_fiber_probability, gaussianSRHTSigns_fiber_probability,
    gaussianSRHTRows_fiber_probability, sketchLaw_weight]

end
end HierarchicalAbsoluteSpectral
