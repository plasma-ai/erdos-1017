module

public import Erdos1017.SelectedModel.Recovery.FullReverseFlowClass

/-!
# Restricting a reverse flow to a source set

The slice `sourceSlice` keeps the flow whose source lies in `T`; its endpoint is
a probability law passing the original clique tests, and the full energy
dominates the sum of both source credits because reverse-oriented flows have
nonnegative mutual shifted energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [MeasurableSpace Ω] in
/-- Keep precisely the original flow whose source belongs to `T`. -/
def sourceSlice (T : Set Ω) (q : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  if p.2 ∈ T then q p else 0

omit [IsFiniteMeasure μ] in
/-- Source restriction preserves actual product integrability. -/
theorem integrable_sourceSlice {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ))
    {T : Set Ω} (hT : MeasurableSet T) : Integrable (sourceSlice T q) (μ.prod μ) :=
  hq.indicator (hT.preimage measurable_snd)

omit [MeasurableSpace Ω] in
/-- Nonzero restricted flow retains its original pair and actual source. -/
theorem sourceSlice_ne_zero {q : Ω × Ω → ℝ} {T : Set Ω} {p : Ω × Ω}
    (hp : sourceSlice T q p ≠ 0) : q p ≠ 0 ∧ p.2 ∈ T := by
  by_cases h : p.2 ∈ T
  · exact ⟨by simpa only [sourceSlice, ite_eq_left h] using hp, h⟩
  · simp only [sourceSlice, ite_eq_right h, ne_eq, not_true_eq_false] at hp

omit [IsFiniteMeasure μ] in
/-- Nonnegative flow remains nonnegative under source restriction. -/
theorem nonnegative_sourceSlice {q : Ω × Ω → ℝ} (hq : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (T : Set Ω) : ∀ᵐ p ∂μ.prod μ, 0 ≤ sourceSlice T q p := by
  filter_upwards [hq] with p hp
  by_cases h : p.2 ∈ T
  · simpa only [sourceSlice, ite_eq_left h] using hp
  · simp only [sourceSlice, ite_eq_right h, le_refl]

omit [IsFiniteMeasure μ] in
/-- The source marginal is restricted pointwise, without a section bound. -/
theorem supply_sourceSlice (T : Set Ω) (q : Ω × Ω → ℝ) :
    supply μ (sourceSlice T q) = T.indicator (supply μ q) := by
  funext y
  by_cases h : y ∈ T
  · simp only [supply, sourceSlice, ite_eq_left h, indicator_of_mem h]
  · simp only [supply, sourceSlice, ite_eq_right h, indicator_of_notMem h, integral_zero]

/-- The actual transported mass is the original supply on the chosen sources. -/
theorem integral_sourceSlice {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ))
    {T : Set Ω} (hT : MeasurableSet T) :
    (∫ p, sourceSlice T q p ∂μ.prod μ) = ∫ x in T, supply μ q x ∂μ := by
  rw [← (integral_marginals (integrable_sourceSlice hq hT)).2,
    supply_sourceSlice, integral_indicator hT]

omit [MeasurableSpace Ω] in
/-- Source and complementary-source densities sum to the original flow. -/
theorem sourceSlice_add_compl (T : Set Ω) (q : Ω × Ω → ℝ) :
    sourceSlice T q + sourceSlice Tᶜ q = q := by
  funext p
  by_cases h : p.2 ∈ T <;> simp [sourceSlice, h]

/-- The actual receipts split by Fubini on one common event. -/
theorem receipt_sourceSlice_add_compl {q : Ω × Ω → ℝ}
    (hq : Integrable q (μ.prod μ)) {T : Set Ω} (hT : MeasurableSet T) :
    receipt μ q =ᵐ[μ] receipt μ (sourceSlice T q) + receipt μ (sourceSlice Tᶜ q) := by
  filter_upwards [(integrable_sourceSlice hq hT).prod_right_ae,
    (integrable_sourceSlice hq hT.compl).prod_right_ae] with x hx hy
  conv_lhs => rw [← sourceSlice_add_compl T q]
  exact integral_add hx hy

/-- The actual integrable directions split into both retained credits. -/
theorem direction_sourceSlice_add_compl {q : Ω × Ω → ℝ}
    (hq : Integrable q (μ.prod μ)) {T : Set Ω} (hT : MeasurableSet T) :
    direction μ q =ᵐ[μ] direction μ (sourceSlice T q) + direction μ (sourceSlice Tᶜ q) := by
  have h := direction_add (integrable_sourceSlice hq hT) (integrable_sourceSlice hq hT.compl)
  rwa [sourceSlice_add_compl] at h

/-- A zero product density has zero actual direction almost everywhere. -/
theorem direction_eq_zero_of_ae_zero {q : Ω × Ω → ℝ} (hq : q =ᵐ[μ.prod μ] 0) :
    direction μ q =ᵐ[μ] 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod hq,
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hq)]
    with x hx hy
  change ∀ᵐ y ∂μ, q (y, x) = 0 at hy
  change (∫ y, q (x, y) ∂μ) - (∫ y, q (y, x) ∂μ) = 0
  rw [integral_eq_zero_of_ae hx, integral_eq_zero_of_ae hy, sub_self]

end Erdos1017.MissingFlow

namespace Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- An actual source slice supplies exactly its chosen measurable HIGH set. -/
theorem sourceSlice_supply (hq : S.IsFullReverseFlow q) {T : Set Ω}
    (hTH : T ⊆ S.H) :
    MissingFlow.supply μ (MissingFlow.sourceSlice T q) =ᵐ[μ] T.indicator (fun _ => 1) := by
  rw [MissingFlow.supply_sourceSlice]
  filter_upwards [hq.supply] with x hx
  by_cases h : x ∈ T
  · rw [indicator_of_mem h, hx, indicator_of_mem (hTH h), indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h]

/-- Partial supply is genuinely dominated by the original law. -/
theorem sourceSlice_supply_le_one (hq : S.IsFullReverseFlow q) {T : Set Ω}
    (hTH : T ⊆ S.H) :
    ∀ᵐ x ∂μ, MissingFlow.supply μ (MissingFlow.sourceSlice T q) x ≤ 1 := by
  filter_upwards [hq.sourceSlice_supply hTH] with x hx
  rw [hx]
  by_cases h : x ∈ T
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]; exact zero_le_one

/-- Partial transported mass is exactly the original source-set mass. -/
theorem sourceSlice_integral (hq : S.IsFullReverseFlow q) {T : Set Ω}
    (hT : MeasurableSet T) (hTH : T ⊆ S.H) :
    (∫ p, MissingFlow.sourceSlice T q p ∂μ.prod μ) = μ.real T := by
  rw [← (MissingFlow.integral_marginals (MissingFlow.integrable_sourceSlice hq.integrable hT)).2,
    integral_congr_ae (hq.sourceSlice_supply hTH), integral_indicator hT,
    setIntegral_const, smul_eq_mul, mul_one]

/-- The complementary source marginal is exactly the remaining original HIGH set. -/
theorem sourceSlice_compl_supply (hq : S.IsFullReverseFlow q) (T : Set Ω) :
    MissingFlow.supply μ (MissingFlow.sourceSlice Tᶜ q) =ᵐ[μ]
      (S.H \ T).indicator (fun _ => 1) := by
  rw [MissingFlow.supply_sourceSlice]
  filter_upwards [hq.supply] with x hx
  by_cases hT : x ∈ T <;> by_cases hH : x ∈ S.H <;> simp [hx, hT, hH]

/-- Complementary transported mass is the original HIGH mass outside the slice. -/
theorem sourceSlice_compl_integral (hq : S.IsFullReverseFlow q) {T : Set Ω}
    (hT : MeasurableSet T) :
    (∫ p, MissingFlow.sourceSlice Tᶜ q p ∂μ.prod μ) = μ.real (S.H \ T) := by
  rw [← (MissingFlow.integral_marginals
    (MissingFlow.integrable_sourceSlice hq.integrable hT.compl)).2,
    integral_congr_ae (hq.sourceSlice_compl_supply T),
    integral_indicator (S.hpartition.1.diff hT), setIntegral_const, smul_eq_mul, mul_one]

/-- The original selected relation, LOW recipients and chosen sources persist. -/
theorem sourceSlice_support (hq : S.IsFullReverseFlow q) (T : Set Ω) :
    ∀ᵐ p ∂μ.prod μ, MissingFlow.sourceSlice T q p ≠ 0 →
      p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.L ∧ p.2 ∈ S.H ∩ T := by
  filter_upwards [hq.support] with p hp hne
  obtain ⟨hne, hT⟩ := MissingFlow.sourceSlice_ne_zero hne
  obtain ⟨hZ, hL, hH⟩ := hp hne
  exact ⟨hZ, hL, hH, hT⟩

/-- Every source slice retains the actual reverse original-degree orientation. -/
theorem sourceSlice_oriented_support (hq : S.IsFullReverseFlow q) (T : Set Ω) :
    ∀ᵐ p ∂μ.prod μ, MissingFlow.sourceSlice T q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
  filter_upwards [hq.oriented_support] with p hp hne
  exact hp (MissingFlow.sourceSlice_ne_zero hne).1

/-- Partial receipts still vanish off the original LOW set. -/
theorem sourceSlice_receipt_zero_off_low (hq : S.IsFullReverseFlow q) (T : Set Ω) :
    ∀ᵐ x ∂μ, x ∉ S.L → MissingFlow.receipt μ (MissingFlow.sourceSlice T q) x = 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod (hq.sourceSlice_support T)] with x hx hnot
  apply integral_eq_zero_of_ae
  filter_upwards [hx] with y hy
  by_contra hne
  exact hnot (hy hne).2.1

/-- Every chosen HIGH source has zero weight in the actual partial endpoint. -/
theorem sourceSlice_endpoint_removes_source (hq : S.IsFullReverseFlow q) {T : Set Ω}
    (hTH : T ⊆ S.H) :
    ∀ᵐ x ∂μ, x ∈ T → 1 + MissingFlow.direction μ (MissingFlow.sourceSlice T q) x = 0 := by
  filter_upwards [hq.sourceSlice_supply hTH, hq.sourceSlice_receipt_zero_off_low T]
    with x hs hr hx
  have hxL : x ∉ S.L := fun h => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hTH hx) h
  change 1 + (MissingFlow.receipt μ (MissingFlow.sourceSlice T q) x -
    MissingFlow.supply μ (MissingFlow.sourceSlice T q) x) = 0
  rw [hr hxL, hs, indicator_of_mem hx]
  ring

/-- The unchanged decorated kernel under the partial endpoint's actual law. -/
def sourceSliceEndpoint (hq : S.IsFullReverseFlow q) {T : Set Ω}
    (hT : MeasurableSet T) (hTH : T ⊆ S.H) :
    Model Ω (missingFlowEndpointLaw μ (MissingFlow.sourceSlice T q)) :=
  missingFlowEndpoint W _ (MissingFlow.integrable_sourceSlice hq.integrable hT)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative T) (hq.sourceSlice_supply_le_one hTH)

/-- The partial endpoint is an actual probability law, including null sources. -/
theorem sourceSliceEndpoint_probability (hq : S.IsFullReverseFlow q) {T : Set Ω}
    (hT : MeasurableSet T) (hTH : T ⊆ S.H) :
    IsProbabilityMeasure (missingFlowEndpointLaw μ (MissingFlow.sourceSlice T q)) :=
  missingFlowEndpoint_probability _ (MissingFlow.integrable_sourceSlice hq.integrable hT)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative T) (hq.sourceSlice_supply_le_one hTH)

/-- All old clique tests survive the actual partial endpoint. -/
theorem sourceSliceEndpoint_fullFeasible (hq : S.IsFullReverseFlow q) {T : Set Ω}
    (hT : MeasurableSet T) (hTH : T ⊆ S.H) (hW : FullFeasible W) :
    FullFeasible (hq.sourceSliceEndpoint hT hTH) :=
  fullFeasible_missingFlowEndpoint W hW _ (MissingFlow.integrable_sourceSlice hq.integrable hT)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative T) (hq.sourceSlice_supply_le_one hTH)

end Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Two actual reverse-oriented flows have nonnegative mutual original
shifted energy. Both are reversed before using the forward cone theorem. -/
theorem FullStationaryClass.reverse_missing_flow_pairing_nonnegative
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q r : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ)) (hr : Integrable r (μ.prod μ))
    (hq0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) (hr0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ r p)
    (hqs : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2)
    (hrs : ∀ᵐ p ∂μ.prod μ, r p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
    0 ≤ KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ q) (MissingFlow.direction μ r) := by
  have reverse (f : Ω × Ω → ℝ)
      (hf : ∀ᵐ p ∂μ.prod μ, f p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
          adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2) :
      ∀ᵐ p ∂μ.prod μ, MissingFlow.swapDensity f p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
        0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
          adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae hf,
      shiftedMoment_symm W m] with p hp hs hne
    have h := hp hne
    exact ⟨hs.symm.trans h.1, sub_pos.mpr h.2⟩
  have h := hW.missing_flow_pairing_nonnegative hd hgap
    (MissingFlow.swapDensity q) (MissingFlow.swapDensity r)
    (MissingFlow.integrable_swapDensity hq) (MissingFlow.integrable_swapDensity hr)
    (MissingFlow.nonnegative_swapDensity hq0) (MissingFlow.nonnegative_swapDensity hr0)
    (reverse q hqs) (reverse r hrs)
  have heq : KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ (MissingFlow.swapDensity q))
      (MissingFlow.direction μ (MissingFlow.swapDensity r)) =
      KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ q) (MissingFlow.direction μ r) := by
    rw [MissingFlow.direction_swapDensity, MissingFlow.direction_swapDensity]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => by dsimp only; ring)
  rwa [heq] at h

namespace SelectedHighLowStructure.IsFullReverseFlow

variable {d c m : ℝ} {W : Model Ω μ} {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- A partial reverse endpoint has density at most the original one, also
when its chosen HIGH source set is null and its flow vanishes. -/
theorem sourceSliceEndpoint_density_le (hq : S.IsFullReverseFlow q)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) {T : Set Ω} (hT : MeasurableSet T) (hTH : T ⊆ S.H) :
    density (hq.sourceSliceEndpoint hT hTH) ≤ d := by
  have hi := MissingFlow.integrable_sourceSlice hq.integrable hT
  have hn := MissingFlow.nonnegative_sourceSlice hq.nonnegative T
  by_cases hpos : 0 < ∫ p, MissingFlow.sourceSlice T q p ∂μ.prod μ
  · exact hW.reverse_missing_flow_endpoint_density_le hd hgap _ hi hn hpos
      (hq.sourceSlice_supply_le_one hTH) (hq.sourceSlice_oriented_support T)
  · have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
      (le_antisymm (le_of_not_gt hpos) (integral_nonneg_of_ae hn))
    have hv := MissingFlow.direction_eq_zero_of_ae_zero hz
    have hlin : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x *
        MissingFlow.direction μ (MissingFlow.sourceSlice T q) x ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hv] with x hx
      rw [hx, Pi.zero_apply, mul_zero]
    have henergy : KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W)
        (MissingFlow.direction μ (MissingFlow.sourceSlice T q)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hv] with p hp
      change adjacencyKernel W p.1 p.2 * MissingFlow.direction μ (MissingFlow.sourceSlice T q) p.2 *
        MissingFlow.direction μ (MissingFlow.sourceSlice T q) p.1 = 0
      rw [hp, Pi.zero_apply, mul_zero]
    change density (integrableTilt W _ (MissingFlow.integrable_direction hi)
      (MissingFlow.integral_direction hi) (MissingFlow.direction_ge_neg_one hn
        (hq.sourceSlice_supply_le_one hTH)) 1 ⟨by norm_num, le_rfl⟩) ≤ d
    have heq := density_integrableTilt W (MissingFlow.direction μ (MissingFlow.sourceSlice T q))
      (MissingFlow.integrable_direction hi) (MissingFlow.integral_direction hi)
      (MissingFlow.direction_ge_neg_one hn (hq.sourceSlice_supply_le_one hTH)) 1 ⟨by norm_num, le_rfl⟩
    rw [heq, hW.density_eq, hlin, henergy]
    simp only [mul_zero, add_zero, zero_div, le_refl]

/-- Every slice has nonnegative original shifted energy, even at zero mass. -/
theorem sourceSlice_energy_nonnegative (hq : S.IsFullReverseFlow q)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) {T : Set Ω} (hT : MeasurableSet T) :
    0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ (MissingFlow.sourceSlice T q)) :=
  hW.reverse_missing_flow_energy_nonnegative hd hgap _
    (MissingFlow.integrable_sourceSlice hq.integrable hT)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative T) (hq.sourceSlice_oriented_support T)

/-- The two source pieces have nonnegative mutual original shifted energy. -/
theorem sourceSlice_pairing_nonnegative (hq : S.IsFullReverseFlow q)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) {T : Set Ω} (hT : MeasurableSet T) :
    0 ≤ KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ (MissingFlow.sourceSlice T q))
      (MissingFlow.direction μ (MissingFlow.sourceSlice Tᶜ q)) :=
  hW.reverse_missing_flow_pairing_nonnegative hd hgap _ _
    (MissingFlow.integrable_sourceSlice hq.integrable hT)
    (MissingFlow.integrable_sourceSlice hq.integrable hT.compl)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative T)
    (MissingFlow.nonnegative_sourceSlice hq.nonnegative Tᶜ)
    (hq.sourceSlice_oriented_support T) (hq.sourceSlice_oriented_support Tᶜ)

/-- Both source credits are retained: the full energy dominates their sum,
using the nonnegative reverse cross pairing rather than mere monotonicity. -/
theorem sourceSlice_energy_add_le (hq : S.IsFullReverseFlow q)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) {T : Set Ω} (hT : MeasurableSet T) :
    KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice T q)) +
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (MissingFlow.direction μ (MissingFlow.sourceSlice Tᶜ q)) ≤
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) := by
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hexpand := KernelOperator.kernelEnergy_sub_mul (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
    (MissingFlow.direction μ (MissingFlow.sourceSlice T q))
    (MissingFlow.direction μ (MissingFlow.sourceSlice Tᶜ q))
    (MissingFlow.integrable_direction (MissingFlow.integrable_sourceSlice hq.integrable hT))
    (MissingFlow.integrable_direction (MissingFlow.integrable_sourceSlice hq.integrable hT.compl)) (-1)
  have heq : KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) (MissingFlow.direction μ q) =
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
        (fun x => MissingFlow.direction μ (MissingFlow.sourceSlice T q) x -
          -1 * MissingFlow.direction μ (MissingFlow.sourceSlice Tᶜ q) x) := by
    apply integral_congr_ae
    have ha := MissingFlow.direction_sourceSlice_add_compl hq.integrable hT
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ha,
      Measure.quasiMeasurePreserving_snd.ae ha] with p hp hr
    dsimp only [Pi.add_apply] at hp hr
    rw [hp, hr]
    ring
  rw [heq, hexpand]
  have hcross := hq.sourceSlice_pairing_nonnegative hW hd hgap hT
  nlinarith

end SelectedHighLowStructure.IsFullReverseFlow

end Erdos1017.CappedModel
