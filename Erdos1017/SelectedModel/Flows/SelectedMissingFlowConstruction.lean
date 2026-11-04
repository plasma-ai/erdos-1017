module

public import Erdos1017.SelectedModel.Structure.SelectedHighLowClassification
public import Erdos1017.SelectedModel.Flows.ClassifiedRelationFlow
public import Erdos1017.SelectedModel.Flows.FullMissingFlowEndpoints

/-!
# The full forward and reverse flows of the selected model

`forwardFlow` and `reverseFlow` use the original degree and row relation on
outside zero pairs between the high and low classes; they transport the low and
high masses, have integrable mean-zero directions bounded below by minus one,
remove their source classes, and have nonnegative shifted energy. They define
the full forward and reverse flow classes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

namespace SelectedHighLowStructure

variable {W : Model Ω μ} {m : ℝ}

/-- The actual full forward flow uses the same original degree and row relation. -/
def forwardFlow (S : SelectedHighLowStructure W m) : Ω × Ω → ℝ :=
  MissingFlow.normalizedDensity μ (MissingFlow.forwardRelation
    (actualZeroRelation W m S.ρ) (adjacencyOperator W (Lp.const 2 μ (1 : ℝ))))

/-- The actual full reverse flow uses the same original degree and row relation. -/
def reverseFlow (S : SelectedHighLowStructure W m) : Ω × Ω → ℝ :=
  MissingFlow.normalizedDensity μ (MissingFlow.reverseRelation
    (actualZeroRelation W m S.ρ) (adjacencyOperator W (Lp.const 2 μ (1 : ℝ))))

/-- Both oriented relations in the selected model are genuinely measurable. -/
theorem measurable_oriented_relations (S : SelectedHighLowStructure W m) :
    MeasurableSet (MissingFlow.forwardRelation (actualZeroRelation W m S.ρ)
      (adjacencyOperator W (Lp.const 2 μ (1 : ℝ)))) ∧
    MeasurableSet (MissingFlow.reverseRelation (actualZeroRelation W m S.ρ)
      (adjacencyOperator W (Lp.const 2 μ (1 : ℝ)))) :=
  MissingFlow.measurableSet_oriented_relations _
    (measurableSet_actualZeroRelation W m S.ρ S.hρ) _ (Lp.stronglyMeasurable _).measurable

/-- Full forward and reverse product densities are L¹ on the original law. -/
theorem integrable_flows (S : SelectedHighLowStructure W m) :
    Integrable S.forwardFlow (μ.prod μ) ∧ Integrable S.reverseFlow (μ.prod μ) :=
  ⟨MissingFlow.integrable_normalizedDensity _ S.measurable_oriented_relations.1,
    MissingFlow.integrable_normalizedDensity _ S.measurable_oriented_relations.2⟩

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Both constructed product densities are nonnegative everywhere. -/
theorem flows_nonnegative (S : SelectedHighLowStructure W m) (p : Ω × Ω) :
    0 ≤ S.forwardFlow p ∧ 0 ≤ S.reverseFlow p :=
  ⟨MissingFlow.normalizedDensity_nonneg _ p, MissingFlow.normalizedDensity_nonneg _ p⟩

/-- Actual forward supply equals the original LOW indicator almost everywhere. -/
theorem forward_supply (S : SelectedHighLowStructure W m) :
    MissingFlow.supply μ S.forwardFlow =ᵐ[μ] S.L.indicator (fun _ => 1) := by
  classical
  rw [forwardFlow, MissingFlow.supply_normalizedDensity _ S.measurable_oriented_relations.1,
    S.hL]
  filter_upwards [MissingFlow.ae_positiveSources_forward_eq_low
    (actualZeroRelation W m S.ρ) (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x)
    S.hnoBoth] with x hx
  change (if x ∈ MissingFlow.positiveSources μ _ then (1 : ℝ) else 0) =
    (if x ∈ OrderedZeroRelation.lowClass μ _ _ then 1 else 0)
  rw [hx]

/-- Actual reverse supply equals the original HIGH indicator pointwise. -/
theorem reverse_supply (S : SelectedHighLowStructure W m) :
    MissingFlow.supply μ S.reverseFlow = S.H.indicator (fun _ => 1) := by
  rw [reverseFlow, MissingFlow.supply_normalizedDensity _ S.measurable_oriented_relations.2,
    MissingFlow.positiveSources_reverseRelation, ← S.hH]

/-- Each actual flow supplies at most the original measure. -/
theorem supply_le_one (S : SelectedHighLowStructure W m) (x : Ω) :
    MissingFlow.supply μ S.forwardFlow x ≤ 1 ∧ MissingFlow.supply μ S.reverseFlow x ≤ 1 :=
  ⟨MissingFlow.supply_normalizedDensity_le_one _ S.measurable_oriented_relations.1 x,
    MissingFlow.supply_normalizedDensity_le_one _ S.measurable_oriented_relations.2 x⟩

/-- Total transported masses are exactly the original LOW and HIGH masses. -/
theorem integral_flows (S : SelectedHighLowStructure W m) :
    (∫ p, S.forwardFlow p ∂μ.prod μ) = μ.real S.L ∧
      (∫ p, S.reverseFlow p ∂μ.prod μ) = μ.real S.H := by
  constructor
  · rw [← (MissingFlow.integral_marginals S.integrable_flows.1).2,
      integral_congr_ae S.forward_supply,
      integral_indicator S.hpartition.2.1, setIntegral_const]
    simp
  · rw [← (MissingFlow.integral_marginals S.integrable_flows.2).2,
      S.reverse_supply, integral_indicator S.hpartition.1, setIntegral_const]
    simp

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The original shifted kernel is zero on forward flow, with strictly
larger original degree at the receipt endpoint. Symmetry is used only AE. -/
theorem forward_support (S : SelectedHighLowStructure W m) :
    ∀ᵐ p ∂μ.prod μ, S.forwardFlow p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      0 < adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 -
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
  filter_upwards [shiftedMoment_symm W m] with p hp hne
  have hmem : p ∈ MissingFlow.forwardRelation (actualZeroRelation W m S.ρ)
      (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) := by
    by_contra hn
    exact hne (MissingFlow.normalizedDensity_eq_zero_of_notMem _ _ hn)
  have hzero : shiftedMoment W m p.swap = 0 := hmem.1.1
  exact ⟨hp.symm.trans hzero, sub_pos.mpr hmem.2⟩

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Reverse flow uses original zero pairs, with strictly larger original
degree at the supplying endpoint. -/
theorem reverse_support (S : SelectedHighLowStructure W m) :
    ∀ᵐ p ∂μ.prod μ, S.reverseFlow p ≠ 0 → shiftedKernel W m p.1 p.2 = 0 ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.1 <
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) p.2 := by
  apply Eventually.of_forall
  intro p hne
  have hmem : p ∈ MissingFlow.reverseRelation (actualZeroRelation W m S.ρ)
      (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) := by
    by_contra hn
    exact hne (MissingFlow.normalizedDensity_eq_zero_of_notMem _ _ hn)
  exact ⟨hmem.1.1, hmem.2⟩

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Forward flow uses actual outside zero pairs from HIGH to LOW. -/
theorem forward_class_support (S : SelectedHighLowStructure W m) :
    ∀ᵐ p ∂μ.prod μ, S.forwardFlow p ≠ 0 →
      p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.H ∧ p.2 ∈ S.L := by
  filter_upwards [S.forward_support, S.hrelation] with p hs hr hne
  have hmem : p ∈ MissingFlow.forwardRelation (actualZeroRelation W m S.ρ)
      (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) := by
    by_contra hn
    exact hne (MissingFlow.normalizedDensity_eq_zero_of_notMem _ _ hn)
  have hZ : p ∈ actualZeroRelation W m S.ρ := ⟨(hs hne).1, hmem.1.2.symm⟩
  refine ⟨hZ, ?_⟩
  rcases hr hZ with h | h
  · exact ⟨h.1, h.2.1⟩
  · exact False.elim ((not_lt_of_ge hmem.2.le) h.2.2)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Reverse flow uses actual outside zero pairs from LOW to HIGH. -/
theorem reverse_class_support (S : SelectedHighLowStructure W m) :
    ∀ᵐ p ∂μ.prod μ, S.reverseFlow p ≠ 0 →
      p ∈ actualZeroRelation W m S.ρ ∧ p.1 ∈ S.L ∧ p.2 ∈ S.H := by
  filter_upwards [S.hrelation] with p hr hne
  have hmem : p ∈ MissingFlow.reverseRelation (actualZeroRelation W m S.ρ)
      (fun x => adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x) := by
    by_contra hn
    exact hne (MissingFlow.normalizedDensity_eq_zero_of_notMem _ _ hn)
  refine ⟨hmem.1, ?_⟩
  rcases hr hmem.1 with h | h
  · exact False.elim ((not_lt_of_ge hmem.2.le) h.2.2)
  · exact ⟨h.2.1, h.1⟩

/-- The two actual directions are integrable, mean zero and bounded below
by minus one. Receipt need not be bounded above. -/
theorem direction_properties (S : SelectedHighLowStructure W m) :
    (Integrable (MissingFlow.direction μ S.forwardFlow) μ ∧
      (∫ x, MissingFlow.direction μ S.forwardFlow x ∂μ) = 0 ∧
      ∀ᵐ x ∂μ, -1 ≤ MissingFlow.direction μ S.forwardFlow x) ∧
    (Integrable (MissingFlow.direction μ S.reverseFlow) μ ∧
      (∫ x, MissingFlow.direction μ S.reverseFlow x ∂μ) = 0 ∧
      ∀ᵐ x ∂μ, -1 ≤ MissingFlow.direction μ S.reverseFlow x) :=
  ⟨MissingFlow.normalized_direction_properties _ S.measurable_oriented_relations.1,
    MissingFlow.normalized_direction_properties _ S.measurable_oriented_relations.2⟩

/-- These actual full-flow endpoint weights remove LOW and HIGH respectively. -/
theorem endpoints_remove_sources (S : SelectedHighLowStructure W m) :
    (∀ᵐ x ∂μ, x ∈ S.L → 1 + MissingFlow.direction μ S.forwardFlow x = 0) ∧
    (∀ᵐ x ∂μ, x ∈ S.H → 1 + MissingFlow.direction μ S.reverseFlow x = 0) := by
  rw [S.hL, S.hH]
  exact MissingFlow.ae_oriented_endpoints_remove_sources _
    (measurableSet_actualZeroRelation W m S.ρ S.hρ) _ (Lp.stronglyMeasurable _).measurable
    (actualZeroRelation_symm W m S.ρ) S.hdegreeNe S.hnoBoth

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Both actual full flows have nonnegative shifted energy in the same
original strict-gap model. No flow-energy premise is supplied. -/
theorem energies_nonnegative (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ S.forwardFlow) ∧
    0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m)
      (MissingFlow.direction μ S.reverseFlow) :=
  ⟨hW.missing_flow_energy_nonnegative hd hgap S.forwardFlow S.integrable_flows.1
      (Eventually.of_forall (fun p => (S.flows_nonnegative p).1)) S.forward_support,
    hW.reverse_missing_flow_energy_nonnegative hd hgap S.reverseFlow S.integrable_flows.2
      (Eventually.of_forall (fun p => (S.flows_nonnegative p).2)) S.reverse_support⟩

end SelectedHighLowStructure

end Erdos1017.CappedModel
