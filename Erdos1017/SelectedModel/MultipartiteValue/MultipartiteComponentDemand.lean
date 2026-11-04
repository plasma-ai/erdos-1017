module

public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteComponentRealization
public import Erdos1017.Multipartite.MultipartitePhysicalUpper
public import Erdos1017.Multipartite.MultipartiteCarrierMass

/-!
# Edge demand of a multipartite partition

`partitionEdges` joins distinct independent classes, with the dust label as a
complete region; conditional class sampling transports the whole ordered edge
demand, and the partition has the density moment of its own anchor-normalized
profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.MultipartiteComponentRealization

local instance componentDemandLabelMeasurable : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Distinct independent classes are joined, and the single dust label
represents a complete region rather than an independent class. -/
def partitionEdges (q : Ω → Label) : Set (Ω × Ω) :=
  {p | q p.1 ≠ q p.2 ∨ q p.1 = .inr ()}

omit [IsProbabilityMeasure μ] in
theorem partitionEdges_measurable (q : Ω → Label) (hq : Measurable q) :
    MeasurableSet (partitionEdges q) :=
  (measurableSet_eq_fun (hq.comp measurable_fst) (hq.comp measurable_snd)).compl.union
    ((hq.comp measurable_fst) (measurableSet_singleton (.inr ())))

variable [MeasurableEq Ω] [NullSingletonClass μ]

/-- Actual conditional class sampling transports the entire ordered edge
demand. Atomlessness licenses the removed physical diagonal. -/
theorem map_graphDemand (q : Ω → Label) (hq : Measurable q)
    (h : Label × unitInterval → Ω) (hh : Measurable h)
    (hpush : (MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
      (heads (μ := μ) q) (dust (μ := μ) q)).map h =
        (ENNReal.ofReal (anchor (μ := μ) q))⁻¹ • μ)
    (hlabels : ∀ᵐ z ∂MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
      (heads (μ := μ) q) (dust (μ := μ) q), q (h z) = z.1) :
    (PhysicalPrimal.graphDemand
      (MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
        (heads (μ := μ) q) (dust (μ := μ) q)) MultipartiteCountableMeasure.edgeSet).map
          (Prod.map h h) =
      ((ENNReal.ofReal (anchor (μ := μ) q))⁻¹ *
        (ENNReal.ofReal (anchor (μ := μ) q))⁻¹) •
          PhysicalPrimal.graphDemand μ (partitionEdges q) := by
  let ρ := MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
    (heads (μ := μ) q) (dust (μ := μ) q)
  have : IsFiniteMeasure ρ :=
    MultipartiteCountableMeasure.vertexMeasure_finite _ _ (heads_summable q hq) _
  have hpair : (ρ.prod ρ).map (Prod.map h h) =
      ((ENNReal.ofReal (anchor (μ := μ) q))⁻¹ *
        (ENNReal.ofReal (anchor (μ := μ) q))⁻¹) • μ.prod μ := by
    rw [← Measure.map_prod_map ρ ρ hh hh]
    change ((MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
      (heads (μ := μ) q) (dust (μ := μ) q)).map h).prod
      ((MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
        (heads (μ := μ) q) (dust (μ := μ) q)).map h) = _
    rw [hpush, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hqm : QuasiMeasurePreserving (Prod.map h h) (ρ.prod ρ) (μ.prod μ) := by
    refine ⟨hh.prodMap hh, ?_⟩
    rw [hpair]
    exact Measure.smul_absolutelyContinuous
  have hneq : ∀ᵐ p ∂μ.prod μ, p.1 ≠ p.2 := by
    have hnull := PhysicalCellLift.product_diagonal_null μ
    simpa only [ae_iff, Set.diagonal, not_not] using hnull
  have he : MultipartiteCountableMeasure.edgeSet =ᵐ[ρ.prod ρ]
      (Prod.map h h) ⁻¹' partitionEdges q := by
    filter_upwards [hqm.ae hneq, Measure.quasiMeasurePreserving_fst.ae hlabels,
      Measure.quasiMeasurePreserving_snd.ae hlabels] with p hn hl hr
    have hp : p.1 ≠ p.2 := fun heq => hn (congrArg h heq)
    apply propext
    simp only [MultipartiteCountableMeasure.edgeSet, PhysicalCellLift.edgeSet,
      PhysicalCellLift.Adj, partitionEdges, mem_preimage, mem_ofPred_eq, Finset.mem_singleton]
    change (p.1 ≠ p.2 ∧ (p.1.1 ≠ p.2.1 ∨ p.1.1 = .inr ())) ↔
      (q (h p.1) ≠ q (h p.2) ∨ q (h p.1) = .inr ())
    rw [hl, hr]
    exact and_iff_right hp

  change ((ρ.prod ρ).restrict MultipartiteCountableMeasure.edgeSet).map (Prod.map h h) = _
  rw [Measure.restrict_congr_set he, ← Measure.restrict_map (hh.prodMap hh)
    (partitionEdges_measurable q hq), hpair, Measure.restrict_smul]
  rfl

variable [StandardBorelSpace Ω]

/-- The same actual partition has the density moment of its own raw
anchor-normalized profile; no square-mass compactness condition is assumed. -/
theorem partition_mass_eq_own_profile (q : Ω → Label) (hq : Measurable q)
    (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q) :
    (PhysicalPrimal.graphDemand μ (partitionEdges q)).real univ / 2 =
      (anchor (μ := μ) q) ^ 2 *
        ((dust (μ := μ) q + ∑' i, heads (μ := μ) q i) +
          ((dust (μ := μ) q + ∑' i, heads (μ := μ) q i) ^ 2 -
            ∑' i, (heads (μ := μ) q i) ^ 2) / 2) := by
  obtain ⟨h, hh, hpush, hlabels⟩ := exists_normalized_sampler q hq ha
  have hp := heads_cube q ha hmax
  have hsum := heads_summable (μ := μ) q hq
  have hsquares : Summable (fun i => (heads (μ := μ) q i) ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => by
      nlinarith [mul_nonneg (hp i).1 (sub_nonneg.mpr (hp i).2)]) hsum
  have hmap := map_graphDemand q hq h hh hpush hlabels
  have hmass :
      (PhysicalPrimal.graphDemand
        (MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
          (heads (μ := μ) q) (dust (μ := μ) q))
        MultipartiteCountableMeasure.edgeSet).real univ =
      (1 / (anchor (μ := μ) q) ^ 2) *
        (PhysicalPrimal.graphDemand μ (partitionEdges q)).real univ := by
    calc
      _ = ((PhysicalPrimal.graphDemand
          (MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
            (heads (μ := μ) q) (dust (μ := μ) q))
          MultipartiteCountableMeasure.edgeSet).map (Prod.map h h)).real univ := by
        simp [measureReal_def, Measure.map_apply (hh.prodMap hh)]
      _ = _ := by
        rw [hmap]
        simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
          ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le]
        ring
  calc
    _ = (anchor (μ := μ) q) ^ 2 *
        ((PhysicalPrimal.graphDemand
          (MultipartiteCountableMeasure.vertexMeasure (volume : Measure unitInterval)
            (heads (μ := μ) q) (dust (μ := μ) q))
          MultipartiteCountableMeasure.edgeSet).real univ / 2) := by
      rw [hmass]
      field_simp
    _ = _ := congrArg (fun x : ℝ => (anchor (μ := μ) q) ^ 2 * x)
      (MultipartiteCountableMeasure.graphDemand_mass (volume : Measure unitInterval)
        (heads (μ := μ) q) (fun i => (hp i).1) hsum hsquares
        (dust (μ := μ) q) (dust_nonneg q ha.le))

end Erdos1017.MultipartiteComponentRealization
