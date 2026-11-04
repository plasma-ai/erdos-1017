module

public import Erdos1017.Exclusions.Common.SelectedRootRepricing
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy
public import Erdos1017.SelectedModel.Structure.WholeRowCrossBlocks

/-!
# Star variation at a clique root

The root neighborhood and root charge row are identified on constant blocks
almost everywhere, saturation failure gives strict head-charge slack, and the
signed star variation bounds the root mass by any concrete common-neighbor cover
(`root_mass_le_cover_of_unsaturated_head`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CliqueStarVariation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A concrete cover of the original common neighbors bounds the original
neighborhood integral. The exceptional set is one product-null set. -/
theorem ae_neighborhood_integral_le_cover
    (G : Ω → Ω → ℝ) (hG : Measurable (Function.uncurry G))
    (hbound : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 ∈ Icc (0 : ℝ) 1)
    (P N Z : Set Ω) (hN : MeasurableSet N)
    (hZ : MeasurableSet Z)
    (hcover : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ N → p.2 ∉ Z → G p.1 p.2 = 0) :
    ∀ᵐ x ∂μ, x ∈ P → (∫ z in N, G x z ∂μ) ≤ μ.real Z := by
  filter_upwards [Measure.ae_ae_of_ae_prod hbound,
    Measure.ae_ae_of_ae_prod hcover] with x hb hc hx
  have hg : Integrable (G x) μ := Integrable.of_bound
    (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (hb.mono (fun z hz => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hz.1], hz.2⟩))
  have hi : Integrable (Z.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hZ
  have hle : ∀ᵐ z ∂μ, N.indicator (G x) z ≤ Z.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [hb, hc] with z hb hc
    by_cases hn : z ∈ N
    · by_cases hz : z ∈ Z
      · simpa [hn, hz] using hb.2
      · simp [hn, hz, hc hx hn hz]
    · by_cases hz : z ∈ Z <;> simp [hn, hz]
  have h := integral_mono_ae (hg.indicator hN) hi hle
  simpa only [integral_indicator hN, integral_indicator hZ, setIntegral_const,
    smul_eq_mul, mul_one] using h

/-- The elementary final mass calculation keeps the original outside mass
separate from any changed-law endpoint mass. -/
theorem private_mass_lt_third {A s t a α : ℝ}
    (hcover : A ≤ s - A + (1 - 2 * t))
    (hbalance : a + s + α = t) (ha : 0 < a) (hα : 0 ≤ α)
    (ht : 1 / 3 < t) : A < 1 / 3 := by
  linarith

end Erdos1017.CliqueStarVariation

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original adjacency row and the literal root neighborhood agree on
one common product event, without evaluating any diagonal representative. -/
theorem ae_original_root_adjacency
    (S : SelectedHighLowStructure W m) (k : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → adjacencyKernel W p.1 p.2 =
      if p.2 ∈ S.rootNeighborhood k then 1 else 0 := by
  filter_upwards [S.ae_root_adjacency k hW hd hgap,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with p hr hG hi
  change W.moment CappedColor.adjacency p = _
  rw [hG]
  by_cases hn : p.2 ∈ S.rootNeighborhood k
  · simp only [(hr hi).mpr hn, hn, ite_true]
  · have hne : PhysicalRepresentative.adjacency W m p.1 p.2 ≠ true :=
      fun he => hn ((hr hi).mp he)
    simp [hne, hn]

/-- A constant original block identifies neighborhood membership on the
second fiber. Positivity selects a good first section, not a diagonal. -/
theorem ae_rootNeighborhood_on_constant_block
    (S : SelectedHighLowStructure W m) (k r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (b : Bool)
    (hblock : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = if b = true then 1 else 0) :
    ∀ᵐ x ∂μ, S.ρ x = r.val → (x ∈ S.rootNeighborhood k ↔ b = true) := by
  have hpair : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      (p.2 ∈ S.rootNeighborhood k ↔ b = true) := by
    filter_upwards [S.ae_original_root_adjacency k hW hd hgap, hblock] with p hr hb hk hu
    have he := (hr hk).symm.trans (hb hk hu)
    cases b <;> by_cases hn : p.2 ∈ S.rootNeighborhood k <;> simp_all
  have hrows := ae_restrict_of_ae (s := {x | S.ρ x = k.val})
    (Measure.ae_ae_of_ae_prod hpair)
  obtain ⟨x, _, hx, hm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers k.val k.property).2.1.ne'
    (hrows.and (ae_restrict_mem (S.hfibers k.val k.property).1))
  exact hx.mono (fun y hy => hy hm)

/-- An actual constant original head block gives the same averaged root
charge on the second fiber, on one common original-law event. -/
theorem ae_rootChargeRow_on_constant_block
    (S : SelectedHighLowStructure W m) (k u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (b : ℝ)
    (hblock : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = u.val →
      chargeKernel W p.1 p.2 = b) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, S.rootChargeRow k x = b := by
  have hpair : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = u.val →
      S.rootChargeRow k p.2 = b := by
    filter_upwards [S.ae_root_charge k hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support,
      hblock] with p hr hY hb hk hu
    exact (hr hk).symm.trans (hY.trans (hb hk hu))
  obtain ⟨x, _, hx, hm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers k.val k.property).2.1.ne'
    ((ae_restrict_of_ae (s := {x | S.ρ x = k.val})
      (Measure.ae_ae_of_ae_prod hpair)).and
        (ae_restrict_mem (S.hfibers k.val k.property).1))
  filter_upwards [ae_restrict_of_ae hx,
    ae_restrict_mem (S.hfibers u.val u.property).1] with y hy hu
  exact hy hm hu

/-- On actual positive whole fibers, failure of saturation gives strict
old head-charge slack. The block constant and its bound are derived. -/
theorem ae_rootChargeRow_lt_one_of_not_saturated
    (S : SelectedHighLowStructure W m) (k u : S.I) (hku : k ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hnot : ¬S.IsSaturatedAtomPair k u) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, S.rootChargeRow k x < 1 := by
  obtain ⟨q, _, _, _, hc⟩ := KernelOperator.exists_whole_row_cross_block
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ k.val u.val
    (S.hfibers k.val k.property).2.1 (S.hfibers u.val u.property).2.1
    (S.hfibers k.val k.property).2.2.2 (S.hfibers u.val u.property).2.2.2
    (shiftedKernel_measurable W m)
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).aestronglyMeasurable
    (W.stronglyMeasurable_moment
      CappedColor.continuous_charge.measurable.stronglyMeasurable).aestronglyMeasurable
    ((shiftedMoment_symm W m).mono (fun _ hx => hx.symm)) hW.moment_mem
  let b := q + m * (if 0 < q then 1 else 0)
  have hb : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = u.val →
      chargeKernel W p.1 p.2 = b := by
    rw [Measure.prod_restrict] at hc
    have h := (ae_restrict_iff' ((S.hfibers k.val k.property).1.prod
      (S.hfibers u.val u.property).1)).mp hc
    exact h.mono (fun _ hp hk hu => (hp ⟨hk, hu⟩).2.2)
  have he := S.ae_rootChargeRow_on_constant_block k u hW hd hgap b hb
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' he
  have hble : b ≤ 1 := hx ▸ (S.rootChargeRow_mem_Icc k x).2
  have hbne : b ≠ 1 := by
    intro hb1
    apply hnot
    exact ⟨hku, hb.mono (fun _ hp hk hu => (hp hk hu).trans hb1)⟩
  exact he.mono (fun _ hx => hx ▸ lt_of_le_of_ne hble hbne)

/-- The actual signed star variation bounds the root mass by any concrete
common-neighbor cover. Feasibility and original optimum comparison come
from the root-repricing theorem, rather than an edited-model input. -/
theorem root_mass_le_cover_of_unsaturated_head
    (S : SelectedHighLowStructure W m) (k : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (P Z : Set Ω) (hP : MeasurableSet P) (hPpos : 0 < μ P) (hZ : MeasurableSet Z)
    (hjoined : ∀ᵐ x ∂μ.restrict P, x ∈ S.rootNeighborhood k)
    (hslack : ∀ᵐ x ∂μ.restrict P, S.rootChargeRow k x < 1)
    (hcover : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ S.rootNeighborhood k →
      p.2 ∉ Z → adjacencyKernel W p.1 p.2 = 0) :
    μ.real {x | S.ρ x = k.val} ≤ μ.real Z := by
  have hG : Measurable (Function.uncurry (adjacencyKernel W)) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable
  have hb : ∀ᵐ p ∂μ.prod μ, adjacencyKernel W p.1 p.2 ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall (fun p => adjacency_moment_mem W p)
  have hupper := CliqueStarVariation.ae_neighborhood_integral_le_cover
    (adjacencyKernel W) hG hb P (S.rootNeighborhood k) Z
    (S.measurableSet_rootNeighborhood k) hZ hcover
  have hgood : ∀ᵐ x ∂μ.restrict P,
      μ.real {z | S.ρ z = k.val} ≤ μ.real Z := by
    filter_upwards [hjoined, hslack,
      ae_restrict_of_ae (S.ae_original_root_degree_ge_mass k hW hd hgap),
      ae_restrict_of_ae hupper, ae_restrict_mem hP] with x hn hs hl hu hx
    exact (hl hn hs).trans (hu hx)
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hPpos.ne' hgood
  exact hx

end Erdos1017.CappedModel.SelectedHighLowStructure
