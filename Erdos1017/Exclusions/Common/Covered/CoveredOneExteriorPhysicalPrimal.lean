module

public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorBlocks
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorGate
public import Erdos1017.Exclusions.Common.Physical.PhysicalChildCountMeasure
public import Erdos1017.Exclusions.Common.Physical.PhysicalPositiveCover
public import Erdos1017.SelectedModel.Selection.FullStrictGapPhysicalPrimal

/-!
# Tight moment data from the one-exterior optimum

A `FullStationaryClass` optimum constructs its own child cost law
`TightMomentData`: the original pair occupation pays both moments and the tight
parents pay every child test (`exists_tightMomentData_of_fullStationaryClass`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CoveredOneExterior

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The supplied own optimum constructs its actual child cost law.
Original pair occupation pays both moments, and original tight parents
pay every true child test. No primal or count certificate is supplied. -/
theorem exists_tightMomentData_of_fullStationaryClass
    (label : Ω → Fin 4) (hlabel : Measurable label) (y : Coefficients) (hy : y ∈ feasible)
    (V : CappedModel.Model Ω μ) {d c m : ℝ} (hV : CappedModel.FullStationaryClass d c V m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    Nonempty (TightMomentData y (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3}))) := by
  obtain ⟨N, _, _, η, hfinite, hcap, _, hη, _, _, htight⟩ :=
    hV.exists_physical_primal_of_strict_gap hd.2 hgap
  let : ∀ n, IsFiniteMeasure (η n) := hfinite
  let B := label ⁻¹' {1}
  let C := label ⁻¹' {2}
  let E := label ⁻¹' {3}
  let G := {p : Ω × Ω | blockAdjacency (label p.1) (label p.2) = true}
  have hB : MeasurableSet B := hlabel (measurableSet_singleton 1)
  have hC : MeasurableSet C := hlabel (measurableSet_singleton 2)
  have hE : MeasurableSet E := hlabel (measurableSet_singleton 3)
  have hG : MeasurableSet G :=
    ((measurable_of_countable (Function.uncurry blockAdjacency)).comp
      ((hlabel.comp measurable_fst).prodMk (hlabel.comp measurable_snd)))
      (measurableSet_singleton true)
  let demand := PhysicalPrimal.graphDemand μ G
  let : IsFiniteMeasure demand := by
    dsimp only [demand, PhysicalPrimal.graphDemand]
    infer_instance
  have hdem : (μ.prod μ).withDensity
      (fun p => ENNReal.ofReal (V.moment CappedColor.adjacency p)) = demand := by
    change _ = (μ.prod μ).restrict G
    rw [← withDensity_indicator_one hG]
    apply withDensity_congr_ae
    filter_upwards with p
    rw [(hmom p).1]
    by_cases hp : blockAdjacency (label p.1) (label p.2) = true <;>
      simp [G, hp]
  have hbalance : PhysicalPrimal.occupation η = demand := hη.2.2.2.trans hdem
  have hclique (n : ℕ) : ∀ᵐ v ∂η n,
      FiniteArity.TupleClique (fun a b => blockAdjacency (label a) (label b)) v := by
    filter_upwards [hη.2.2.1 n] with v hv i j hij
    have h := hv i j hij
    rw [(hmom (v i, v j)).1] at h
    cases hg : blockAdjacency (label (v i)) (label (v j)) <;> simp_all
  have hcover : ∀ᵐ p ∂demand, p.1 ∉ B → p.2 ∉ B →
      CappedModel.chargeKernel V p.1 p.2 ≤ 0 := by
    filter_upwards with p hp hq
    change label p.1 ≠ 1 at hp
    change label p.2 ≠ 1 at hq
    change V.moment CappedColor.charge p ≤ 0
    rw [(hmom p).2]
    have hi : label p.1 = 0 ∨ label p.1 = 2 ∨ label p.1 = 3 := by omega
    have hj : label p.2 = 0 ∨ label p.2 = 2 ∨ label p.2 = 3 := by omega
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
      simp [blockCharge, hi, hj, hy.1]
  have hroot (n : ℕ) : ∀ᵐ v ∂η n, ∃! i, v i ∈ B := by
    filter_upwards [PhysicalPrimal.ae_parent_meets_positive_cover η demand hbalance
      (Function.uncurry (CappedModel.chargeKernel V)) B hcover htight n, hclique n]
      with v hv hc
    obtain ⟨i, hi⟩ := hv
    refine ⟨i, hi, ?_⟩
    intro j hj
    by_contra hji
    have h := hc j i hji
    change label (v i) = 1 at hi
    change label (v j) = 1 at hj
    simp [hi, hj, blockAdjacency] at h
  have hCcount (n : ℕ) : ∀ᵐ v ∂η n, PhysicalPrimal.tupleCount C v ≤ 1 := by
    filter_upwards [hclique n] with v hv
    suffices PhysicalPrimal.labelCount (fun i => label (v i)) 2 ≤ 1 by
      simpa only [PhysicalPrimal.labelCount, PhysicalPrimal.tupleCount, C,
        mem_preimage, mem_singleton_iff] using this
    apply PhysicalPrimal.labelCount_le_one
    intro i j hi hj
    by_contra hij
    have h := hv i j hij
    simp [hi, hj, blockAdjacency] at h
  let θ := PhysicalPrimal.countMeasure N η C E
  have hbool : ∀ᵐ z ∂θ, z.1 ≤ 1 :=
    PhysicalPrimal.ae_countMeasure N η C E hC hE (fun z => z.1 ≤ 1) hCcount
  have hBC : Disjoint B C := by
    apply Set.disjoint_left.mpr
    intro v hvB hvC
    change label v = 1 at hvB
    change label v = 2 at hvC
    omega
  have hCE : Disjoint C E := by
    apply Set.disjoint_left.mpr
    intro v hvC hvE
    change label v = 2 at hvC
    change label v = 3 at hvE
    omega
  have hcap' (n : ℕ) (hn : N < n) : η n = 0 := hcap n (Or.inr hn)
  have hBCmass : demand.real (B ×ˢ C) = μ.real B * μ.real C := by
    apply PhysicalPrimal.graphDemand_real_rectangle μ G B C hB hC
    filter_upwards with p hp hq
    change label p.1 = 1 at hp
    change label p.2 = 2 at hq
    simp [G, hp, hq, blockAdjacency]
  have hCEmass : demand.real (C ×ˢ E) = μ.real C * μ.real E := by
    apply PhysicalPrimal.graphDemand_real_rectangle μ G C E hC hE
    filter_upwards with p hp hq
    change label p.1 = 2 at hp
    change label p.2 = 3 at hq
    simp [G, hp, hq, blockAdjacency]
  have htrue : ∀ᵐ z ∂θ, z.1 = 1 → test true z.2 y = 1 := by
    apply PhysicalPrimal.ae_countMeasure N η C E hC hE
    intro n
    filter_upwards [hclique n, hroot n, htight n] with v hv hb ht hc
    have h2 : PhysicalPrimal.labelCount (fun i => label (v i)) 2 = 1 := by
      simpa only [PhysicalPrimal.labelCount, PhysicalPrimal.tupleCount, C,
        mem_preimage, mem_singleton_iff] using hc
    have h1 : PhysicalPrimal.labelCount (fun i => label (v i)) 1 = 1 := by
      simpa only [PhysicalPrimal.labelCount, PhysicalPrimal.tupleCount, B,
        mem_preimage, mem_singleton_iff] using
        PhysicalPrimal.tupleCount_eq_one_of_unique B v hb
    have hex : ∃ i, label (v i) = 2 := by
      by_contra hn
      push Not at hn
      simp [PhysicalPrimal.labelCount, hn] at h2
    obtain ⟨j, hj⟩ := hex
    have hnot (i : Fin n) : label (v i) ≠ 0 := by
      intro hi
      have hij : i ≠ j := by intro he; simp [he, hj] at hi
      have h := hv i j hij
      simp [hi, hj, blockAdjacency] at h
    have h0 : PhysicalPrimal.labelCount (fun i => label (v i)) 0 = 0 := by
      simp [PhysicalPrimal.labelCount, hnot]
    have hY : Function.uncurry (CappedModel.chargeKernel V) =
        Function.uncurry (fun a b => blockCharge y (label a) (label b)) := by
      funext p
      exact (hmom p).2
    rw [hY, PhysicalPrimal.charge_uncurry_eq_tupleCharge] at ht
    have he := block_tupleCharge_eq_test y (fun i => label (v i)) h0 h1 h2
    have ht' : FiniteArity.tupleCharge (blockCharge y) (fun i => label (v i)) = 1 := ht
    rw [he] at ht'
    simpa only [PhysicalPrimal.labelCount, PhysicalPrimal.tupleCount, E,
      mem_preimage, mem_singleton_iff] using ht'
  refine ⟨⟨PhysicalPrimal.childCountMeasure θ, inferInstance, ?_, ?_, ?_, ?_⟩⟩
  · exact PhysicalPrimal.integrable_childCountMeasure θ (fun n : ℕ => (n : ℝ))
      (PhysicalPrimal.integrable_countMeasure N η C E hC hE (fun z => (z.2 : ℝ)))
  · rw [PhysicalPrimal.childCountMeasure_mass θ hbool]
    exact (PhysicalPrimal.countMeasure_first_moment N η B C E hB hC hE
      hBC hroot hcap' demand hbalance).trans hBCmass
  · rw [PhysicalPrimal.childCountMeasure_first θ hbool]
    exact (PhysicalPrimal.countMeasure_cross_moment N η C E hC hE
      hCE hcap' demand hbalance).trans hCEmass
  · exact PhysicalPrimal.ae_childCountMeasure θ (fun n => test true n y = 1) htrue

end Erdos1017.CoveredOneExterior
