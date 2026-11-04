module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateRootStar
public import Erdos1017.SelectedModel.Selection.FullStrictGapPhysicalPrimal

/-!
# Physical primal of a private two-root model

The structure `PrivatePhysicalPrimal` packages the private two-root primal data,
distinct whole roots sharing an independent union with different exact leaf
quotas, and the private model constructs its own attained physical laws and both
root quotas with at most one root in the union.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Actual original private two-root primal data. The distinct whole roots
share an independent union and retain their different exact leaf quotas. -/
structure PrivatePhysicalPrimal (S : SelectedHighLowStructure W m) (i p : S.I) (c : ℝ) where
  orderCap : ℕ
  orderCap_ge_two : 2 ≤ orderCap
  distinct_roots : i ≠ p
  laws : PhysicalPrimal.Laws Ω
  finite : ∀ n, IsFiniteMeasure (laws n)
  capped : ∀ n, n < 2 ∨ orderCap < n → laws n = 0
  feasible : PhysicalPrimal.Feasible
    (fun x y => PhysicalRepresentative.adjacency W m x y = true)
    (PhysicalPrimal.graphDemand μ {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true}) laws
  cost : PhysicalPrimal.cost laws = c
  distinct : ∀ n, ∀ᵐ v ∂laws n, Function.Injective v
  tight_original : ∀ n, ∀ᵐ v ∂laws n,
    PhysicalPrimal.charge (Function.uncurry (chargeKernel W)) v = 1
  tight_physical : ∀ n, ∀ᵐ v ∂laws n,
    PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v = 1
  leaves_first : PhysicalPrimal.rootLeaves laws {x | S.ρ x = i.val} =
    μ {x | S.ρ x = i.val} •
      μ.restrict ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ
  leaves_second : PhysicalPrimal.rootLeaves laws {x | S.ρ x = p.val} =
    μ {x | S.ρ x = p.val} • μ.restrict (S.rootNeighborhood p)
  unique_roots : ∀ n, ∀ᵐ v ∂laws n, ∀ j k,
    (S.ρ (v j) = i.val ∨ S.ρ (v j) = p.val) →
      (S.ρ (v k) = i.val ∨ S.ρ (v k) = p.val) → j = k

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

private theorem private_physical_blocks
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    let E := {z : Ω × Ω | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
    (∀ᵐ z ∂(μ.restrict I).prod μ, z ∈ E ↔ z.2 ∉ I ∪ P) ∧
      (∀ᵐ z ∂(μ.restrict P).prod μ, z ∈ E ↔ z.2 ∈ S.rootNeighborhood p) ∧
        (μ.prod μ) (E ∩ ((I ∪ P) ×ˢ (I ∪ P))) = 0 := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let E := {z : Ω × Ω | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hrowI : ∀ᵐ z ∂μ.prod μ, z.1 ∈ I → (z ∈ E ↔ z.2 ∉ I ∪ P) := by
    filter_upwards [S.ae_root_adjacency i hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae
        (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate)]
      with z hr hn hx
    exact (hr hx).trans (by simpa only [I, P, mem_union, mem_ofPred_eq, not_or] using hn)
  constructor
  · filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl) hrowI,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI)] with z hz hx
    exact hz hx
  constructor
  · filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl)
      (S.ae_root_adjacency p hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP)] with z hz hx
    exact hz hx
  · have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hrowI, hswap.ae hrowI,
      S.ae_root_fiber_physical_independent p hW hd hgap] with z hi hir hp hz
    rcases hz.2.1 with hx | hx
    · exact (hi hx).mp hz.1 hz.2.2
    · rcases hz.2.2 with hy | hy
      · have hr := hir hy
        have hG : PhysicalRepresentative.adjacency W m z.2 z.1 = true := by
          rw [PhysicalRepresentative.adjacency_symm W m z.2 z.1]
          exact hz.1
        exact hr.mp hG (Or.inr hx)
      · have hfalse := hp hx hy
        have htrue : PhysicalRepresentative.adjacency W m z.1 z.2 = true := hz.1
        rw [hfalse] at htrue
        exact Bool.false_ne_true htrue

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The original private model constructs its own attained physical laws
and both exact root quotas, with at most one root in their independent union. -/
theorem exists_private_physical_primal
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    Nonempty (S.PrivatePhysicalPrimal i p c) := by
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  obtain ⟨N, hN2, heq, _, _⟩ := hW.exists_physical_primal_of_strict_gap hd.2 hgap
  have hvalue : capValue Ω μ N (density W) = FractionalGraph.densityLimit (density W) := by
    simpa only [hW.density_eq] using heq
  obtain ⟨η, hfinite, hcap, _, hfeasible, hcost, hdistinct, htight⟩ :=
    exists_physical_primal_of_finite_order_equality W hW.full
      (by rw [hW.objective_eq, hW.density_eq]; exact hW.optimal) m hs hW.deterministic N hN2 hvalue
  have hE : MeasurableSet {z : Ω × Ω |
      PhysicalRepresentative.adjacency W m z.1 z.2 = true} :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hb := S.private_physical_blocks i p hW hd hgap hprivate
  refine ⟨⟨N, hN2, hip, η, hfinite, hcap, hfeasible, hcost.trans hW.objective_eq,
    hdistinct, htight, ?_, ?_, ?_, ?_⟩⟩
  · intro n
    filter_upwards [htight n,
      ae_physical_charge_eq_original W m hs η hfeasible.2.2.2 n] with v hv he
    exact he.trans hv
  · exact PhysicalPrimal.rootLeaves_graphDemand_homogeneous η μ _ hE hfeasible.2.2.2
      {x | S.ρ x = i.val} ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ
      (S.hfibers i.val i.property).1 hb.1
  · exact PhysicalPrimal.rootLeaves_graphDemand_homogeneous η μ _ hE hfeasible.2.2.2
      {x | S.ρ x = p.val} (S.rootNeighborhood p) (S.hfibers p.val p.property).1 hb.2.1
  · exact PhysicalPrimal.ae_at_most_one_root_graphDemand η μ _ hfeasible.2.2.2
      ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})
      ((S.hfibers i.val i.property).1.union (S.hfibers p.val p.property).1) hb.2.2

end Erdos1017.CappedModel.SelectedHighLowStructure
