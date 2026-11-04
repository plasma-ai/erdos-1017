module

public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.SelectedModel.Selection.FullStrictGapPhysicalPrimal
public import Erdos1017.Exclusions.Common.Physical.PhysicalRootReplacementOccupation

/-!
# Physical primal of a universal root

This module defines the same-model physical root data with its whole independent
fiber and full outside neighborhood, and constructs it from the full strict-gap
optimum with a bounded-order tight primal and the exact root-leaf law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Same-model physical root data, with the actual whole independent fiber
and its full outside neighborhood. Joint parent laws may be singular. -/
structure UniversalPhysicalPrimal (S : SelectedHighLowStructure W m) (r : S.I) (c : ℝ) where
  orderCap : ℕ
  orderCap_ge_two : 2 ≤ orderCap
  laws : PhysicalPrimal.Laws Ω
  finite : ∀ n, IsFiniteMeasure (laws n)
  capped : ∀ n, n < 2 ∨ orderCap < n → laws n = 0
  feasible : PhysicalPrimal.Feasible
    (fun x y => PhysicalRepresentative.adjacency W m x y = true)
    (PhysicalPrimal.graphDemand μ {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true}) laws
  cost : PhysicalPrimal.cost laws = c
  distinct : ∀ n, ∀ᵐ v ∂laws n, Function.Injective v
  tight_original : ∀ n, ∀ᵐ v ∂laws n,
    PhysicalPrimal.charge (Function.uncurry (chargeKernel W)) v = 1
  tight_physical : ∀ n, ∀ᵐ v ∂laws n,
    PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v = 1
  leaves : PhysicalPrimal.rootLeaves laws {x | S.ρ x = r.val} =
    μ {x | S.ρ x = r.val} • μ.restrict {x | S.ρ x ≠ r.val}
  unique_root : ∀ n, ∀ᵐ v ∂laws n, ∀ i j,
    S.ρ (v i) = r.val → S.ρ (v j) = r.val → i = j

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- The pointwise symmetric physical graph retains the universal row on
the same original whole fiber, with one product-AE exception. -/
theorem neutral_atom_physical_adjacency (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ S.ρ p.2 ≠ r.val) := by
  filter_upwards [S.neutral_atom_adjacency r hW hd hgap hN,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with p hp he hx
  have h := he.symm.trans (hp hx)
  change (if PhysicalRepresentative.adjacency W m p.1 p.2 = true then (1 : ℝ) else 0) =
    (if S.ρ p.2 = r.val then 0 else 1) at h
  cases hA : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
    by_cases hr : S.ρ p.2 = r.val <;> simp_all

/-- Universal physical adjacency supplies both the restricted row law and
zero internal graph demand used by actual root replacement. -/
theorem neutral_atom_physical_blocks (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    (∀ᵐ p ∂(μ.restrict {x | S.ρ x = r.val}).prod μ,
      PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔ S.ρ p.2 ≠ r.val) ∧
    (μ.prod μ) ({p | PhysicalRepresentative.adjacency W m p.1 p.2 = true} ∩
      ({x | S.ρ x = r.val} ×ˢ {x | S.ρ x = r.val})) = 0 := by
  have hp := S.neutral_atom_physical_adjacency r hW hd hgap hN
  constructor
  · filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl) hp,
      Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (S.hfibers r.val r.property).1)] with p hp hx
    exact hp hx
  · apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hp] with p hp hmem
    exact (hp hmem.2.1).mp hmem.1 hmem.2.2

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The original full strict-gap optimum constructs a bounded-order tight
physical primal and the exact universal root-leaf law internally. -/
theorem exists_universal_physical_primal (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    Nonempty (S.UniversalPhysicalPrimal r c) := by
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  obtain ⟨N, hN2, heq, _, _⟩ := hW.exists_physical_primal_of_strict_gap hd.2 hgap
  have hvalue : capValue Ω μ N (density W) = FractionalGraph.densityLimit (density W) := by
    simpa only [hW.density_eq] using heq
  obtain ⟨η, hfinite, hcap, _, hfeasible, hcost, hdistinct, htight⟩ :=
    exists_physical_primal_of_finite_order_equality W hW.full
      (by rw [hW.objective_eq, hW.density_eq]; exact hW.optimal) m hs hW.deterministic N hN2 hvalue
  have hE : MeasurableSet {p : Ω × Ω |
      PhysicalRepresentative.adjacency W m p.1 p.2 = true} :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hb := S.neutral_atom_physical_blocks r hW hd hgap hN
  refine ⟨⟨N, hN2, η, hfinite, hcap, hfeasible, hcost.trans hW.objective_eq,
    hdistinct, htight, ?_, ?_, ?_⟩⟩
  · intro n
    filter_upwards [htight n,
      ae_physical_charge_eq_original W m hs η hfeasible.2.2.2 n] with v hv he
    exact he.trans hv
  · exact PhysicalPrimal.rootLeaves_graphDemand_homogeneous η μ _ hE hfeasible.2.2.2
      {x | S.ρ x = r.val} {x | S.ρ x ≠ r.val} (S.hfibers r.val r.property).1 hb.1
  · exact PhysicalPrimal.ae_at_most_one_root_graphDemand η μ _ hfeasible.2.2.2
      {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 hb.2

namespace ReverseRecovery

variable {S : SelectedHighLowStructure W m} (R : S.ReverseRecovery)

/-- A recovered common head peak supplies its own original universal
physical primal; no primal or root-row hypothesis is used. -/
theorem common_peak_head_physical_primal (r : S.I) (hr : r ∈ R.plateau) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c r) :
    Nonempty (S.UniversalPhysicalPrimal r c) :=
  S.exists_universal_physical_primal r hW hd hgap (R.common_peak_head_neutral r hr hpeak)

end ReverseRecovery

end Erdos1017.CappedModel.SelectedHighLowStructure
