module

public import Erdos1017.Multipartite.Physical.PhysicalLawMap
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Graph demand and its tail from an omitted component

Ordered graph demand is defined from a vertex measure and a measurable edge
relation, and the tail of edges touching an omitted component costs at most
total mass times omitted mass, so a partition of the retained measure extends to
the full graph by order-two laws (`pairRepair_graph`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.PhysicalPrimal

open MeasureTheory

variable {V : Type*} [MeasurableSpace V]

/-- Ordered graph demand from a vertex measure and a measurable edge relation. -/
def graphDemand (η : Measure V) (E : Set (V × V)) : Measure (V × V) :=
  (η.prod η).restrict E

/-- All graph edges with at least one vertex in the omitted measure component. -/
def tailDemand (η τ : Measure V) (E : Set (V × V)) : Measure (V × V) :=
  (η.prod τ + τ.prod η + τ.prod τ).restrict E

/-- Product expansion gives exact demand balance, without requiring disjoint supports. -/
theorem graphDemand_add (η τ : Measure V) [SFinite η] [SFinite τ] (E : Set (V × V)) :
    graphDemand (η + τ) E = graphDemand η E + tailDemand η τ E := by
  unfold graphDemand tailDemand
  simp only [Measure.add_prod, Measure.prod_add, Measure.restrict_add]
  ac_rfl

theorem tailDemand_swap (η τ : Measure V) [SFinite η] [SFinite τ]
    (E : Set (V × V)) (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E) :
    (tailDemand η τ E).map Prod.swap = tailDemand η τ E := by
  unfold tailDemand
  rw [← hsym, ← Measure.restrict_map measurable_swap hE]
  rw [Measure.map_add _ _ measurable_swap, Measure.map_add _ _ measurable_swap]
  simp only [Measure.prod_swap]
  congr 1
  · ac_rfl
  · exact hsym.symm

theorem tailDemand_supported (η τ : Measure V) (E : Set (V × V)) (hE : MeasurableSet E) :
    ∀ᵐ z ∂tailDemand η τ E, z ∈ E := ae_restrict_mem hE

/-- Pair repair of tail edges costs at most total vertex mass times omitted mass. -/
theorem tailDemand_mass_bound (η τ : Measure V) [IsFiniteMeasure η] [IsFiniteMeasure τ]
    (E : Set (V × V)) :
    (tailDemand η τ E).real Set.univ / 2 ≤
      (η.real Set.univ + τ.real Set.univ) * τ.real Set.univ := by
  have hle : (tailDemand η τ E).real Set.univ ≤
      (η.prod τ + τ.prod η + τ.prod τ).real Set.univ := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact Measure.restrict_le_self _
  have hmass : (η.prod τ + τ.prod η + τ.prod τ).real Set.univ =
      2 * η.real Set.univ * τ.real Set.univ + (τ.real Set.univ) ^ 2 := by
    rw [measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _),
      measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)]
    have hprod (μ ν : Measure V) [SFinite ν] : (μ.prod ν).real Set.univ = μ.real Set.univ * ν.real Set.univ := by
      simpa only [Set.univ_prod_univ] using measureReal_prod_prod (μ := μ) (ν := ν) Set.univ Set.univ
    rw [hprod, hprod, hprod]
    ring
  rw [hmass] at hle
  nlinarith [sq_nonneg (τ.real Set.univ)]

/-- An actual partition of the retained vertex measure extends to the full graph
by covering all omitted-vertex edges with order-two laws. -/
theorem pairRepair_graph (η τ : Measure V) [IsFiniteMeasure η] [IsFiniteMeasure τ]
    (E : Set (V × V)) (hE : MeasurableSet E) (hsym : Prod.swap ⁻¹' E = E)
    (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (hμ : Feasible (fun x y => (x, y) ∈ E) (graphDemand η E) μ) :
    Feasible (fun x y => (x, y) ∈ E) (graphDemand (η + τ) E)
        (pairRepair μ (tailDemand η τ E)) ∧
      cost (pairRepair μ (tailDemand η τ E)) ≤ cost μ +
        (η.real Set.univ + τ.real Set.univ) * τ.real Set.univ := by
  have : IsFiniteMeasure (graphDemand η E) := by unfold graphDemand; infer_instance
  have : IsFiniteMeasure (tailDemand η τ E) := by unfold tailDemand; infer_instance
  constructor
  · rw [graphDemand_add]
    apply pairRepair_feasible μ _ _ _ hμ hE
    · intro x y hxy
      change (x, y) ∈ Prod.swap ⁻¹' E
      rwa [hsym]
    · exact tailDemand_supported η τ E hE
    · exact tailDemand_swap η τ E hE hsym
  · rw [cost_pairRepair μ (graphDemand η E) (tailDemand η τ E)
      hμ.1 hμ.2.1 hμ.2.2.2]
    linarith [tailDemand_mass_bound η τ E]

end Erdos1017.PhysicalPrimal
