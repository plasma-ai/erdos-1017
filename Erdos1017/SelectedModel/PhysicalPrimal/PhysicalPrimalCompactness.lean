module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp

/-!
# Compactness of exactly balanced clique law families

Exact pair balance, rather than closedness of the clique locus, makes the family
of weighted clique laws compact, the cost is continuous, convergent costs lift
to an exactly balanced limit (`exists_cost_limit`), and permutation invariance
is a closed condition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal

namespace Erdos1017.PhysicalPrimal

variable {ι : Type*} [Fintype ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, TopologicalSpace (Ω i)] [∀ i, CompactSpace (Ω i)]
  [∀ i, T2Space (Ω i)] [∀ i, BorelSpace (Ω i)]
variable {S : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
  [HasOuterApproxClosed S]

/-- The weighted pair marginals of a finite family of clique laws. -/
def pairLoad (c : ι → ℝ≥0) (π : ∀ i, Ω i → S)
    (μs : ∀ i, FiniteMeasure (Ω i)) : FiniteMeasure S :=
  ∑ i, c i • (μs i).map (π i)

/-- The total mass charged by the family. -/
def finiteCost (μs : ∀ i, FiniteMeasure (Ω i)) : ℝ≥0 := ∑ i, (μs i).mass

omit [TopologicalSpace S] [BorelSpace S] [HasOuterApproxClosed S] in
private theorem mass_sum {α : Type*} (s : Finset α) (μ : α → FiniteMeasure S) :
    (∑ i ∈ s, μ i).mass = ∑ i ∈ s, (μ i).mass := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FiniteMeasure.mass]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    simpa [FiniteMeasure.mass, FiniteMeasure.coeFn_add] using ih

omit [∀ i, CompactSpace (Ω i)] [∀ i, T2Space (Ω i)] [HasOuterApproxClosed S] in
theorem pairLoad_mass (c : ι → ℝ≥0) (π : ∀ i, Ω i → S)
    (hπ : ∀ i, Continuous (π i)) (μs : ∀ i, FiniteMeasure (Ω i)) :
    (pairLoad c π μs).mass = ∑ i, c i * (μs i).mass := by
  rw [pairLoad, mass_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [FiniteMeasure.mass, FiniteMeasure.smul_apply,
    FiniteMeasure.map_apply _ (hπ i).measurable MeasurableSet.univ]

omit [∀ i, CompactSpace (Ω i)] [∀ i, T2Space (Ω i)] [HasOuterApproxClosed S] in
theorem continuous_pairLoad (c : ι → ℝ≥0) (π : ∀ i, Ω i → S)
    (hπ : ∀ i, Continuous (π i)) : Continuous (pairLoad c π) := by
  unfold pairLoad
  apply continuous_finsetSum
  intro i _
  have he : Continuous (fun μs : ∀ i, FiniteMeasure (Ω i) => μs i) := continuous_apply i
  exact ((FiniteMeasure.continuous_map (hπ i)).comp he).const_smul (c i)

omit [∀ i, CompactSpace (Ω i)] [∀ i, T2Space (Ω i)] [HasOuterApproxClosed S] in
theorem component_mass_le (c : ι → ℝ≥0) (hc : ∀ i, 1 ≤ c i)
    (π : ∀ i, Ω i → S) (hπ : ∀ i, Continuous (π i))
    (ν : FiniteMeasure S) {μs : ∀ i, FiniteMeasure (Ω i)}
    (hμs : pairLoad c π μs = ν) (i : ι) : (μs i).mass ≤ ν.mass := by
  calc
    (μs i).mass ≤ c i * (μs i).mass := le_mul_of_one_le_left (zero_le) (hc i)
    _ ≤ ∑ j, c j * (μs j).mass :=
      Finset.single_le_sum (f := fun j => c j * (μs j).mass) (fun j _ => bot_le) (Finset.mem_univ i)
    _ = ν.mass := by rw [← pairLoad_mass c π hπ, hμs]

omit [TopologicalSpace S] [BorelSpace S] [HasOuterApproxClosed S] in
private theorem sum_apply {α : Type*} (s : Finset α) (μ : α → FiniteMeasure S)
    (B : Set S) : (∑ i ∈ s, μ i) B = ∑ i ∈ s, μ i B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, FiniteMeasure.coeFn_add, Pi.add_apply, ih]

omit [∀ i, CompactSpace (Ω i)] [∀ i, T2Space (Ω i)] [HasOuterApproxClosed S] in
/-- Pair balance controls every measurable pair event, including forbidden edges. -/
theorem component_pair_le (c : ι → ℝ≥0) (hc : ∀ i, 1 ≤ c i)
    (π : ∀ i, Ω i → S) (hπ : ∀ i, Continuous (π i))
    (ν : FiniteMeasure S) {μs : ∀ i, FiniteMeasure (Ω i)}
    (hμs : pairLoad c π μs = ν) (i : ι) (B : Set S) (hB : MeasurableSet B) :
    μs i (π i ⁻¹' B) ≤ ν B := by
  have heq : ν B = ∑ j, c j * μs j (π j ⁻¹' B) := by
    rw [← hμs, pairLoad, sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp [FiniteMeasure.smul_apply, FiniteMeasure.map_apply _ (hπ j).measurable hB]
  rw [heq]
  exact (le_mul_of_one_le_left (zero_le) (hc i)).trans
    (Finset.single_le_sum (f := fun j => c j * μs j (π j ⁻¹' B))
      (fun j _ => bot_le) (Finset.mem_univ i))

omit [∀ i, CompactSpace (Ω i)] [∀ i, T2Space (Ω i)] [HasOuterApproxClosed S] in
/-- No topological closedness of the forbidden pair set is required. -/
theorem component_pair_null (c : ι → ℝ≥0) (hc : ∀ i, 1 ≤ c i)
    (π : ∀ i, Ω i → S) (hπ : ∀ i, Continuous (π i))
    (ν : FiniteMeasure S) {μs : ∀ i, FiniteMeasure (Ω i)}
    (hμs : pairLoad c π μs = ν) (i : ι) (B : Set S) (hB : MeasurableSet B)
    (hν : ν B = 0) : μs i (π i ⁻¹' B) = 0 := by
  exact le_antisymm ((component_pair_le c hc π hπ ν hμs i B hB).trans_eq hν) bot_le

/-- Exact pair balance, rather than closedness of the measurable clique locus,
provides the compact constraint used in the physical-primal limit. -/
theorem isCompact_balanced (c : ι → ℝ≥0) (hc : ∀ i, 1 ≤ c i)
    (π : ∀ i, Ω i → S) (hπ : ∀ i, Continuous (π i))
    (ν : FiniteMeasure S) :
    IsCompact {μs : ∀ i, FiniteMeasure (Ω i) | pairLoad c π μs = ν} := by
  have hbox : IsCompact {μs : ∀ i, FiniteMeasure (Ω i) | ∀ i, (μs i).mass ≤ ν.mass} :=
    isCompact_pi_infinite (fun i =>
      isCompact_setOfPred_finiteMeasure_le_of_compactSpace (Ω i) ν.mass)
  exact hbox.of_isClosed_subset
    (isClosed_eq (continuous_pairLoad c π hπ) continuous_const)
    (fun μs hμs i => component_mass_le c hc π hπ ν hμs i)

omit [∀ i, CompactSpace (Ω i)] [∀ i, T2Space (Ω i)] in
theorem continuous_cost : Continuous (finiteCost (Ω := Ω)) := by
  unfold finiteCost
  exact continuous_finsetSum _ (fun i _ => FiniteMeasure.continuous_mass.comp (continuous_apply i))

/-- Convergence of costs can be lifted to an exactly balanced limiting family.
The input families must already have the exact demand, as in averaged sampling. -/
theorem exists_cost_limit (c : ι → ℝ≥0) (hc : ∀ i, 1 ≤ c i)
    (π : ∀ i, Ω i → S) (hπ : ∀ i, Continuous (π i))
    (ν : FiniteMeasure S) (A : Set (∀ i, FiniteMeasure (Ω i))) (hA : IsClosed A)
    (μs : ℕ → ∀ i, FiniteMeasure (Ω i))
    (hμs : ∀ n, μs n ∈ A ∧ pairLoad c π (μs n) = ν)
    (v : ℝ≥0) (hv : Filter.Tendsto (fun n => finiteCost (μs n)) Filter.atTop (nhds v)) :
    ∃ η ∈ A, pairLoad c π η = ν ∧ finiteCost η = v := by
  have hk := (isCompact_balanced c hc π hπ ν).inter_left hA
  have hclosed := (hk.image continuous_cost).isClosed
  have hv' : v ∈ finiteCost '' (A ∩ {η | pairLoad c π η = ν}) :=
    hclosed.mem_of_tendsto hv (Filter.Eventually.of_forall (fun n => ⟨μs n, hμs n, rfl⟩))
  obtain ⟨η, hη, heq⟩ := hv'
  exact ⟨η, hη.1, hη.2, heq⟩

omit [Fintype ι] [∀ i, CompactSpace (Ω i)] [∀ i, T2Space (Ω i)] in
/-- Invariance under continuous coordinate permutations is a closed condition
on the family of laws. The index types may list all permutations of each tuple. -/
theorem isClosed_invariant [∀ i, HasOuterApproxClosed (Ω i)]
    {J : ι → Type*} (σ : ∀ i, J i → Ω i → Ω i)
    (hσ : ∀ i j, Continuous (σ i j)) :
    IsClosed {μs : ∀ i, FiniteMeasure (Ω i) | ∀ i j, (μs i).map (σ i j) = μs i} := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq
    ((FiniteMeasure.continuous_map (hσ i j)).comp (continuous_apply i)) (continuous_apply i)

/-- Any additional closed restrictions, such as permutation invariance, preserve
attainment. Nonemptiness must be supplied by the actual primal construction. -/
theorem exists_minimum (c : ι → ℝ≥0) (hc : ∀ i, 1 ≤ c i)
    (π : ∀ i, Ω i → S) (hπ : ∀ i, Continuous (π i))
    (ν : FiniteMeasure S) (A : Set (∀ i, FiniteMeasure (Ω i))) (hA : IsClosed A)
    (hne : (A ∩ {μs | pairLoad c π μs = ν}).Nonempty) :
    ∃ μs ∈ A, pairLoad c π μs = ν ∧
      ∀ η ∈ A, pairLoad c π η = ν → finiteCost μs ≤ finiteCost η := by
  have hk := (isCompact_balanced c hc π hπ ν).inter_left hA
  obtain ⟨μs, hμs, hmin⟩ := hk.exists_isMinOn hne continuous_cost.continuousOn
  exact ⟨μs, hμs.1, hμs.2, fun η hη heq => hmin ⟨hη, heq⟩⟩

end Erdos1017.PhysicalPrimal
