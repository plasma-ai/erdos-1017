module

public import Erdos1017.Multipartite.Physical.PhysicalGraphTail
public import Erdos1017.Multipartite.Physical.PhysicalPrimalAssembly

/-!
# Leaf measure of a root set

`rootLeaves` counts the other vertices of each parent coordinate lying in a root
set; under balance every leaf event has its root-to-event pair demand, an
independent root set occurs in at most one coordinate of almost every parent,
and a homogeneous adjacency row gives the leaf measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- Count every other vertex for every coordinate whose physical point lies
in the supplied root set. This retains the original joint parent measure. -/
def orderRootLeaves (n : ℕ) (ρ : Measure (Fin n → V)) (I : Set V) : Measure V :=
  ∑ ij : PairIndex n,
    (ρ.restrict {v | v ij.val.1 ∈ I}).map (fun v => v ij.val.2)

/-- Actual leaf counting over all parent orders, without normalizing the
mass of parents that contain a root. -/
def rootLeaves (μ : Laws V) (I : Set V) : Measure V :=
  Measure.sum (fun n => orderRootLeaves n (μ n) I)

/-- The counted leaves at one order are exactly the second marginal of
the ordered pair occupation restricted at its first endpoint. -/
theorem orderRootLeaves_eq_snd_restrict (n : ℕ) (ρ : Measure (Fin n → V))
    (I : Set V) (hI : MeasurableSet I) :
    orderRootLeaves n ρ I = ((orderOccupation n ρ).restrict (I ×ˢ univ)).snd := by
  classical
  ext B hB
  rw [orderRootLeaves, Measure.finsetSum_apply, Measure.snd_apply hB,
    Measure.restrict_apply (measurable_snd hB), orderOccupation, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Measure.map_apply (measurable_pi_apply _) hB,
    Measure.restrict_apply ((measurable_pi_apply _) hB),
    Measure.map_apply ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
      ((measurable_snd hB).inter (hI.prod MeasurableSet.univ))]
  congr 1
  ext v
  simp

/-- The complete all-order leaf measure is derived from actual coordinate
counts and exact pair occupation, including singular parent laws. -/
theorem rootLeaves_eq_snd_restrict (μ : Laws V) (I : Set V) (hI : MeasurableSet I) :
    rootLeaves μ I = ((occupation μ).restrict (I ×ˢ univ)).snd := by
  unfold rootLeaves occupation
  rw [Measure.restrict_sum _ (hI.prod MeasurableSet.univ), Measure.snd_sum]
  congr 1
  funext n
  exact orderRootLeaves_eq_snd_restrict n (μ n) I hI

theorem rootLeaves_of_balance (μ : Laws V) (demand : Measure (V × V))
    (hbalance : occupation μ = demand) (I : Set V) (hI : MeasurableSet I) :
    rootLeaves μ I = (demand.restrict (I ×ˢ univ)).snd := by
  rw [rootLeaves_eq_snd_restrict μ I hI, hbalance]

/-- Every measurable leaf event has precisely its actual root-to-event
ordered pair demand. There is no division by the root-parent mass. -/
theorem rootLeaves_apply_of_balance (μ : Laws V) (demand : Measure (V × V))
    (hbalance : occupation μ = demand) (I B : Set V)
    (hI : MeasurableSet I) (hB : MeasurableSet B) :
    rootLeaves μ I B = demand (I ×ˢ B) := by
  rw [rootLeaves_of_balance μ demand hbalance I hI, Measure.snd_apply hB,
    Measure.restrict_apply (measurable_snd hB)]
  congr 1
  ext p
  simp [and_comm]

/-- An independent root set occurs in at most one coordinate of almost
every actual parent, using only its zero internal ordered pair demand. -/
theorem ae_at_most_one_root_of_balance (μ : Laws V) (demand : Measure (V × V))
    (hbalance : occupation μ = demand) (I : Set V)
    (hindependent : demand (I ×ˢ I) = 0) (n : ℕ) :
    ∀ᵐ v ∂μ n, ∀ i j, v i ∈ I → v j ∈ I → i = j := by
  have hp : ∀ᵐ p ∂demand, ¬(p.1 ∈ I ∧ p.2 ∈ I) := by
    rw [ae_iff]
    have heq : {p : V × V | ¬¬(p.1 ∈ I ∧ p.2 ∈ I)} = I ×ˢ I := by
      ext p
      simp
    rw [heq]
    exact hindependent
  filter_upwards [ae_all_pairs_of_balance μ demand hbalance
    (fun p => ¬(p.1 ∈ I ∧ p.2 ∈ I)) hp n] with v hv
  intro i j hi hj
  by_contra hij
  exact hv i j hij ⟨hi, hj⟩

theorem ae_at_most_one_root_graphDemand (μ : Laws V) (η : Measure V)
    (E : Set (V × V)) (hbalance : occupation μ = graphDemand η E)
    (I : Set V) (hI : MeasurableSet I)
    (hindependent : (η.prod η) (E ∩ (I ×ˢ I)) = 0) (n : ℕ) :
    ∀ᵐ v ∂μ n, ∀ i j, v i ∈ I → v j ∈ I → i = j := by
  apply ae_at_most_one_root_of_balance μ (graphDemand η E) hbalance I _ n
  rw [graphDemand, Measure.restrict_apply (hI.prod hI), Set.inter_comm]
  exact hindependent

/-- A homogeneous original adjacency row identifies the entire leaf measure
with the root-set mass times the original vertex measure on its neighborhood. -/
theorem rootLeaves_graphDemand_homogeneous (μ : Laws V) (η : Measure V) [SFinite η]
    (E : Set (V × V)) (hE : MeasurableSet E)
    (hbalance : occupation μ = graphDemand η E)
    (I N : Set V) (hI : MeasurableSet I)
    (hrow : ∀ᵐ p ∂(η.restrict I).prod η, p ∈ E ↔ p.2 ∈ N) :
    rootLeaves μ I = η I • η.restrict N := by
  rw [rootLeaves_of_balance μ _ hbalance I hI, graphDemand,
    Measure.restrict_restrict (hI.prod MeasurableSet.univ), Set.inter_comm,
    ← Measure.restrict_restrict hE]
  have hprod : (η.prod η).restrict (I ×ˢ univ) = (η.restrict I).prod η := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod]
  have hsets : E =ᵐ[(η.restrict I).prod η] (univ ×ˢ N) := by
    filter_upwards [hrow] with p hp
    apply propext
    simpa only [mem_prod, mem_univ, true_and] using hp
  rw [Measure.restrict_congr_set hsets, ← Measure.prod_restrict,
    Measure.restrict_univ, Measure.snd, Measure.map_snd_prod,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]

/-- The root-leaf intensity formula holds on every measurable
event; independence gives each root-containing parent a unique root in I. -/
theorem rootLeaves_graphDemand_apply (μ : Laws V) (η : Measure V) [SFinite η]
    (E : Set (V × V)) (hE : MeasurableSet E)
    (hbalance : occupation μ = graphDemand η E)
    (I N B : Set V) (hI : MeasurableSet I)
    (hB : MeasurableSet B)
    (hrow : ∀ᵐ p ∂(η.restrict I).prod η, p ∈ E ↔ p.2 ∈ N) :
    rootLeaves μ I B = η I * η (B ∩ N) := by
  rw [rootLeaves_graphDemand_homogeneous μ η E hE hbalance I N hI hrow,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]

end Erdos1017.PhysicalPrimal
