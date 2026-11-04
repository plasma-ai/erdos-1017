module

public import Erdos1017.Multipartite.Physical.PhysicalPrimalAssembly
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalPrimalCompactness

/-!
# Finite-order limits of balanced capped laws

Finite families of joint laws at orders two through the cap have a weakly
compact ordered-balance set, so symmetric exactly balanced capped laws with
convergent costs have a symmetric physical limit of the limiting cost
(`exists_symmetric_laws_cost_limit`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- A finite family retaining the actual joint law at every order from two
through the cap. The family is empty when the cap is below two. -/
abbrev BoundedLaws (V : Type*) [MeasurableSpace V] (N : ℕ) :=
  ∀ i : Fin (N - 1), FiniteMeasure (Fin (i.val + 2) → V)

/-- Actual ordered occupation of the bounded family. Every coordinate pair
is retained, so this definition does not require permutation invariance. -/
def boundedOccupation (N : ℕ) (μs : BoundedLaws V N) : FiniteMeasure (V × V) :=
  ∑ i, ∑ ij : PairIndex (i.val + 2),
    (μs i).map (fun v => (v ij.val.1, v ij.val.2))

/-- Embed the finite family into the existing all-orders physical laws. -/
def boundedLaws (N : ℕ) (μs : BoundedLaws V N) : Laws V :=
  assemble (fun i => i.val + 2) (fun i => (μs i : Measure _))

theorem boundedOccupation_toMeasure (N : ℕ) (μs : BoundedLaws V N) :
    (boundedOccupation N μs : Measure (V × V)) = occupation (boundedLaws N μs) := by
  rw [boundedLaws, occupation_assemble]
  simp [boundedOccupation, orderOccupation, FiniteMeasure.toMeasure_sum]

theorem boundedLaws_finite (N : ℕ) (μs : BoundedLaws V N) (n : ℕ) :
    IsFiniteMeasure (boundedLaws N μs n) := assemble_finite _ _ n

/-- Each supported order is the original joint measure, without averaging
or replacing it by a product measure. -/
theorem boundedLaws_apply (N : ℕ) (μs : BoundedLaws V N) (i : Fin (N - 1)) :
    boundedLaws N μs (i.val + 2) = (μs i : Measure _) := by
  classical
  unfold boundedLaws assemble
  rw [Finset.sum_eq_single i]
  · exact singleOrder_self _ _
  · intro j _ hji
    apply singleOrder_ne
    intro h
    have hval : j.val + 2 = i.val + 2 := h
    exact hji (Fin.ext (by omega))
  · simp

theorem boundedLaws_eq_zero (N : ℕ) (μs : BoundedLaws V N) (n : ℕ)
    (hn : n < 2 ∨ N < n) : boundedLaws N μs n = 0 := by
  classical
  unfold boundedLaws assemble
  apply Finset.sum_eq_zero
  intro i _
  apply singleOrder_ne
  intro h
  have hval : i.val + 2 = n := h
  have hi := i.isLt
  omega

/-- The all-orders cost is exactly the real coercion of the finite mass sum. -/
theorem cost_boundedLaws (N : ℕ) (μs : BoundedLaws V N) :
    cost (boundedLaws N μs) = (finiteCost μs : ℝ) := by
  rw [boundedLaws, cost_assemble]
  simp only [finiteCost, NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Extract the finitely many actual measures from a capped all-orders law. -/
def restrictOrders (N : ℕ) (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)] : BoundedLaws V N :=
  fun i => ⟨μ (i.val + 2), inferInstance⟩

/-- Extraction and assembly are inverse on actual capped laws. -/
theorem boundedLaws_restrictOrders (N : ℕ) (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (hcap : ∀ n, n < 2 ∨ N < n → μ n = 0) :
    boundedLaws N (restrictOrders N μ) = μ := by
  funext n
  by_cases hn : n < 2 ∨ N < n
  · rw [boundedLaws_eq_zero N _ n hn, hcap n hn]
  · let i : Fin (N - 1) := ⟨n - 2, by omega⟩
    have hi : i.val + 2 = n := by dsimp [i]; omega
    rw [← hi, boundedLaws_apply]
    rfl

theorem boundedOccupation_restrictOrders (N : ℕ) (μ : Laws V)
    [∀ n, IsFiniteMeasure (μ n)] (hcap : ∀ n, n < 2 ∨ N < n → μ n = 0) :
    (boundedOccupation N (restrictOrders N μ) : Measure (V × V)) = occupation μ := by
  rw [boundedOccupation_toMeasure, boundedLaws_restrictOrders N μ hcap]

theorem cost_restrictOrders (N : ℕ) (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (hcap : ∀ n, n < 2 ∨ N < n → μ n = 0) :
    (finiteCost (restrictOrders N μ) : ℝ) = cost μ := by
  rw [← cost_boundedLaws, boundedLaws_restrictOrders N μ hcap]

section Compactness

variable [MetricSpace V] [CompactSpace V] [BorelSpace V]

omit [MeasurableSpace V] [CompactSpace V] [BorelSpace V] in
private theorem continuous_tuplePair {n : ℕ} (ij : PairIndex n) :
    Continuous (fun v : Fin n → V => (v ij.val.1, v ij.val.2)) :=
  (continuous_apply _).prodMk (continuous_apply _)

theorem continuous_boundedOccupation (N : ℕ) :
    Continuous (boundedOccupation (V := V) N) := by
  unfold boundedOccupation
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro ij _
  exact (FiniteMeasure.continuous_map (continuous_tuplePair ij)).comp (continuous_apply i)

/-- A single ordered marginal bounds its parent's mass by the exact demand.
This gives the compact mass box without any clique-support restriction. -/
theorem bounded_component_mass_le (N : ℕ) (ν : FiniteMeasure (V × V))
    {μs : BoundedLaws V N} (hbalance : boundedOccupation N μs = ν) (i : Fin (N - 1)) :
    (μs i).mass ≤ ν.mass := by
  let ij : PairIndex (i.val + 2) := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
    intro h
    have hval : (0 : ℕ) = 1 := congrArg Fin.val h
    omega⟩
  have hle : (μs i : Measure (Fin (i.val + 2) → V)).map
      (fun v => (v ij.val.1, v ij.val.2)) ≤
      (boundedOccupation N μs : Measure (V × V)) := by
    rw [boundedOccupation_toMeasure, boundedLaws, occupation_assemble]
    apply le_trans (pair_le_orderOccupation _ _ ij)
    exact Finset.single_le_sum
      (f := fun j : Fin (N - 1) => orderOccupation (j.val + 2)
        (μs j : Measure (Fin (j.val + 2) → V)))
      (fun _ _ => by intro s; exact bot_le) (Finset.mem_univ i)
  have hm := hle Set.univ
  rw [Measure.map_apply (continuous_tuplePair ij).measurable MeasurableSet.univ,
    Set.preimage_univ, hbalance] at hm
  exact ENNReal.toNNReal_mono (measure_ne_top _ _) hm

/-- The actual ordered-balance set is weakly compact. The clique locus need
only be measurable, because it is not used as a compactness constraint. -/
theorem isCompact_bounded_balanced (N : ℕ) (ν : FiniteMeasure (V × V)) :
    IsCompact {μs : BoundedLaws V N | boundedOccupation N μs = ν} := by
  have hbox : IsCompact {μs : BoundedLaws V N | ∀ i, (μs i).mass ≤ ν.mass} :=
    isCompact_pi_infinite (fun i : Fin (N - 1) =>
      isCompact_setOfPred_finiteMeasure_le_of_compactSpace (Fin (i.val + 2) → V) ν.mass)
  exact hbox.of_isClosed_subset
    (isClosed_eq (continuous_boundedOccupation N) continuous_const)
    (fun μs hμs i => bounded_component_mass_le N ν hμs i)

/-- Exactly balanced approximations with convergent costs yield an exactly
balanced finite-order family of that cost. Additional restrictions must be
closed, as permutation invariance is; actual clique support is derived later. -/
theorem exists_bounded_cost_limit (N : ℕ) (ν : FiniteMeasure (V × V))
    (A : Set (BoundedLaws V N)) (hA : IsClosed A)
    (μs : ℕ → BoundedLaws V N)
    (hμs : ∀ m, μs m ∈ A ∧ boundedOccupation N (μs m) = ν)
    (c : ℝ≥0) (hc : Filter.Tendsto (fun m => finiteCost (μs m)) Filter.atTop (nhds c)) :
    ∃ η ∈ A, boundedOccupation N η = ν ∧ finiteCost η = c := by
  have hk := (isCompact_bounded_balanced N ν).inter_left hA
  have hclosed := (hk.image continuous_cost).isClosed
  have hmem : c ∈ finiteCost '' (A ∩ {η | boundedOccupation N η = ν}) :=
    hclosed.mem_of_tendsto hc (Filter.Eventually.of_forall (fun m => ⟨μs m, hμs m, rfl⟩))
  obtain ⟨η, hη, heq⟩ := hmem
  exact ⟨η, hη.1, hη.2, heq⟩

/-- Coordinate permutation invariance is a closed restriction on the actual
finite family, so it can be retained in the compact limit. -/
theorem isClosed_bounded_symmetric (N : ℕ) :
    IsClosed {μs : BoundedLaws V N | ∀ i (σ : Equiv.Perm (Fin (i.val + 2))),
      (μs i).map (fun v => v ∘ σ) = μs i} := by
  apply isClosed_invariant
    (Ω := fun i : Fin (N - 1) => Fin (i.val + 2) → V)
    (J := fun i => Equiv.Perm (Fin (i.val + 2))) (fun _ σ v => v ∘ σ)
  intro i σ
  exact continuous_pi (fun j => continuous_apply (σ j))

/-- The real-valued cost interface matches expected sampled costs directly. -/
theorem exists_bounded_real_cost_limit (N : ℕ) (ν : FiniteMeasure (V × V))
    (A : Set (BoundedLaws V N)) (hA : IsClosed A)
    (μs : ℕ → BoundedLaws V N)
    (hμs : ∀ m, μs m ∈ A ∧ boundedOccupation N (μs m) = ν)
    (c : ℝ) (hc : Filter.Tendsto (fun m => (finiteCost (μs m) : ℝ))
      Filter.atTop (nhds c)) :
    ∃ η ∈ A, boundedOccupation N η = ν ∧ (finiteCost η : ℝ) = c := by
  have hk := (isCompact_bounded_balanced N ν).inter_left hA
  have hcont : Continuous (fun η : BoundedLaws V N => (finiteCost η : ℝ)) :=
    NNReal.continuous_coe.comp continuous_cost
  have hclosed := (hk.image hcont).isClosed
  have hmem : c ∈ (fun η => (finiteCost η : ℝ)) ''
      (A ∩ {η | boundedOccupation N η = ν}) :=
    hclosed.mem_of_tendsto hc (Filter.Eventually.of_forall (fun m => ⟨μs m, hμs m, rfl⟩))
  obtain ⟨η, hη, heq⟩ := hmem
  exact ⟨η, hη.1, hη.2, heq⟩

/-- Symmetric, exactly balanced actual capped laws have a symmetric physical
limit of their limiting cost. The premises concern approximating laws only;
attainment, clique support and tightness are not assumed. -/
theorem exists_symmetric_laws_cost_limit (N : ℕ) (ν : FiniteMeasure (V × V))
    (μs : ℕ → Laws V) [∀ m n, IsFiniteMeasure (μs m n)]
    (hcap : ∀ m n, n < 2 ∨ N < n → μs m n = 0)
    (hsym : ∀ m n (σ : Equiv.Perm (Fin n)), (μs m n).map (fun v => v ∘ σ) = μs m n)
    (hbalance : ∀ m, occupation (μs m) = (ν : Measure (V × V)))
    (c : ℝ) (hc : Filter.Tendsto (fun m => cost (μs m)) Filter.atTop (nhds c)) :
    ∃ μ : Laws V, (∀ n, IsFiniteMeasure (μ n)) ∧
      (∀ n, n < 2 ∨ N < n → μ n = 0) ∧
      (∀ n (σ : Equiv.Perm (Fin n)), (μ n).map (fun v => v ∘ σ) = μ n) ∧
      occupation μ = (ν : Measure (V × V)) ∧ cost μ = c := by
  let A : Set (BoundedLaws V N) := {η | ∀ i (σ : Equiv.Perm (Fin (i.val + 2))),
    (η i).map (fun v => v ∘ σ) = η i}
  have hA : IsClosed A := isClosed_bounded_symmetric N
  have happrox (m : ℕ) : restrictOrders N (μs m) ∈ A ∧
      boundedOccupation N (restrictOrders N (μs m)) = ν := by
    constructor
    · intro i σ
      apply FiniteMeasure.toMeasure_injective
      exact hsym m (i.val + 2) σ
    · apply FiniteMeasure.toMeasure_injective
      rw [boundedOccupation_restrictOrders N (μs m) (hcap m), hbalance m]
  have hcost : Filter.Tendsto (fun m => (finiteCost (restrictOrders N (μs m)) : ℝ))
      Filter.atTop (nhds c) := by
    simpa only [cost_restrictOrders N (μs _) (hcap _)] using hc
  obtain ⟨η, hη, hbalanceη, hcostη⟩ :=
    exists_bounded_real_cost_limit N ν A hA (fun m => restrictOrders N (μs m)) happrox c hcost
  refine ⟨boundedLaws N η, boundedLaws_finite N η, boundedLaws_eq_zero N η, ?_, ?_, ?_⟩
  · intro n σ
    by_cases hn : n < 2 ∨ N < n
    · simp [boundedLaws_eq_zero N η n hn]
    · let i : Fin (N - 1) := ⟨n - 2, by omega⟩
      have hi : i.val + 2 = n := by dsimp [i]; omega
      revert σ
      rw [← hi]
      intro σ
      rw [boundedLaws_apply]
      exact congrArg FiniteMeasure.toMeasure (hη i σ)
  · rw [← boundedOccupation_toMeasure, hbalanceη]
  · rw [cost_boundedLaws, hcostη]

end Compactness

end Erdos1017.PhysicalPrimal
