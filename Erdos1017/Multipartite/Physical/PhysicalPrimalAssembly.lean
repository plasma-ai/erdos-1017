module

public import Erdos1017.Multipartite.Physical.PhysicalPrimalDuality

/-!
# Assembling tuple laws into an all-orders family

A single tuple law is placed at its order in the unrestricted family, and
assembling such laws preserves occupation, cost, support and pair balance,
including mixtures of sampled laws with order-two repair laws
(`feasible_assemble`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- Place one genuine tuple law at its actual order in the unrestricted family. -/
def singleOrder (k : ℕ) (ρ : Measure (Fin k → V)) : Laws V :=
  fun n => if h : k = n then h ▸ ρ else 0

@[simp] theorem singleOrder_self (k : ℕ) (ρ : Measure (Fin k → V)) :
    singleOrder k ρ k = ρ := by simp [singleOrder]

@[simp] theorem singleOrder_ne (k n : ℕ) (ρ : Measure (Fin k → V)) (h : k ≠ n) :
    singleOrder k ρ n = 0 := by simp [singleOrder, h]

@[simp] theorem orderOccupation_zero (n : ℕ) :
    orderOccupation n (0 : Measure (Fin n → V)) = 0 := by
  simp [orderOccupation]

/-- Reindexing a tuple law by its order preserves its complete pair occupation. -/
theorem occupation_singleOrder (k : ℕ) (ρ : Measure (Fin k → V)) :
    occupation (singleOrder k ρ) = orderOccupation k ρ := by
  have h (n : ℕ) : orderOccupation n (singleOrder k ρ n) =
      if n = k then orderOccupation k ρ else 0 := by
    by_cases hn : n = k
    · subst n
      simp
    · simp [singleOrder_ne k n ρ (Ne.symm hn), hn]
  unfold occupation
  simp_rw [h]
  ext s hs
  simp [Measure.sum_apply _ hs, apply_ite, ite_apply]

/-- Reindexing preserves parent mass exactly. -/
theorem cost_singleOrder (k : ℕ) (ρ : Measure (Fin k → V)) :
    cost (singleOrder k ρ) = ρ.real Set.univ := by
  unfold cost
  rw [tsum_eq_single k]
  · simp
  · intro n hn
    simp [singleOrder_ne k n ρ (Ne.symm hn)]

/-- Occupation is additive in arbitrary parent laws. -/
theorem orderOccupation_add (n : ℕ) (μ ν : Measure (Fin n → V)) :
    orderOccupation n (μ + ν) = orderOccupation n μ + orderOccupation n ν := by
  classical
  unfold orderOccupation
  simp_rw [Measure.map_add _ _
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))]
  exact Finset.sum_add_distrib

/-- The unrestricted occupation respects finite assembly of different laws. -/
theorem occupation_add (μ ν : Laws V) :
    occupation (fun n => μ n + ν n) = occupation μ + occupation ν := by
  simp only [occupation, orderOccupation_add, ← Measure.sum_add_sum]

/-- Ordered coordinate occupation written with explicit diagonal exclusion. -/
theorem orderOccupation_eq_sum (n : ℕ) (ρ : Measure (Fin n → V)) :
    orderOccupation n ρ = ∑ i, ∑ j, if i ≠ j then
      ρ.map (fun v => (v i, v j)) else 0 := by
  classical
  unfold orderOccupation
  rw [← Fintype.sum_prod_type (fun ij : Fin n × Fin n =>
    if ij.1 ≠ ij.2 then ρ.map (fun v => (v ij.1, v ij.2)) else 0), ← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
    (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2))
    (by simp) (fun ij => ρ.map (fun v => (v ij.1, v ij.2)))).symm

/-- Additive occupation respects a finite sum at each order. -/
theorem orderOccupation_finsetSum {I : Type*} (s : Finset I) (n : ℕ)
    (μ : I → Measure (Fin n → V)) :
    orderOccupation n (∑ i ∈ s, μ i) = ∑ i ∈ s, orderOccupation n (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, orderOccupation_add, ih]

theorem occupation_sum {I : Type*} [Fintype I] (μ : I → Laws V) :
    occupation (fun n => ∑ i, μ i n) = ∑ i, occupation (μ i) := by
  unfold occupation
  simp_rw [orderOccupation_finsetSum, ← Measure.sum_fintype]
  exact Measure.sum_comm _

/-- Assemble a finite family of genuine tuple laws at their possibly different
orders. This retains every joint law, rather than replacing it by a product law. -/
def assemble {I : Type*} [Fintype I] (k : I → ℕ)
    (ρ : ∀ i, Measure (Fin (k i) → V)) : Laws V :=
  fun n => ∑ i, singleOrder (k i) (ρ i) n

theorem occupation_assemble {I : Type*} [Fintype I] (k : I → ℕ)
    (ρ : ∀ i, Measure (Fin (k i) → V)) :
    occupation (assemble k ρ) = ∑ i, orderOccupation (k i) (ρ i) := by
  unfold assemble
  rw [occupation_sum]
  simp_rw [occupation_singleOrder]

theorem singleOrder_finite (k n : ℕ) (ρ : Measure (Fin k → V)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (singleOrder k ρ n) := by
  by_cases h : k = n
  · subst n
    simpa using (inferInstance : IsFiniteMeasure ρ)
  · rw [singleOrder_ne k n ρ h]
    infer_instance

theorem assemble_finite {I : Type*} [Fintype I] (k : I → ℕ)
    (ρ : ∀ i, Measure (Fin (k i) → V)) [∀ i, IsFiniteMeasure (ρ i)] (n : ℕ) :
    IsFiniteMeasure (assemble k ρ n) := by
  have (i : I) : IsFiniteMeasure (singleOrder (k i) (ρ i) n) := singleOrder_finite _ _ _
  unfold assemble
  infer_instance

/-- Parent costs add exactly when finite tuple laws are assembled. -/
theorem cost_assemble {I : Type*} [Fintype I] (k : I → ℕ)
    (ρ : ∀ i, Measure (Fin (k i) → V)) [∀ i, IsFiniteMeasure (ρ i)] :
    cost (assemble k ρ) = ∑ i, (ρ i).real Set.univ := by
  classical
  have hf (i : I) (n : ℕ) : IsFiniteMeasure (singleOrder (k i) (ρ i) n) :=
    singleOrder_finite _ _ _
  have hr (n : ℕ) : (assemble k ρ n).real Set.univ =
      ∑ i, (singleOrder (k i) (ρ i) n).real Set.univ := by
    simp only [assemble, measureReal_def, Measure.finsetSum_apply]
    exact ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)
  have hs (i : I) : Summable (fun n => (singleOrder (k i) (ρ i) n).real Set.univ) := by
    apply summable_of_ne_finset_zero (s := {k i})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [singleOrder_ne (k i) n (ρ i) (Ne.symm hn)]
  unfold cost
  simp_rw [hr]
  rw [Summable.tsum_finsetSum (fun i _ => hs i)]
  exact Finset.sum_congr rfl (fun i _ => cost_singleOrder (k i) (ρ i))

@[simp] theorem singleOrder_zero (k n : ℕ) :
    singleOrder k (0 : Measure (Fin k → V)) n = 0 := by
  unfold singleOrder
  split_ifs with h
  · subst n
    rfl
  · rfl

/-- Actual support and pair balance survive assembly, including mixtures of
sampled laws with order-two repair laws. -/
theorem feasible_assemble {I : Type*} [Fintype I] (k : I → ℕ)
    (ρ : ∀ i, Measure (Fin (k i) → V)) (A : V → V → Prop) (demand : Measure (V × V))
    (hsmall : ∀ i, k i ≤ 1 → ρ i = 0)
    (hclique : ∀ i, ∀ᵐ v ∂ρ i, ∀ a b, a ≠ b → A (v a) (v b))
    (hbalance : (∑ i, orderOccupation (k i) (ρ i)) = demand) :
    Feasible A demand (assemble k ρ) := by
  classical
  have hzero (n : ℕ) (hn : n ≤ 1) : assemble k ρ n = 0 := by
    unfold assemble
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : k i = n
    · rw [hsmall i (h ▸ hn)]
      exact singleOrder_zero _ _
    · exact singleOrder_ne _ _ _ h
  refine ⟨hzero 0 (by decide), hzero 1 le_rfl, ?_, ?_⟩
  · intro n
    unfold assemble
    rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro i
    by_cases h : k i = n
    · subst n
      simpa only [singleOrder_self] using hclique i
    · simp [singleOrder_ne _ _ _ h]
  · rw [occupation_assemble, hbalance]

end Erdos1017.PhysicalPrimal
