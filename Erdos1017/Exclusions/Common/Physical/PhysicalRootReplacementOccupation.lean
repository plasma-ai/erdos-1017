module

public import Erdos1017.Exclusions.Common.Physical.PhysicalRootReplacement
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Occupation identities of the root replacement

Under the root replacement, pair marginals away from the root are unchanged,
outgoing and incoming replaced pairs follow the independent fresh-root and
old-leaf law, and the ordered occupation changes only in the two directed root
rows, so exact ordered balance is preserved.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalRootReplacement

open PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The fresh root and the actual counted leaves have precisely the old
outgoing homogeneous graph demand. The leaf intensity is derived from balance. -/
theorem rootLaw_prod_rootLeaves (η : Laws Ω) (E : Set (Ω × Ω))
    (hE : MeasurableSet E) (hbalance : occupation η = graphDemand μ E)
    (I N : Set Ω) (hI : MeasurableSet I) (hI0 : μ I ≠ 0)
    (hrow : ∀ᵐ p ∂(μ.restrict I).prod μ, p ∈ E ↔ p.2 ∈ N) :
    (rootLaw μ I hI0 : Measure Ω).prod (rootLeaves η I) =
      (occupation η).restrict (I ×ˢ univ) := by
  rw [rootLeaves_graphDemand_homogeneous η μ E hE hbalance I N hI hrow]
  have hprod : (rootLaw μ I hI0 : Measure Ω).prod (μ I • μ.restrict N) =
      (μ.restrict I).prod (μ.restrict N) := by
    change (((μ I)⁻¹) • μ.restrict I).prod (μ I • μ.restrict N) = _
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      ENNReal.inv_mul_cancel hI0 (measure_ne_top μ I), one_smul]
  rw [hprod, hbalance, graphDemand,
    Measure.restrict_restrict (hI.prod MeasurableSet.univ), Set.inter_comm,
    ← Measure.restrict_restrict hE]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hsets : E =ᵐ[(μ.restrict I).prod μ] (univ ×ˢ N) := by
    filter_upwards [hrow] with p hp
    exact propext (by simpa using hp)
  rw [Measure.restrict_congr_set hsets, ← Measure.prod_restrict, Measure.restrict_univ]

/-- Pair marginals with neither endpoint replaced retain their full measure. -/
theorem replacedLaw_pair_away {n : ℕ} (I : Set Ω) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i a b : Fin n)
    (ha : a ≠ i) (hb : b ≠ i) :
    (replacedLaw μ I hI0 ρ i).map (fun v => (v a, v b)) =
      (rootedLaw ρ I i).map (fun v => (v a, v b)) := by
  rw [replacedLaw, Measure.map_map
    ((measurable_pi_apply a).prodMk (measurable_pi_apply b)) (measurable_replaceTuple i)]
  have heq : (fun v : Fin n → Ω => (v a, v b)) ∘ replaceTuple i =
      (fun v : Fin n → Ω => (v a, v b)) ∘ Prod.snd := by
    funext p
    simp [replaceTuple, Function.update_of_ne ha, Function.update_of_ne hb]
  rw [heq, ← Measure.map_map
    ((measurable_pi_apply a).prodMk (measurable_pi_apply b)) measurable_snd]
  congr 1
  exact (measurePreserving_snd (μ := (rootLaw μ I hI0 : Measure Ω))
    (ν := rootedLaw ρ I i)).map_eq

/-- An outgoing replaced pair has the independent fresh-root/old-leaf law. -/
theorem replacedLaw_pair_outgoing {n : ℕ} (I : Set Ω) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i j : Fin n) (hij : i ≠ j) :
    (replacedLaw μ I hI0 ρ i).map (fun v => (v i, v j)) =
      (rootLaw μ I hI0 : Measure Ω).prod ((rootedLaw ρ I i).map (fun v => v j)) := by
  rw [replacedLaw, Measure.map_map
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) (measurable_replaceTuple i)]
  have heq : (fun v : Fin n → Ω => (v i, v j)) ∘ replaceTuple i =
      Prod.map (id : Ω → Ω) (fun v : Fin n → Ω => v j) := by
    funext p
    change (replaceTuple i p i, replaceTuple i p j) = (p.1, p.2 j)
    simp [replaceTuple, Function.update_of_ne (Ne.symm hij)]
  rw [heq, coupling, ← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply j),
    Measure.map_id]

/-- The incoming replaced pair is the transpose of the outgoing pair. -/
theorem replacedLaw_pair_incoming {n : ℕ} (I : Set Ω) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i j : Fin n) (hij : i ≠ j) :
    (replacedLaw μ I hI0 ρ i).map (fun v => (v j, v i)) =
      ((rootLaw μ I hI0 : Measure Ω).prod
        ((rootedLaw ρ I i).map (fun v => v j))).map Prod.swap := by
  rw [← replacedLaw_pair_outgoing I hI0 ρ i j hij]
  exact (Measure.map_map measurable_swap
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).symm

private abbrev pairLaw {n : ℕ} (ρ : Measure (Fin n → Ω)) (ij : PairIndex n) :
    Measure (Ω × Ω) := ρ.map (fun v => (v ij.val.1, v ij.val.2))

private abbrev freshPair {n : ℕ} (I : Set Ω) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) (ij : PairIndex n) : Measure (Ω × Ω) :=
  (rootLaw μ I hI0 : Measure Ω).prod
    ((rootedLaw ρ I ij.val.1).map (fun v => v ij.val.2))

private def reversePair (n : ℕ) : PairIndex n ≃ PairIndex n where
  toFun ij := ⟨(ij.val.2, ij.val.1), Ne.symm ij.property⟩
  invFun ij := ⟨(ij.val.2, ij.val.1), Ne.symm ij.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem pairLaw_reverse {n : ℕ} (ρ : Measure (Fin n → Ω)) (ij : PairIndex n) :
    pairLaw ρ (reversePair n ij) = (pairLaw ρ ij).map Prod.swap := by
  exact (Measure.map_map measurable_swap
    ((measurable_pi_apply ij.val.1).prodMk (measurable_pi_apply ij.val.2))).symm

private theorem marked_pair_identity {n : ℕ} (I : Set Ω) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] (i : Fin n) (ij : PairIndex n) :
    pairLaw (replacedLaw μ I hI0 ρ i) ij +
        (if ij.val.1 = i then pairLaw (rootedLaw ρ I i) ij else 0) +
        (if ij.val.2 = i then pairLaw (rootedLaw ρ I i) ij else 0) =
      pairLaw (rootedLaw ρ I i) ij +
        (if ij.val.1 = i then freshPair I hI0 ρ ij else 0) +
        (if ij.val.2 = i then (freshPair I hI0 ρ (reversePair n ij)).map Prod.swap else 0) := by
  classical
  by_cases ha : ij.val.1 = i
  · have hb : ij.val.2 ≠ i := fun hb => ij.property (ha.trans hb.symm)
    simp only [ha, hb, ite_true, ite_false, add_zero]
    rw [pairLaw, ha, replacedLaw_pair_outgoing I hI0 ρ i ij.val.2 (ha ▸ ij.property)]
    have heq : freshPair I hI0 ρ ij =
        (rootLaw μ I hI0 : Measure Ω).prod
          ((rootedLaw ρ I i).map (fun v => v ij.val.2)) := by simp only [freshPair, ha]
    rw [heq, add_comm]
  · by_cases hb : ij.val.2 = i
    · simp only [ha, hb, ite_true, ite_false, add_zero]
      rw [pairLaw, hb, replacedLaw_pair_incoming I hI0 ρ i ij.val.1
        (Ne.symm (hb ▸ ij.property))]
      have heq : freshPair I hI0 ρ (reversePair n ij) =
          (rootLaw μ I hI0 : Measure Ω).prod
            ((rootedLaw ρ I i).map (fun v => v ij.val.1)) := by
        simp only [freshPair, reversePair, Equiv.coe_fn_mk, hb]
      rw [heq, add_comm]
    · simp only [ha, hb, ite_false, add_zero]
      exact replacedLaw_pair_away I hI0 ρ i _ _ ha hb

private theorem outgoingOld_eq_restrict {n : ℕ} (I : Set Ω) (hI : MeasurableSet I)
    (ρ : Measure (Fin n → Ω)) :
    (∑ ij : PairIndex n, pairLaw (rootedLaw ρ I ij.val.1) ij) =
      (orderOccupation n ρ).restrict (I ×ˢ univ) := by
  classical
  ext B hB
  rw [Measure.finsetSum_apply, Measure.restrict_apply hB, orderOccupation,
    Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Measure.map_apply ((measurable_pi_apply _).prodMk (measurable_pi_apply _)) hB,
    rootedLaw, Measure.restrict_apply
      (((measurable_pi_apply _).prodMk (measurable_pi_apply _)) hB),
    Measure.map_apply ((measurable_pi_apply _).prodMk (measurable_pi_apply _))
      (hB.inter (hI.prod MeasurableSet.univ))]
  congr 1
  ext v
  simp

private theorem freshPair_sum {n : ℕ} (I : Set Ω) (hI0 : μ I ≠ 0)
    (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ] :
    (∑ ij : PairIndex n, freshPair I hI0 ρ ij) =
      (rootLaw μ I hI0 : Measure Ω).prod (orderRootLeaves n ρ I) := by
  classical
  conv_rhs => rw [orderRootLeaves, ← Measure.sum_fintype]
  rw [Measure.prod_sum_right, Measure.sum_fintype]
  rfl

private theorem incomingOld_eq_swap {n : ℕ} (I : Set Ω)
    (ρ : Measure (Fin n → Ω)) :
    (∑ ij : PairIndex n, pairLaw (rootedLaw ρ I ij.val.2) ij) =
      (∑ ij : PairIndex n, pairLaw (rootedLaw ρ I ij.val.1) ij).map Prod.swap := by
  classical
  rw [Measure.map_finset_sum measurable_swap.aemeasurable]
  have h := (reversePair n).sum_comp
    (fun ij : PairIndex n => pairLaw (rootedLaw ρ I ij.val.1) ij)
  have hm := congrArg (fun ν : Measure (Ω × Ω) => ν.map Prod.swap) h
  simp only [Measure.map_finset_sum measurable_swap.aemeasurable] at hm
  rw [← hm]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← pairLaw_reverse]
  rfl

/-- The ordered occupation changes only in the two directed root rows.
This additive identity avoids subtraction of arbitrary measures. -/
theorem replacedAllLaw_occupation_identity {n : ℕ} (I : Set Ω) (hI : MeasurableSet I)
    (hI0 : μ I ≠ 0) (ρ : Measure (Fin n → Ω)) [IsFiniteMeasure ρ]
    (hunique : ∀ᵐ v ∂ρ, ∀ i j, v i ∈ I → v j ∈ I → i = j) :
    orderOccupation n (replacedAllLaw μ I hI0 ρ) +
        (orderOccupation n ρ).restrict (I ×ˢ univ) +
        ((orderOccupation n ρ).restrict (I ×ˢ univ)).map Prod.swap =
      orderOccupation n ρ +
        (rootLaw μ I hI0 : Measure Ω).prod (orderRootLeaves n ρ I) +
        ((rootLaw μ I hI0 : Measure Ω).prod (orderRootLeaves n ρ I)).map Prod.swap := by
  classical
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun i _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (PairIndex n))) rfl
      (fun ij _ => marked_pair_identity I hI0 ρ i ij))
  simp only [Finset.sum_add_distrib] at hsum
  have ho : (∑ i : Fin n, ∑ ij : PairIndex n,
      if ij.val.1 = i then pairLaw (rootedLaw ρ I i) ij else 0) =
      (orderOccupation n ρ).restrict (I ×ˢ univ) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact outgoingOld_eq_restrict I hI ρ
  have hi : (∑ i : Fin n, ∑ ij : PairIndex n,
      if ij.val.2 = i then pairLaw (rootedLaw ρ I i) ij else 0) =
      ((orderOccupation n ρ).restrict (I ×ˢ univ)).map Prod.swap := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [incomingOld_eq_swap, outgoingOld_eq_restrict I hI ρ]
  have hfo : (∑ i : Fin n, ∑ ij : PairIndex n,
      if ij.val.1 = i then freshPair I hI0 ρ ij else 0) =
      (rootLaw μ I hI0 : Measure Ω).prod (orderRootLeaves n ρ I) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact freshPair_sum I hI0 ρ
  have hfi : (∑ i : Fin n, ∑ ij : PairIndex n,
      if ij.val.2 = i then (freshPair I hI0 ρ (reversePair n ij)).map Prod.swap else 0) =
      ((rootLaw μ I hI0 : Measure Ω).prod (orderRootLeaves n ρ I)).map Prod.swap := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← Measure.map_finset_sum measurable_swap.aemeasurable,
      (reversePair n).sum_comp, freshPair_sum I hI0 ρ]
  rw [ho, hi, hfo, hfi] at hsum
  have hdecomp := congrArg (orderOccupation n) (rootedLaw_decomposition I hI ρ hunique)
  rw [orderOccupation_add, orderOccupation_finsetSum] at hdecomp
  rw [replacedAllLaw, orderOccupation_add, orderOccupation_finsetSum]
  change (∑ i, orderOccupation n (replacedLaw μ I hI0 ρ i)) + _ + _ =
    (∑ i, orderOccupation n (rootedLaw ρ I i)) + _ + _ at hsum
  have h := congrArg (fun ν : Measure (Ω × Ω) => orderOccupation n (noRootLaw ρ I) + ν) hsum
  simp only [← add_assoc] at h
  rw [hdecomp] at h
  exact h

/-- Across every original order, replacement exchanges exactly the actual
outgoing root occupation and its transpose with the independent products. -/
theorem replacedLaws_occupation_identity (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (I : Set Ω) (hI : MeasurableSet I) (hI0 : μ I ≠ 0)
    (hunique : ∀ n, ∀ᵐ v ∂η n, ∀ i j, v i ∈ I → v j ∈ I → i = j) :
    occupation (replacedLaws μ I hI0 η) + (occupation η).restrict (I ×ˢ univ) +
        ((occupation η).restrict (I ×ˢ univ)).map Prod.swap =
      occupation η + (rootLaw μ I hI0 : Measure Ω).prod (rootLeaves η I) +
        ((rootLaw μ I hI0 : Measure Ω).prod (rootLeaves η I)).map Prod.swap := by
  let : ∀ n, IsFiniteMeasure (orderRootLeaves n (η n) I) := fun n => by
    unfold orderRootLeaves
    infer_instance
  have h := congrArg Measure.sum (funext (fun n =>
    replacedAllLaw_occupation_identity I hI hI0 (η n) (hunique n)))
  simp only [← Measure.sum_add_sum] at h
  simp only [occupation, replacedLaws, rootLeaves,
    Measure.restrict_sum _ (hI.prod MeasurableSet.univ),
    Measure.map_sum measurable_swap.aemeasurable, Measure.prod_sum_right]
  exact h

/-- Exact ordered balance is preserved by the genuine whole-family root
replacement. Unique roots and the leaf intensity are both derived from the
original graph balance and the supplied independent homogeneous class. -/
theorem occupation_replacedLaws (η : Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (E : Set (Ω × Ω)) (hE : MeasurableSet E)
    (hbalance : occupation η = graphDemand μ E)
    (I N : Set Ω) (hI : MeasurableSet I) (hI0 : μ I ≠ 0)
    (hindependent : (μ.prod μ) (E ∩ (I ×ˢ I)) = 0)
    (hrow : ∀ᵐ p ∂(μ.restrict I).prod μ, p ∈ E ↔ p.2 ∈ N) :
    occupation (replacedLaws μ I hI0 η) = graphDemand μ E := by
  have hunique := ae_at_most_one_root_graphDemand η μ E hbalance I hI hindependent
  have h := replacedLaws_occupation_identity η I hI hI0 hunique
  rw [rootLaw_prod_rootLeaves η E hE hbalance I N hI hI0 hrow] at h
  have : IsFiniteMeasure ((occupation η).restrict (I ×ˢ univ)) := by
    rw [hbalance]
    unfold graphDemand
    infer_instance
  have heq : occupation (replacedLaws μ I hI0 η) = occupation η := by
    apply (Measure.add_left_inj
      (((occupation η).restrict (I ×ˢ univ)).map Prod.swap) _ _).mp at h
    exact (Measure.add_left_inj ((occupation η).restrict (I ×ˢ univ)) _ _).mp h
  exact heq.trans hbalance

end Erdos1017.PhysicalRootReplacement
