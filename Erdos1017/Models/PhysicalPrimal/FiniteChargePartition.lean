module

public import Erdos1017.Models.PhysicalPrimal.FiniteProductSampling

/-!
# Pair charges on partitioned vertex sets

`pairCharge` is half the ordered-pair charge, recovering the usual charge on
unordered edges; the sampled bin charge equals the charge on the disjoint union,
and restoring discarded vertices costs at most one internal charge plus one unit
per cross pair.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FiniteArity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Half the ordered-pair charge; zero diagonal and symmetry recover the
usual charge on unordered edges. -/
def pairCharge (U : Finset α) (y : α → α → ℝ) : ℝ := crossSum U U y / 2

theorem subset_pairCharge_moment (U : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (y : α → α → ℝ) (hy : ∀ a, y a a = 0) :
    (∑ S, subsetWeight U k S * pairCharge S y) =
      ((k.choose 2 : ℝ) / U.card.choose 2) * pairCharge U y := by
  unfold pairCharge
  simp only [mul_div, ← Finset.sum_div]
  congr 1
  simp only [crossSum_bit, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · subst b
    simp [hy]
  · have hm := subset_pair_moment U k hk a b hab
    calc
      _ = y a b * (∑ S, subsetWeight U k S * (subsetBit S a * subsetBit S b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        ring
      _ = _ := by rw [hm]; ring

theorem subset_average_pairCharge (U : Finset α) (hU : 2 ≤ U.card)
    (y : α → α → ℝ) (hy : ∀ a, y a a = 0) :
    subsetAverage U 2 (fun S => pairCharge S y) = pairCharge U y / U.card.choose 2 := by
  have hm := subset_pairCharge_moment U 2 hU y hy
  rw [subset_expectation] at hm
  simpa [subsetAverage, div_eq_inv_mul] using hm

theorem pairCharge_eq_sum_pairs (U : Finset α) (y : α → α → ℝ) (hy : ∀ a, y a a = 0) :
    pairCharge U y = ∑ t ∈ U.powersetCard 2, pairCharge t y := by
  by_cases hU : 2 ≤ U.card
  · have hm := subset_average_pairCharge U hU y hy
    have hc : (U.card.choose 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hU).ne'
    unfold subsetAverage at hm
    field_simp at hm
    exact hm.symm
  · have hcard : U.card ≤ 1 := by omega
    have hempty : U.powersetCard 2 = ∅ := Finset.powersetCard_eq_empty.mpr (by omega)
    rw [hempty, Finset.sum_empty]
    unfold pairCharge crossSum
    have hzero : (∑ a ∈ U, ∑ b ∈ U, y a b) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro b hb
      rw [(Finset.card_le_one.mp hcard) a ha b hb, hy]
    rw [hzero, zero_div]

/-- The sampled bin charge is exactly the actual charge on the disjoint union. -/
theorem binCharge_eq_union {m : ℕ} (U : Fin m → Finset α)
    (hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) U)
    (y : α → α → ℝ) (hy : ∀ a, y a a = 0) :
    binCharge (fun _ S => pairCharge S y) (fun _ _ => y) U =
      pairCharge (Finset.univ.biUnion U) y := by
  have hfull : crossSum (Finset.univ.biUnion U) (Finset.univ.biUnion U) y =
      ∑ i, ∑ j, crossSum (U i) (U j) y := by
    unfold crossSum
    rw [Finset.sum_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [Finset.sum_biUnion hdisj]
    rw [Finset.sum_comm]
  have hsplit : (∑ i, ∑ j, crossSum (U i) (U j) y) =
      (∑ i, crossSum (U i) (U i) y) +
      ∑ i, ∑ j, if i = j then 0 else crossSum (U i) (U j) y := by
    have hpoint (i j : Fin m) : crossSum (U i) (U j) y =
        (if i = j then crossSum (U i) (U i) y else 0) +
        (if i = j then 0 else crossSum (U i) (U j) y) := by
      by_cases hij : i = j <;> simp [hij]
    calc
      _ = ∑ i, ∑ j, ((if i = j then crossSum (U i) (U i) y else 0) +
          (if i = j then 0 else crossSum (U i) (U j) y)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hpoint i j
      _ = _ := by simp [Finset.sum_add_distrib]
  unfold binCharge
  simp_rw [← pairCharge_eq_sum_pairs _ y hy]
  simp only [pairCharge, ← Finset.sum_div]
  rw [hfull, hsplit, add_div]

omit [Fintype α] in
theorem pairCharge_union (S T : Finset α) (hdisj : Disjoint S T) (y : α → α → ℝ) :
    pairCharge (S ∪ T) y = pairCharge S y + pairCharge T y +
      (crossSum S T y + crossSum T S y) / 2 := by
  unfold pairCharge crossSum
  simp_rw [Finset.sum_union hdisj, Finset.sum_add_distrib]
  ring

omit [Fintype α] [DecidableEq α] in
theorem crossSum_le_card (S T : Finset α) (y : α → α → ℝ)
    (hy : ∀ a ∈ S, ∀ b ∈ T, y a b ≤ 1) :
    crossSum S T y ≤ (S.card : ℝ) * T.card := by
  unfold crossSum
  calc
    (∑ a ∈ S, ∑ b ∈ T, y a b) ≤ ∑ _ ∈ S, ∑ _ ∈ T, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum (fun b hb => hy a ha b hb)
    _ = (S.card : ℝ) * T.card := by simp

omit [Fintype α] in
/-- Restoring the discarded vertices incurs at most one internal charge and
one unit for each cross pair. -/
theorem discarded_charge_bound (D R : Finset α) (hdisj : Disjoint D R)
    (y : α → α → ℝ) (hy : ∀ a b, y a b ≤ 1) (L n δ : ℝ)
    (hD : (D.card : ℝ) ≤ L) (hR : (R.card : ℝ) = n)
    (hsmall : pairCharge D y ≤ 1)
    (hretained : pairCharge R y ≤ 3 * n / 2 - δ * n ^ 2 / 2) :
    pairCharge (D ∪ R) y ≤ 1 + (L + 3 / 2) * n - δ * n ^ 2 / 2 := by
  have hcross := crossSum_le_card D R y (fun a _ b _ => hy a b)
  have hcross' := crossSum_le_card R D y (fun a _ b _ => hy a b)
  have hn : 0 ≤ n := hR ▸ Nat.cast_nonneg R.card
  have hsize := mul_le_mul_of_nonneg_right hD hn
  rw [hR] at hcross hcross'
  rw [pairCharge_union D R hdisj]
  nlinarith

omit [Fintype α] in
theorem pairCharge_pair (a b : α) (hab : a ≠ b) (y : α → α → ℝ)
    (hy : ∀ x, y x x = 0) : pairCharge {a, b} y = (y a b + y b a) / 2 := by
  simp [pairCharge, crossSum, hab, hy]

omit [Fintype α] in
theorem subsetAverage_pairCharge_lower (U : Finset α) (hU : 2 ≤ U.card)
    (y : α → α → ℝ) (hy : ∀ a, y a a = 0) (c : ℝ)
    (hlower : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → c ≤ y a b) :
    c ≤ subsetAverage U 2 (fun S => pairCharge S y) := by
  have hc : (0 : ℝ) < U.card.choose 2 := by exact_mod_cast Nat.choose_pos hU
  unfold subsetAverage
  apply (le_div_iff₀ hc).mpr
  calc
    c * (U.card.choose 2 : ℝ) = ∑ _ ∈ U.powersetCard 2, c := by simp [mul_comm]
    _ ≤ ∑ S ∈ U.powersetCard 2, pairCharge S y := by
      apply Finset.sum_le_sum
      intro S hS
      obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hS).2
      subst S
      have ha : a ∈ U := (Finset.mem_powersetCard.mp hS).1 (by simp)
      have hb : b ∈ U := (Finset.mem_powersetCard.mp hS).1 (by simp)
      rw [pairCharge_pair a b hab y hy]
      have h1 := hlower a ha b hb hab
      have h2 := hlower b hb a ha hab.symm
      linarith

omit [Fintype α] [DecidableEq α] in
theorem subsetAverage_singleton_sum (U : Finset α) (f : α → ℝ) :
    subsetAverage U 1 (fun S => ∑ a ∈ S, f a) = (∑ a ∈ U, f a) / U.card := by
  simp [subsetAverage, Finset.powersetCard_one]

omit [Fintype α] [DecidableEq α] in
theorem pairCharge_map {β : Type*} [DecidableEq β] (U : Finset α) (e : α ↪ β)
    (y : β → β → ℝ) :
    pairCharge (U.map e) y = pairCharge U (fun a b => y (e a) (e b)) := by
  simp [pairCharge, crossSum, Finset.sum_map]

end Erdos1017.FiniteArity
