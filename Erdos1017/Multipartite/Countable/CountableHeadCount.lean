module

public import Erdos1017.Multipartite.Countable.CountableRepeatWitnesses

/-!
# Finite head count from repeat witnesses

Distinct positive heads cannot share a maximizing dust count under the strict
pair and multiplier bounds, so repeat witnesses bound the number of positive
heads even when the support was countably infinite; in the dust-free supported
model at most one secondary head can be positive.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- The actual anchored clique with two heads and any dust count. -/
theorem anchored_head_pair_dust_test {D : Coefficients} (hD : D ∈ feasible)
    (i j : ℕ) (hij : i ≠ j) (k : ℕ) :
    head D i + head D j + MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) +
      (k : ℝ) * (linear D - incident D i - incident D j) -
      penalty D * k * ((k : ℝ) - 1) / 2 ≤ 1 := by
  let n := max i j + 1
  have hi : i < n := by dsimp [n]; omega
  have hj : j < n := by dsimp [n]; omega
  let X : Selector.Selection n := fun l => decide (l = ⟨j, hj⟩)
  have habsent : X ⟨i, hi⟩ = false := by simp [X, Fin.ext_iff, hij]
  let S : RepeatContext i := ⟨n, hi, X, habsent, k⟩
  have hrow : S.row D = head D i +
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) - (k : ℝ) * incident D i := by
    have hk : (DustCellRestriction.headDual (restrict n D)).beta ⟨i, hi⟩ ⟨j, hj⟩ =
        MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) :=
      (MultipartiteCountableMeasure.kernel_embed D n
        (.inl (some ⟨i, hi⟩)) (.inl (some ⟨j, hj⟩))).symm
    simp [RepeatContext.row, S, X, Selector.bit, hk, MultipartiteDust.head,
      MultipartiteDust.incident, restrict]
  have hcharge : S.charge D = head D j + (k : ℝ) * (linear D - incident D j) -
      penalty D * k * ((k : ℝ) - 1) / 2 := by
    simp [RepeatContext.charge, S, X, MultipartiteDust.charge, Selector.bit,
      MultipartiteDust.head, MultipartiteDust.incident, MultipartiteDust.linear,
      MultipartiteDust.penalty, restrict, head, incident, linear, penalty]
  have h := S.one_test hD
  rw [hrow, hcharge] at h
  nlinarith

/-- A dust witness's two-copy threshold is at most its one-copy row. -/
theorem dustThreshold_le_row {D : Coefficients} (hD : D ∈ feasible) (i k : ℕ) :
    dustThreshold D i k ≤ head D i - (k : ℝ) * incident D i := by
  have h := (dustContext i k).one_test hD
  simp only [RepeatContext.row, RepeatContext.charge, dustContext, MultipartiteDust.charge,
    Selector.bit, Bool.false_eq_true, ↓reduceIte, mul_zero, Finset.sum_const_zero, add_zero,
    sub_zero, MultipartiteDust.head, MultipartiteDust.incident, MultipartiteDust.linear,
    MultipartiteDust.penalty, restrict] at h
  unfold dustThreshold
  simp only [zero_add] at h
  change head D i - (k : ℝ) * incident D i +
    ((k : ℝ) * linear D - penalty D * k * ((k : ℝ) - 1) / 2) ≤ 1 at h
  nlinarith

/-- Every actual witness lies below the strict counting cutoff. -/
theorem dust_witness_bound {D : Coefficients} (hD : D ∈ feasible)
    (ℓ g : ℝ) (hg : 0 < g) (i k : ℕ) (hti : head D i < 1) (hci : g ≤ incident D i)
    (hK : ℓ ≤ twoRepeatPenalty D i) (hwitness : twoRepeatPenalty D i = dustThreshold D i k) :
    (k : ℝ) < (1 - ℓ) / g := by
  have hrow := dustThreshold_le_row hD i k
  rw [← hwitness] at hrow
  have hinc := mul_le_mul_of_nonneg_left hci (Nat.cast_nonneg k)
  apply (lt_div_iff₀ hg).mpr
  nlinarith

/-- Distinct positive heads cannot share a maximizing dust count once the
actual strict pair and multiplier bounds hold. -/
theorem dust_witness_injective {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (ℓ : ℝ)
    (hK : ∀ i, 0 < p i → ℓ ≤ twoRepeatPenalty D i)
    (hpair : ∀ i j, i ≠ j → 0 < p i → 0 < p j →
      -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) ≤ ℓ)
    (hstrict : ∀ i j, i ≠ j → 0 < p i → 0 < p j →
      -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) <
        min (twoRepeatPenalty D i) (twoRepeatPenalty D j))
    (f : {i // 0 < p i} → ℕ) (hf : ∀ i, twoRepeatPenalty D i.val = dustThreshold D i.val (f i)) :
    Function.Injective f := by
  intro i j hijcount
  apply Subtype.ext
  by_contra hij
  have htest := anchored_head_pair_dust_test hD i.val j.val hij (f i)
  have hKi := hK i.val i.property
  have hKj := hK j.val j.property
  have hc := hpair i.val j.val hij i.property j.property
  have hstricti := (hstrict i.val j.val hij i.property j.property).trans_le (min_le_left _ _)
  have hwi := hf i
  have hwj := hf j
  rw [← hijcount] at hwj
  unfold dustThreshold at hwi hwj
  nlinarith

/-- Actual repeat witnesses give a finite bound even when the original
positive head support was countably infinite. -/
theorem positive_head_count_le {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hzero : ∀ i, p i = 0 → head D i = 0 ∧ incident D i = 0 ∧
      ∀ j, pair D i j = 0 ∧ pair D j i = 0)
    (ℓ g : ℝ) (hℓ : 1 / 2 < ℓ) (hg : 0 < g)
    (ht : ∀ i, 0 < p i → head D i < 1)
    (hK : ∀ i, 0 < p i → ℓ ≤ twoRepeatPenalty D i)
    (hpair : ∀ i j, i ≠ j → 0 < p i → 0 < p j →
      -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) ≤ ℓ)
    (hstrict : ∀ i j, i ≠ j → 0 < p i → 0 < p j →
      -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) <
        min (twoRepeatPenalty D i) (twoRepeatPenalty D j))
    (hci : ∀ i, 0 < p i → g ≤ incident D i) (hpen : g ≤ penalty D) :
    Finite {i // 0 < p i} ∧ Nat.card {i // 0 < p i} ≤ ⌈(1 - ℓ) / g⌉₊ := by
  have hhead (i : ℕ) (hi : 0 < p i) : ℓ ≤ head D i := (hK i hi).trans (twoRepeatPenalty_le_head hD i)
  have hex (i : {i // 0 < p i}) : ∃ k, twoRepeatPenalty D i.val = dustThreshold D i.val k := by
    obtain ⟨k, hk, _⟩ := exists_dust_witness hD p hp hzero ℓ hℓ hhead (hg.trans_le hpen)
      i.val (ht i.val i.property) (hK i.val i.property)
    exact ⟨k, hk⟩
  choose f hf using hex
  have hfinj := dust_witness_injective hD p ℓ hK hpair hstrict f hf
  have hbound (i : {i // 0 < p i}) : (f i : ℝ) < (1 - ℓ) / g :=
    dust_witness_bound hD ℓ g hg i.val (f i) (ht i.val i.property) (hci i.val i.property)
      (hK i.val i.property) (hf i)
  let F : {i // 0 < p i} → Fin ⌈(1 - ℓ) / g⌉₊ := fun i => ⟨f i, Nat.lt_ceil.mpr (hbound i)⟩
  have hF : Function.Injective F := fun i j hij => hfinj (congrArg Fin.val hij)
  have hfinite : Finite {i // 0 < p i} := Finite.of_injective F hF
  refine ⟨hfinite, ?_⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective F hF

/-- In the dust-free supported model the sole witness count is zero, so
at most one independent secondary head can be positive. -/
theorem positive_heads_unique_of_zero_dust {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hzero : ∀ i, p i = 0 → head D i = 0 ∧ incident D i = 0 ∧
      ∀ j, pair D i j = 0 ∧ pair D j i = 0)
    (ℓ : ℝ) (hℓ : 1 / 2 < ℓ)
    (ht : ∀ i, 0 < p i → head D i < 1) (hK : ∀ i, 0 < p i → ℓ ≤ twoRepeatPenalty D i)
    (hpair : ∀ i j, i ≠ j → 0 < p i → 0 < p j →
      -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) ≤ ℓ)
    (hstrict : ∀ i j, i ≠ j → 0 < p i → 0 < p j →
      -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) <
        min (twoRepeatPenalty D i) (twoRepeatPenalty D j))
    (hv : linear D = 0) (hc : ∀ j, incident D j = 0) (hpD : penalty D = 0)
    (i j : ℕ) (hi : 0 < p i) (hj : 0 < p j) : i = j := by
  have hhead (k : ℕ) (hk : 0 < p k) : ℓ ≤ head D k := (hK k hk).trans (twoRepeatPenalty_le_head hD k)
  have hwitness (k : {k // 0 < p k}) : twoRepeatPenalty D k.val = dustThreshold D k.val 0 :=
    twoRepeatPenalty_eq_zero_dust_threshold hD p hp hzero ℓ hℓ hhead hv hc hpD
      k.val (ht k.val k.property) (hK k.val k.property)
  have hinj := dust_witness_injective hD p ℓ hK hpair hstrict (fun _ => 0) hwitness
  have h := hinj (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) rfl
  exact congrArg Subtype.val h

end Erdos1017.MultipartiteCountableDual
