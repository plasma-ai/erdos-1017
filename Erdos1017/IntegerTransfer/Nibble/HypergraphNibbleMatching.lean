module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleVariance

/-!
# The retained matching of one nibble round

The sampled edges meeting no other sampled edge form the retained matching of a
round, which is disjoint from the residual; its expected size is computed
exactly and has the expected first-order size with an explicit second-order loss
(`retained_count_expectation_lower`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sampled edges having no other sampled edge meeting them form the retained matching. -/
def retained (H : Finset (Finset V)) (X : Finset V → Bool) : Finset (Finset V) :=
  H.filter (fun e => X e = true ∧ ∀ f ∈ (incident H e).erase e, X f = false)

theorem retained_pairwise_disjoint (H : Finset (Finset V)) (X : Finset V → Bool) :
    (retained H X : Set (Finset V)).PairwiseDisjoint id := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  have hinc : f ∈ incident H e := Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hf).1, ⟨v, Finset.mem_inter.mpr ⟨hvf, hve⟩⟩⟩
  have hfalse := (Finset.mem_filter.mp he).2.2 f (Finset.mem_erase.mpr ⟨Ne.symm hef, hinc⟩)
  have htrue := (Finset.mem_filter.mp hf).2.1
  simp_all

theorem retained_disjoint_residual (H : Finset (Finset V)) (X : Finset V → Bool)
    (e f : Finset V) (he : e ∈ retained H X) (hf : f ∈ residual H X) : Disjoint e f := by
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  have hinc : e ∈ incident H f := Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp he).1, ⟨v, Finset.mem_inter.mpr ⟨hve, hvf⟩⟩⟩
  have hfalse := (Finset.mem_filter.mp hf).2 e hinc
  have htrue := (Finset.mem_filter.mp he).2.1
  simp_all

private theorem product_moment {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (h : α → Bool → ℝ) (A : Finset α) :
    (∑ X, CliqueSampling.weight p X * ∏ e ∈ A, h e (X e)) =
      ∏ e ∈ A, ((1 - p e) * h e false + p e * h e true) := by
  have hm := CliqueSampling.bernoulli_product_expectation p
    (fun e b => if e ∈ A then h e b else 1)
  have hfactor (e : α) :
      (1 - p e) * (if e ∈ A then h e false else 1) +
        p e * (if e ∈ A then h e true else 1) =
      if e ∈ A then (1 - p e) * h e false + p e * h e true else 1 := by
    by_cases he : e ∈ A <;> simp [he]
  simp only [hfactor, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.prod_const_one, mul_one] at hm
  exact hm

private theorem isolated_indicator (H : Finset (Finset V)) (X : Finset V → Bool)
    (e : Finset V) (he : e ∈ H) :
    (if e ∈ retained H X then (1 : ℝ) else 0) =
      ∏ f ∈ insert e ((incident H e).erase e),
        (if f = e then Selector.bit (X f) else if X f then 0 else 1) := by
  classical
  rw [Finset.prod_insert (Finset.notMem_erase _ _)]
  simp only [↓reduceIte]
  by_cases hkeep : e ∈ retained H X
  · have hx := (Finset.mem_filter.mp hkeep).2.1
    have hall := (Finset.mem_filter.mp hkeep).2.2
    rw [ite_eq_left hkeep]
    have hprod : (∏ f ∈ (incident H e).erase e,
        if f = e then Selector.bit (X f) else if X f then (0 : ℝ) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro f hf
      simp [(Finset.mem_erase.mp hf).1, hall f hf]
    rw [hprod]
    simp [hx, Selector.bit]
  · rw [ite_eq_right hkeep]
    by_cases hx : X e = true
    · have hnot : ¬∀ f ∈ (incident H e).erase e, X f = false := by
        intro hall
        exact hkeep (Finset.mem_filter.mpr ⟨he, hx, hall⟩)
      push Not at hnot
      obtain ⟨f, hf, hxf⟩ := hnot
      have hz : (∏ f ∈ (incident H e).erase e,
          if f = e then Selector.bit (X f) else if X f then (0 : ℝ) else 1) = 0 := by
        apply Finset.prod_eq_zero hf
        simp only [(Finset.mem_erase.mp hf).1, ↓reduceIte]
        cases hval : X f <;> simp_all
      simp [hz]
    · simp [Selector.bit, hx]

/-- Exact expected number of matching edges retained in a single uniform nibble round. -/
theorem retained_count_expectation (H : Finset (Finset V)) (p : ℝ) :
    (∑ X, CliqueSampling.weight (fun _ => p) X * ((retained H X).card : ℝ)) =
      ∑ e ∈ H, p * (1 - p) ^ ((incident H e).erase e).card := by
  classical
  have hcard (X : Finset V → Bool) :
      ((retained H X).card : ℝ) = ∑ e ∈ H, if e ∈ retained H X then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    have hfilter : H.filter (fun e => e ∈ retained H X) = retained H X := by
      ext e
      simp [retained]
    simp [hfilter]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp_rw [isolated_indicator H _ e he]
  rw [product_moment (fun _ => p)
    (fun f b => if f = e then Selector.bit b else if b then 0 else 1),
    Finset.prod_insert (Finset.notMem_erase _ _)]
  simp only [↓reduceIte, Selector.bit, Bool.false_eq_true, mul_zero, mul_one, zero_add]
  congr 1
  calc
    _ = ∏ f ∈ (incident H e).erase e, (1 - p) := by
      apply Finset.prod_congr rfl
      intro f hf
      simp [(Finset.mem_erase.mp hf).1]
    _ = _ := Finset.prod_const _

omit [Fintype V] in
/-- A rank bound and maximum degree bound control each edge's possible conflicts. -/
theorem incident_card_le_rank_degree (H : Finset (Finset V)) (e : Finset V)
    (r : ℕ) (D : ℝ) (hD : 0 ≤ D) (he : e.card ≤ r)
    (hdegree : ∀ v, (degree H v : ℝ) ≤ D) :
    ((incident H e).card : ℝ) ≤ r * D := by
  classical
  have hunion : incident H e = e.biUnion (fun v => H.filter (fun f => v ∈ f)) := by
    ext f
    simp only [incident, Finset.mem_filter, Finset.mem_biUnion, Finset.Nonempty,
      Finset.mem_inter]
    aesop
  have hcard : (incident H e).card ≤ ∑ v ∈ e, degree H v := by
    rw [hunion]
    exact Finset.card_biUnion_le
  calc
    ((incident H e).card : ℝ) ≤ ∑ v ∈ e, (degree H v : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ v ∈ e, D := Finset.sum_le_sum (fun v _ => hdegree v)
    _ = (e.card : ℝ) * D := by simp
    _ ≤ r * D := mul_le_mul_of_nonneg_right (by exact_mod_cast he) hD

/-- The retained matching has the expected first-order size with an explicit second-order loss. -/
theorem retained_count_expectation_lower (H : Finset (Finset V)) (p D : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 0 ≤ D)
    (hrank : ∀ e ∈ H, e.card ≤ r) (hdegree : ∀ v, (degree H v : ℝ) ≤ D) :
    p * (1 - p * (r * D)) * H.card ≤
      ∑ X, CliqueSampling.weight (fun _ => p) X * ((retained H X).card : ℝ) := by
  rw [retained_count_expectation]
  calc
    _ = ∑ e ∈ H, p * (1 - p * (r * D)) := by simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      have hbound := incident_card_le_rank_degree H e r D hD (hrank e he) hdegree
      have herase : (((incident H e).erase e).card : ℝ) ≤ (incident H e).card := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset e (incident H e))
      have hbern : 1 - (((incident H e).erase e).card : ℝ) * p ≤
          (1 - p) ^ ((incident H e).erase e).card := by
        have h := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p)
          ((incident H e).erase e).card
        convert h using 1
        ring
      have hmul := mul_le_mul_of_nonneg_left (herase.trans hbound) hp
      apply mul_le_mul_of_nonneg_left _ hp
      nlinarith

end Erdos1017.HypergraphNibble
