module

public import Erdos1017.Models.PhysicalPrimal.FiniteSubsetSampling
public import Erdos1017.Models.PhysicalPrimal.FiniteArityRounding
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Positivity

/-!
# Independent sampling inside adjacency bins

Configurations are sampled independently inside each retained adjacency bin
(`productWeight`, `binCharge`), with exact expectations and moments; tested
subconfigurations bound the expected count polynomial, imply coercivity of the
average-charge matrix `binMatrix`, and bound the charge of the full retained
bins.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FiniteArity

variable {m : ℕ} {Ω : Type*} [Fintype Ω]

/-- Independent finite choices for the retained adjacency bins. -/
def productWeight (q : Fin m → Ω → ℝ) (v : Fin m → Ω) : ℝ := ∏ i, q i (v i)

theorem product_expectation (q h : Fin m → Ω → ℝ) :
    (∑ v, productWeight q v * ∏ i, h i (v i)) = ∏ i, ∑ x, q i x * h i x := by
  simp only [productWeight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => q i x * h i x)).symm

theorem product_moment (q h : Fin m → Ω → ℝ) (hq : ∀ i, ∑ x, q i x = 1)
    (S : Finset (Fin m)) :
    (∑ v, productWeight q v * ∏ i ∈ S, h i (v i)) = ∏ i ∈ S, ∑ x, q i x * h i x := by
  have hm := product_expectation q (fun i x => if i ∈ S then h i x else 1)
  have hfactor (i : Fin m) :
      (∑ x, q i x * (if i ∈ S then h i x else 1)) =
        if i ∈ S then ∑ x, q i x * h i x else 1 := by
    by_cases hi : i ∈ S <;> simp [hi, hq]
  simp only [hfactor] at hm
  simpa only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.prod_const_one, mul_one] using hm

theorem productWeight_total (q : Fin m → Ω → ℝ) (hq : ∀ i, ∑ x, q i x = 1) :
    ∑ v, productWeight q v = 1 := by
  simpa using product_moment q (fun _ _ => 1) hq ∅

theorem product_first (q : Fin m → Ω → ℝ) (hq : ∀ i, ∑ x, q i x = 1)
    (f : Ω → ℝ) (i : Fin m) :
    (∑ v, productWeight q v * f (v i)) = ∑ x, q i x * f x := by
  simpa using product_moment q (fun _ x => f x) hq {i}

theorem product_pair (q : Fin m → Ω → ℝ) (hq : ∀ i, ∑ x, q i x = 1)
    (f g : Ω → ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∑ v, productWeight q v * (f (v i) * g (v j))) =
      (∑ x, q i x * f x) * (∑ x, q j x * g x) := by
  simpa [hij, hij.symm] using
    product_moment q (fun t x => if t = i then f x else g x) hq {i, j}

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Uniform without-replacement sampling, represented on all subsets with zero
weight assigned to subsets outside the requested size and ambient bin. -/
def subsetWeight (U : Finset α) (k : ℕ) (S : Finset α) : ℝ :=
  if S ∈ U.powersetCard k then (U.card.choose k : ℝ)⁻¹ else 0

theorem subset_expectation (U : Finset α) (k : ℕ) (f : Finset α → ℝ) :
    (∑ S, subsetWeight U k S * f S) =
      (∑ S ∈ U.powersetCard k, f S) / (U.card.choose k : ℝ) := by
  simp only [subsetWeight, ite_mul, zero_mul, ← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun S : Finset α => S ∈ U.powersetCard k) = U.powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter, ← Finset.mul_sum, div_eq_inv_mul]

theorem subsetWeight_total (U : Finset α) (k : ℕ) (hk : k ≤ U.card) :
    ∑ S, subsetWeight U k S = 1 := by
  have h := subset_expectation U k (fun _ => 1)
  have hc : (U.card.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  simpa [Finset.card_powersetCard, hc] using h

/-- Membership indicator for a sampled subset. -/
def subsetBit (S : Finset α) (a : α) : ℝ := if a ∈ S then 1 else 0

omit [Fintype α] in
private theorem singleton_indicator_sum (S : Finset α) (a : α) :
    (∑ t ∈ S.powersetCard 1, if t = {a} then (1 : ℝ) else 0) = subsetBit S a := by
  simp [subsetBit, Finset.singleton_subset_iff]

theorem subset_first_moment (U : Finset α) (k : ℕ) (hk : k ≤ U.card) (a : α) :
    (∑ S, subsetWeight U k S * subsetBit S a) =
      (k : ℝ) / U.card * subsetBit U a := by
  rw [subset_expectation]
  by_cases hk0 : k = 0
  · subst k
    simp [subsetBit]
  · have h1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hm := subset_sample_average U 1 k h1 hk (fun t => if t = {a} then (1 : ℝ) else 0)
    simp only [singleton_indicator_sum, Nat.choose_one_right] at hm
    rw [hm]
    unfold subsetAverage
    rw [singleton_indicator_sum, Nat.choose_one_right]
    ring

omit [Fintype α] in
private theorem pair_indicator_sum (S : Finset α) (a b : α) (hab : a ≠ b) :
    (∑ t ∈ S.powersetCard 2, if t = {a, b} then (1 : ℝ) else 0) =
      subsetBit S a * subsetBit S b := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    simp [subsetBit, ha, hb, hab, Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem subset_pair_moment (U : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (a b : α) (hab : a ≠ b) :
    (∑ S, subsetWeight U k S * (subsetBit S a * subsetBit S b)) =
      ((k.choose 2 : ℝ) / U.card.choose 2) * (subsetBit U a * subsetBit U b) := by
  rw [subset_expectation]
  have hm := subset_sample_average_all U 2 k hk
    (fun t => if t = {a, b} then (1 : ℝ) else 0)
  simp only [pair_indicator_sum _ _ _ hab] at hm
  rw [hm]
  unfold subsetAverage
  rw [pair_indicator_sum _ _ _ hab]
  ring

theorem subset_within_moment (U : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (f : Finset α → ℝ) :
    (∑ S, subsetWeight U k S * ∑ t ∈ S.powersetCard 2, f t) =
      (k.choose 2 : ℝ) * subsetAverage U 2 f := by
  rw [subset_expectation]
  exact subset_sample_average_all U 2 k hk f

/-- Signed total charge between two selected bins. -/
def crossSum (S T : Finset α) (y : α → α → ℝ) : ℝ := ∑ a ∈ S, ∑ b ∈ T, y a b

/-- Mean charge between two ambient bins. -/
def crossAverage (S T : Finset α) (y : α → α → ℝ) : ℝ :=
  crossSum S T y / ((S.card : ℝ) * T.card)

theorem crossSum_bit (S T : Finset α) (y : α → α → ℝ) :
    crossSum S T y = ∑ a, ∑ b, y a b * subsetBit S a * subsetBit T b := by
  simp [crossSum, subsetBit, mul_ite, Finset.sum_ite_mem]

/-- Independent without-replacement choices in distinct bins have exact cross load. -/
theorem subset_cross_moment (U : Fin m → Finset α) (n : Fin m → ℕ)
    (hn : ∀ i, n i ≤ (U i).card) (y : α → α → ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∑ v, productWeight (fun t => subsetWeight (U t) (n t)) v * crossSum (v i) (v j) y) =
      ((n i : ℝ) / (U i).card) * ((n j : ℝ) / (U j).card) * crossSum (U i) (U j) y := by
  simp only [crossSum_bit, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hp := product_pair (fun t => subsetWeight (U t) (n t))
    (fun t => subsetWeight_total (U t) (n t) (hn t))
    (fun S => subsetBit S a) (fun S => subsetBit S b) i j hij
  rw [subset_first_moment _ _ (hn i), subset_first_moment _ _ (hn j)] at hp
  calc
    _ = y a b * (∑ v, productWeight (fun t => subsetWeight (U t) (n t)) v *
        (subsetBit (v i) a * subsetBit (v j) b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by rw [hp]; ring

theorem subset_cross_expectation (U : Fin m → Finset α) (n : Fin m → ℕ)
    (hn : ∀ i, n i ≤ (U i).card) (y : α → α → ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∑ v, productWeight (fun t => subsetWeight (U t) (n t)) v * crossSum (v i) (v j) y) =
      (n i : ℝ) * n j * crossAverage (U i) (U j) y := by
  rw [subset_cross_moment U n hn y i j hij]
  unfold crossAverage
  ring

/-- Matrix of negative average within-bin and between-bin charges. -/
def binMatrix (a : Fin m → ℝ) (b : Fin m → Fin m → ℝ) (i j : Fin m) : ℝ :=
  if i = j then -a i else -b i j

theorem countCharge_binMatrix (a : Fin m → ℝ) (b : Fin m → Fin m → ℝ)
    (n : Fin m → ℕ) :
    countCharge (binMatrix a b) (fun i => (n i : ℝ)) =
      (∑ i, (n i).choose 2 * a i) +
      (∑ i, ∑ j, if i = j then 0 else (n i : ℝ) * n j * b i j) / 2 := by
  have hlinear : (∑ i, binMatrix a b i i * (n i : ℝ)) = -∑ i, a i * n i := by
    simp [binMatrix, Finset.sum_neg_distrib]
  have hpoint (i j : Fin m) : binMatrix a b i j * (n i : ℝ) * n j =
      (if i = j then -(a i * (n i : ℝ) ^ 2) else 0) -
      (if i = j then 0 else (n i : ℝ) * n j * b i j) := by
    by_cases hij : i = j
    · subst j
      simp [binMatrix]
      ring
    · simp [binMatrix, hij]
      ring
  have hquadratic : (∑ i, ∑ j, binMatrix a b i j * (n i : ℝ) * n j) =
      -(∑ i, a i * (n i : ℝ) ^ 2) -
        (∑ i, ∑ j, if i = j then 0 else (n i : ℝ) * n j * b i j) := by
    simp_rw [hpoint, Finset.sum_sub_distrib]
    simp [Finset.sum_neg_distrib]
  unfold countCharge
  rw [hlinear, hquadratic]
  have hwithin : (∑ i, (n i).choose 2 * a i) =
      ((∑ i, a i * (n i : ℝ) ^ 2) - ∑ i, a i * n i) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_choose_two]
    ring
  rw [hwithin]
  ring

/-- The charge of a configuration sampled separately inside each bin. -/
def binCharge (within : Fin m → Finset α → ℝ)
    (cross : Fin m → Fin m → α → α → ℝ) (v : Fin m → Finset α) : ℝ :=
  (∑ i, ∑ t ∈ (v i).powersetCard 2, within i t) +
    (∑ i, ∑ j, if i = j then 0 else crossSum (v i) (v j) (cross i j)) / 2

/-- Exact expected charge of the actual independent bin samples. -/
theorem binCharge_expectation (U : Fin m → Finset α) (n : Fin m → ℕ)
    (hn : ∀ i, n i ≤ (U i).card) (within : Fin m → Finset α → ℝ)
    (cross : Fin m → Fin m → α → α → ℝ) :
    (∑ v, productWeight (fun t => subsetWeight (U t) (n t)) v * binCharge within cross v) =
      countCharge (binMatrix (fun i => subsetAverage (U i) 2 (within i))
        (fun i j => crossAverage (U i) (U j) (cross i j))) (fun i => (n i : ℝ)) := by
  have htotal : ∀ i, ∑ S, subsetWeight (U i) (n i) S = 1 :=
    fun i => subsetWeight_total (U i) (n i) (hn i)
  have hwithin :
      (∑ v, productWeight (fun t => subsetWeight (U t) (n t)) v *
        ∑ i, ∑ t ∈ (v i).powersetCard 2, within i t) =
      ∑ i, (n i).choose 2 * subsetAverage (U i) 2 (within i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← Finset.mul_sum]
    rw [product_first _ htotal (fun S => ∑ t ∈ S.powersetCard 2, within i t) i]
    exact subset_within_moment (U i) (n i) (hn i) (within i)
  have hcross :
      (∑ v, productWeight (fun t => subsetWeight (U t) (n t)) v *
        ∑ i, ∑ j, if i = j then 0 else crossSum (v i) (v j) (cross i j)) =
      ∑ i, ∑ j, if i = j then 0 else
        (n i : ℝ) * n j * crossAverage (U i) (U j) (cross i j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ite_false]
      exact subset_cross_expectation U n hn (cross i j) i j hij
  unfold binCharge
  simp only [mul_add, mul_div, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hwithin, hcross, countCharge_binMatrix]

/-- Tested actual configurations bound the expected count polynomial. -/
theorem countCharge_le_of_bin_tests (U : Fin m → Finset α) (n : Fin m → ℕ)
    (hn : ∀ i, n i ≤ (U i).card) (within : Fin m → Finset α → ℝ)
    (cross : Fin m → Fin m → α → α → ℝ)
    (htest : ∀ v : Fin m → Finset α, (∀ i, v i ∈ (U i).powersetCard (n i)) →
      binCharge within cross v ≤ 1) :
    countCharge (binMatrix (fun i => subsetAverage (U i) 2 (within i))
      (fun i j => crossAverage (U i) (U j) (cross i j))) (fun i => (n i : ℝ)) ≤ 1 := by
  rw [← binCharge_expectation U n hn within cross,
    ← productWeight_total _ (fun i => subsetWeight_total (U i) (n i) (hn i))]
  apply Finset.sum_le_sum
  intro v _
  have hnonneg : 0 ≤ productWeight (fun t => subsetWeight (U t) (n t)) v := by
    apply Finset.prod_nonneg
    intro i _
    dsimp only [subsetWeight]
    split_ifs <;> positivity
  by_cases hz : productWeight (fun t => subsetWeight (U t) (n t)) v = 0
  · simp [hz]
  · apply mul_le_of_le_one_right hnonneg
    apply htest
    intro i
    by_contra hi
    apply hz
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [subsetWeight, hi])

/-- Actual bounded subconfigurations imply coercivity of their average-charge matrix. -/
theorem binMatrix_coercive (U : Fin m → Finset α) (T : ℕ) (hT : 0 < T)
    (hcapacity : ∀ i, T ≤ (U i).card) (within : Fin m → Finset α → ℝ)
    (cross : Fin m → Fin m → α → α → ℝ) (p₀ : ℝ) (hp₀ : 0 ≤ p₀)
    (hdiag : ∀ i, p₀ ≤ -subsetAverage (U i) 2 (within i) ∧
      -subsetAverage (U i) 2 (within i) ≤ 3)
    (htest : ∀ v : Fin m → Finset α, (∀ i, v i ⊆ U i) →
      (∀ i, (v i).card ≤ T) → (∑ i, (v i).card) ≤ T + m → binCharge within cross v ≤ 1)
    (hsize : 3 * (m : ℝ) / 2 + 4 ≤ T * p₀)
    (θ : Fin m → ℝ) (hθ : ∀ i, 0 ≤ θ i) (hθsum : ∑ i, θ i = 1) :
    p₀ / (2 * T) ≤ ∑ i, ∑ j,
      binMatrix (fun i => subsetAverage (U i) 2 (within i))
        (fun i j => crossAverage (U i) (U j) (cross i j)) i j * θ i * θ j := by
  apply probability_coercive_of_count_tests θ hθ hθsum _ p₀ T hp₀ hT
    (fun i => by simpa [binMatrix] using hdiag i) _ hsize
  intro n hn hsum
  apply countCharge_le_of_bin_tests U n (fun i => (hn i).trans (hcapacity i)) within cross
  intro v hv
  apply htest v (fun i => (Finset.mem_powersetCard.mp (hv i)).1)
  · intro i
    rw [(Finset.mem_powersetCard.mp (hv i)).2]
    exact hn i
  · simpa only [(fun i => (Finset.mem_powersetCard.mp (hv i)).2)] using hsum

omit [Fintype α] in
private theorem productWeight_full (U v : Fin m → Finset α) :
    productWeight (fun i => subsetWeight (U i) (U i).card) v = if v = U then 1 else 0 := by
  by_cases hv : v = U
  · subst v
    simp [productWeight, subsetWeight]
  · rw [ite_eq_right hv]
    have hi : ∃ i, v i ≠ U i := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [subsetWeight, hi])

/-- Sampling every vertex of every bin recovers its actual charge exactly. -/
theorem binCharge_full_eq (U : Fin m → Finset α) (within : Fin m → Finset α → ℝ)
    (cross : Fin m → Fin m → α → α → ℝ) :
    binCharge within cross U =
      countCharge (binMatrix (fun i => subsetAverage (U i) 2 (within i))
        (fun i j => crossAverage (U i) (U j) (cross i j)))
        (fun i => ((U i).card : ℝ)) := by
  have h := binCharge_expectation U (fun i => (U i).card) (fun _ => le_rfl) within cross
  simpa [productWeight_full, ite_mul] using h

/-- Small actual subconfiguration tests bound the charge of the full retained bins. -/
theorem binCharge_bound_of_small_tests (U : Fin m → Finset α) (T : ℕ) (hT : 0 < T)
    (hcapacity : ∀ i, T ≤ (U i).card) (within : Fin m → Finset α → ℝ)
    (cross : Fin m → Fin m → α → α → ℝ) (p₀ : ℝ) (hp₀ : 0 ≤ p₀)
    (hdiag : ∀ i, p₀ ≤ -subsetAverage (U i) 2 (within i) ∧
      -subsetAverage (U i) 2 (within i) ≤ 3)
    (htest : ∀ v : Fin m → Finset α, (∀ i, v i ⊆ U i) →
      (∀ i, (v i).card ≤ T) → (∑ i, (v i).card) ≤ T + m → binCharge within cross v ≤ 1)
    (hsize : 3 * (m : ℝ) / 2 + 4 ≤ T * p₀)
    (n : ℝ) (hsum : ∑ i, ((U i).card : ℝ) = n) (hn : 0 < n) :
    binCharge within cross U ≤ 3 * n / 2 - (p₀ / (2 * T)) * n ^ 2 / 2 := by
  rw [binCharge_full_eq]
  apply countCharge_le_of_coercive _ (p₀ / (2 * T))
    (fun i => by simpa [binMatrix] using (hdiag i).2) _
    (fun i => ((U i).card : ℝ)) (fun i => Nat.cast_nonneg _) n hsum hn
  intro θ hθ hθsum
  exact binMatrix_coercive U T hT hcapacity within cross p₀ hp₀ hdiag htest hsize θ hθ hθsum

end Erdos1017.FiniteArity
