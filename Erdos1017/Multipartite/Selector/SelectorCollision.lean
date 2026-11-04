module

public import Erdos1017.Multipartite.Selector.SelectorOptimalValue
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Collision bound for the selector optimum

An explicit adjacent-count mixture construction gives a relaxed selector for
every nonnegative finite load vector, which bounds the exact selector optimum on
the closed cube (`value_le_collision_bound`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector.Collision

open scoped BigOperators

variable {m : ℕ} {Ω : Type*} [Fintype Ω]

/-- A repeated label is retained exactly once when a word is collapsed. -/
def support (N : Fin m → ℕ) : Selection m := fun i => decide (0 < N i)

theorem bit_support_le (N : Fin m → ℕ) (i : Fin m) : bit (support N i) ≤ (N i : ℝ) := by
  by_cases hi : N i = 0
  · simp [support, bit, hi]
  · have hpos : 0 < N i := Nat.pos_of_ne_zero hi
    have hreal : (1 : ℝ) ≤ N i := by exact_mod_cast hpos
    simpa [support, bit, hpos] using hreal

theorem bit_support_nonneg (N : Fin m → ℕ) (i : Fin m) : 0 ≤ bit (support N i) := by
  unfold support bit
  split_ifs <;> norm_num

/-- Each lost duplicate is paid for by half the ordered collision count. -/
theorem duplicate_bound (n : ℕ) :
    (n : ℝ) - bit (decide (0 < n)) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rcases n with _ | n
  · norm_num [bit]
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [Nat.zero_lt_succ, decide_true, bit, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    nlinarith [sq_nonneg (n : ℝ), show (n : ℝ) ≤ (n : ℝ) ^ 2 from by
      rcases n with _ | n
      · norm_num
      · have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        nlinarith]

/-- Push a finite count law to Boolean supports, omitting its empty outcome. -/
def collapseWeight (μ : Ω → ℝ) (N : Ω → Fin m → ℕ) (X : Selection m) : ℝ :=
  if X = (fun _ => false) then 0 else ∑ ω, if support (N ω) = X then μ ω else 0

theorem collapseWeight_nonneg (μ : Ω → ℝ) (N : Ω → Fin m → ℕ)
    (hμ : ∀ ω, 0 ≤ μ ω) (X : Selection m) : 0 ≤ collapseWeight μ N X := by
  unfold collapseWeight
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg (fun ω _ => by split_ifs <;> simp_all)

theorem collapseWeight_expectation (μ : Ω → ℝ) (N : Ω → Fin m → ℕ)
    (h : Selection m → ℝ) (hzero : h (fun _ => false) = 0) :
    (∑ X, collapseWeight μ N X * h X) = ∑ ω, μ ω * h (support (N ω)) := by
  have hterm (X : Selection m) : collapseWeight μ N X * h X =
      (∑ ω, if support (N ω) = X then μ ω else 0) * h X := by
    by_cases hX : X = (fun _ => false)
    · simp [collapseWeight, hX, hzero]
    · simp [collapseWeight, hX]
  simp_rw [hterm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul, Finset.sum_ite_eq]

theorem collapseWeight_cost_le (μ : Ω → ℝ) (N : Ω → Fin m → ℕ)
    (hμ : ∀ ω, 0 ≤ μ ω) : cost (collapseWeight μ N) ≤ ∑ ω, μ ω := by
  have hterm (X : Selection m) : collapseWeight μ N X ≤
      ∑ ω, if support (N ω) = X then μ ω else 0 := by
    unfold collapseWeight
    split_ifs
    · exact Finset.sum_nonneg (fun ω _ => by split_ifs <;> simp_all)
    · exact le_rfl
  calc
    cost (collapseWeight μ N) ≤ ∑ X : Selection m, ∑ ω, if support (N ω) = X then μ ω else 0 :=
      Finset.sum_le_sum (fun X _ => hterm X)
    _ = ∑ ω, μ ω := by rw [Finset.sum_comm]; simp

/-- Singleton repairs restore every first moment lost to repeated labels. -/
def singletonWeight (δ : Fin m → ℝ) (X : Selection m) : ℝ :=
  ∑ i, if X = (fun k => decide (k = i)) then δ i else 0

theorem singletonWeight_expectation (δ : Fin m → ℝ) (h : Selection m → ℝ) :
    (∑ X, singletonWeight δ X * h X) = ∑ i, δ i * h (fun k => decide (k = i)) := by
  simp_rw [singletonWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

theorem singletonWeight_first (δ : Fin m → ℝ) (i : Fin m) :
    (∑ X, singletonWeight δ X * bit (X i)) = δ i := by
  rw [singletonWeight_expectation]
  simp [bit, mul_ite]

theorem singletonWeight_pair (δ : Fin m → ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∑ X, singletonWeight δ X * (bit (X i) * bit (X j))) = 0 := by
  rw [singletonWeight_expectation]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i = k
  · subst k
    simp [bit, Ne.symm hij]
  · simp [bit, hik]

theorem singletonWeight_cost (δ : Fin m → ℝ) : cost (singletonWeight δ) = ∑ i, δ i := by
  have h := singletonWeight_expectation δ (fun _ => 1)
  simpa only [cost, mul_one] using h

/-- An actual count law yields repaired Boolean weights, with every collision paid once. -/
theorem repair_count_law (p : Fin m → ℝ) (μ : Ω → ℝ) (N : Ω → Fin m → ℕ)
    (hμ : ∀ ω, 0 ≤ μ ω)
    (hfirst : ∀ i, ∑ ω, μ ω * (N ω i : ℝ) = p i)
    (hpair : ∀ i j, i ≠ j → ∑ ω, μ ω * ((N ω i : ℝ) * (N ω j : ℝ)) = p i * p j)
    (hdiag : ∀ i, ∑ ω, μ ω * ((N ω i : ℝ) * ((N ω i : ℝ) - 1)) = p i ^ 2) :
    ∃ w : Selection m → ℝ, RelaxedPrimalFeasible p w ∧
      cost w ≤ (∑ ω, μ ω) + (∑ i, p i ^ 2) / 2 := by
  let δ : Fin m → ℝ := fun i => p i - ∑ ω, μ ω * bit (support (N ω) i)
  have hδ : ∀ i, 0 ≤ δ i := by
    intro i
    apply sub_nonneg.mpr
    rw [← hfirst i]
    apply Finset.sum_le_sum
    intro ω _
    exact mul_le_mul_of_nonneg_left (bit_support_le (N ω) i) (hμ ω)
  let w : Selection m → ℝ := fun X => collapseWeight μ N X + singletonWeight δ X
  have hzero (i : Fin m) : (fun _ : Fin m => false) ≠ (fun k => decide (k = i)) := by
    intro h
    have hi := congrFun h i
    simp at hi
  refine ⟨w, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro X
    apply add_nonneg (collapseWeight_nonneg μ N hμ X)
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp_all)
  · simp [w, collapseWeight, singletonWeight, hzero]
  · intro i
    change p i ≤ ∑ X, (collapseWeight μ N X + singletonWeight δ X) * bit (X i)
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [collapseWeight_expectation μ N (fun X => bit (X i)) (by simp [bit]), singletonWeight_first]
    dsimp [δ]
    linarith
  · intro i j hij
    change (∑ X, (collapseWeight μ N X + singletonWeight δ X) * (bit (X i) * bit (X j))) ≤ p i * p j
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [singletonWeight_pair δ i j hij, add_zero,
      collapseWeight_expectation μ N (fun X => bit (X i) * bit (X j)) (by simp [bit]), ← hpair i j hij]
    apply Finset.sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (hμ ω)
    exact mul_le_mul (bit_support_le (N ω) i) (bit_support_le (N ω) j)
      (bit_support_nonneg (N ω) j) (Nat.cast_nonneg _)
  · have hδbound : ∀ i, δ i ≤ p i ^ 2 / 2 := by
      intro i
      calc
        δ i = ∑ ω, μ ω * ((N ω i : ℝ) - bit (support (N ω) i)) := by
          dsimp [δ]
          rw [← hfirst i]
          simp [mul_sub, Finset.sum_sub_distrib]
        _ ≤ ∑ ω, μ ω * ((N ω i : ℝ) * ((N ω i : ℝ) - 1) / 2) := by
          apply Finset.sum_le_sum
          intro ω _
          exact mul_le_mul_of_nonneg_left (duplicate_bound (N ω i)) (hμ ω)
        _ = p i ^ 2 / 2 := by simp_rw [mul_div, ← Finset.sum_div]; rw [hdiag i]
    have hsumδ : (∑ i, δ i) ≤ (∑ i, p i ^ 2) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun i _ => hδbound i)
    change (∑ X : Selection m, (collapseWeight μ N X + singletonWeight δ X)) ≤ _
    rw [Finset.sum_add_distrib]
    change cost (collapseWeight μ N) + cost (singletonWeight δ) ≤ _
    rw [singletonWeight_cost]
    exact add_le_add (collapseWeight_cost_le μ N hμ) hsumδ

def wordWeight (q : Fin m → ℝ) {k : ℕ} (v : Fin k → Fin m) : ℝ := ∏ t, q (v t)

def wordCount {k : ℕ} (v : Fin k → Fin m) (i : Fin m) : ℕ :=
  ∑ t, if v t = i then 1 else 0

theorem wordCount_cast {k : ℕ} (v : Fin k → Fin m) (i : Fin m) :
    (wordCount v i : ℝ) = ∑ t, bit (decide (v t = i)) := by
  simp [wordCount, bit]

/-- Finite independent draws factor exactly, including zero-probability labels. -/
theorem word_product_expectation {k : ℕ} (q : Fin m → ℝ) (h : Fin k → Fin m → ℝ) :
    (∑ v : Fin k → Fin m, wordWeight q v * ∏ t, h t (v t)) =
      ∏ t, ∑ i, q i * h t i := by
  simp only [wordWeight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (t : Fin k) (i : Fin m) => q i * h t i)).symm

theorem word_moment {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1)
    (S : Finset (Fin k)) (label : Fin k → Fin m) :
    (∑ v : Fin k → Fin m, wordWeight q v * ∏ t ∈ S, bit (decide (v t = label t))) =
      ∏ t ∈ S, q (label t) := by
  have h := word_product_expectation q (fun t i => if t ∈ S then bit (decide (i = label t)) else 1)
  have hfactor (t : Fin k) :
      (∑ i, q i * (if t ∈ S then bit (decide (i = label t)) else 1)) =
        if t ∈ S then q (label t) else 1 := by
    by_cases ht : t ∈ S <;> simp [ht, bit, mul_ite, hq]
  simp only [hfactor] at h
  simpa only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.prod_const_one, mul_one] using h

theorem wordWeight_total {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1) :
    ∑ v : Fin k → Fin m, wordWeight q v = 1 := by
  have h := word_product_expectation q (fun (_ : Fin k) _ => 1)
  simpa [hq] using h

theorem word_position_first {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1)
    (t : Fin k) (i : Fin m) :
    (∑ v : Fin k → Fin m, wordWeight q v * bit (decide (v t = i))) = q i := by
  simpa using word_moment q hq {t} (fun _ => i)

theorem word_position_pair {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1)
    (t u : Fin k) (htu : t ≠ u) (i j : Fin m) :
    (∑ v : Fin k → Fin m, wordWeight q v *
      (bit (decide (v t = i)) * bit (decide (v u = j)))) = q i * q j := by
  simpa [htu, Ne.symm htu] using word_moment q hq {t, u} (fun x => if x = t then i else j)

theorem word_first_moment {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1) (i : Fin m) :
    (∑ v : Fin k → Fin m, wordWeight q v * (wordCount v i : ℝ)) = (k : ℝ) * q i := by
  simp_rw [wordCount_cast, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [word_position_first q hq]
  simp

theorem word_position_product {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1)
    (t u : Fin k) (i j : Fin m) :
    (∑ v : Fin k → Fin m, wordWeight q v *
      (bit (decide (v t = i)) * bit (decide (v u = j)))) =
      q i * q j + if u = t then (if i = j then q i else 0) - q i * q j else 0 := by
  by_cases htu : u = t
  · subst u
    have hbits (v : Fin k → Fin m) :
        bit (decide (v t = i)) * bit (decide (v t = j)) =
          if i = j then bit (decide (v t = i)) else 0 := by
      by_cases hij : i = j
      · subst j
        by_cases hv : v t = i <;> simp [hv, bit]
      · by_cases hv : v t = i
        · simp [hv, hij, bit]
        · simp [hv, hij, bit]
    simp_rw [hbits]
    by_cases hij : i = j
    · simp only [hij, ite_true]
      rw [word_position_first q hq]
      ring
    · simp [hij]
  · rw [word_position_pair q hq t u (Ne.symm htu)]
    simp [htu]

theorem word_second_moment {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1) (i j : Fin m) :
    (∑ v : Fin k → Fin m, wordWeight q v * ((wordCount v i : ℝ) * (wordCount v j : ℝ))) =
      (k : ℝ) * ((k : ℝ) - 1) * (q i * q j) + if i = j then (k : ℝ) * q i else 0 := by
  have hexpand (v : Fin k → Fin m) :
      wordWeight q v * ((wordCount v i : ℝ) * (wordCount v j : ℝ)) =
        ∑ t : Fin k, ∑ u : Fin k, wordWeight q v *
          (bit (decide (v t = i)) * bit (decide (v u = j))) := by
    rw [wordCount_cast, wordCount_cast]
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  have hinner (t : Fin k) :
      (∑ v : Fin k → Fin m, ∑ u : Fin k, wordWeight q v *
        (bit (decide (v t = i)) * bit (decide (v u = j)))) =
      (k : ℝ) * (q i * q j) + (if i = j then q i else 0) - q i * q j := by
    rw [Finset.sum_comm]
    simp_rw [word_position_product q hq]
    simp [Finset.sum_add_distrib]
    ring
  simp_rw [hinner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] <;> ring

theorem word_pair_moment {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1)
    (i j : Fin m) (hij : i ≠ j) :
    (∑ v : Fin k → Fin m, wordWeight q v * ((wordCount v i : ℝ) * (wordCount v j : ℝ))) =
      (k : ℝ) * ((k : ℝ) - 1) * (q i * q j) := by
  simpa only [hij, ite_false, add_zero] using word_second_moment q hq i j

theorem word_factorial_moment {k : ℕ} (q : Fin m → ℝ) (hq : ∑ i, q i = 1) (i : Fin m) :
    (∑ v : Fin k → Fin m, wordWeight q v * ((wordCount v i : ℝ) * ((wordCount v i : ℝ) - 1))) =
      (k : ℝ) * ((k : ℝ) - 1) * q i ^ 2 := by
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [word_second_moment q hq, word_first_moment q hq]
  simp only [ite_true]
  ring

def drawIndex (T : ℝ) : ℕ := max 1 ⌈T⌉₊

/-- The nonempty mass of the adjacent integer draw-count law. -/
def collisionCurve (T : ℝ) : ℝ :=
  if T = 0 then 0 else
    let j : ℝ := drawIndex T
    (2 * j * T - T ^ 2) / (j * (j + 1))

def lowerCountMass (j : ℕ) (T : ℝ) : ℝ := T * ((j : ℝ) - T) / j

def upperCountMass (j : ℕ) (T : ℝ) : ℝ := T * (T - (j : ℝ) + 1) / ((j : ℝ) + 1)

theorem drawIndex_bounds {T : ℝ} (hT : 0 < T) :
    0 < drawIndex T ∧ (drawIndex T : ℝ) - 1 ≤ T ∧ T ≤ drawIndex T := by
  have hj : 1 ≤ ⌈T⌉₊ := Nat.one_le_ceil_iff.mpr hT
  have heq : drawIndex T = ⌈T⌉₊ := max_eq_right hj
  rw [heq]
  exact ⟨by omega, by linarith [Nat.ceil_lt_add_one hT.le], Nat.le_ceil T⟩

theorem countMass_nonneg {j : ℕ} {T : ℝ} (hj : 0 < j)
    (hT : 0 ≤ T) (hlo : (j : ℝ) - 1 ≤ T) (hhi : T ≤ j) :
    0 ≤ lowerCountMass j T ∧ 0 ≤ upperCountMass j T := by
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  unfold lowerCountMass upperCountMass
  constructor <;> apply div_nonneg
  · exact mul_nonneg hT (sub_nonneg.mpr hhi)
  · exact hj'.le
  · exact mul_nonneg hT (by linarith)
  · positivity

theorem countMass_total (j : ℕ) (hj : 0 < j) (T : ℝ) :
    lowerCountMass j T + upperCountMass j T =
      (2 * (j : ℝ) * T - T ^ 2) / ((j : ℝ) * ((j : ℝ) + 1)) := by
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  unfold lowerCountMass upperCountMass
  field_simp
  ring

theorem countMass_total_le_one (j : ℕ) (hj : 0 < j) (T : ℝ) :
    lowerCountMass j T + upperCountMass j T ≤ 1 := by
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  rw [countMass_total j hj T]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg (T - (j : ℝ))]

theorem countMass_mean (j : ℕ) (hj : 0 < j) (T : ℝ) :
    lowerCountMass j T * (j : ℝ) + upperCountMass j T * ((j : ℝ) + 1) = T := by
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  unfold lowerCountMass upperCountMass
  field_simp
  ring

theorem countMass_factorial (j : ℕ) (hj : 0 < j) (T : ℝ) :
    lowerCountMass j T * ((j : ℝ) * ((j : ℝ) - 1)) +
      upperCountMass j T * (((j : ℝ) + 1) * (j : ℝ)) = T ^ 2 := by
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  unfold lowerCountMass upperCountMass
  field_simp
  ring

abbrev DrawWords (m j : ℕ) := (Fin j → Fin m) ⊕ (Fin (j + 1) → Fin m)

def mixtureWeight (q : Fin m → ℝ) (j : ℕ) (T : ℝ) : DrawWords m j → ℝ :=
  Sum.elim (fun v => lowerCountMass j T * wordWeight q v)
    (fun v => upperCountMass j T * wordWeight q v)

def mixtureCount (j : ℕ) : DrawWords m j → Fin m → ℕ := Sum.elim wordCount wordCount

theorem mixture_total (q : Fin m → ℝ) (hq : ∑ i, q i = 1) (j : ℕ) (T : ℝ) :
    (∑ ω, mixtureWeight q j T ω) = lowerCountMass j T + upperCountMass j T := by
  simp only [Fintype.sum_sum_type, mixtureWeight, Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum]
  rw [wordWeight_total q hq, wordWeight_total q hq]
  ring

theorem mixture_first (q : Fin m → ℝ) (hq : ∑ i, q i = 1) (j : ℕ) (hj : 0 < j) (T : ℝ)
    (i : Fin m) :
    (∑ ω, mixtureWeight q j T ω * (mixtureCount j ω i : ℝ)) = T * q i := by
  simp only [Fintype.sum_sum_type, mixtureWeight, mixtureCount, Sum.elim_inl, Sum.elim_inr,
    mul_assoc, ← Finset.mul_sum]
  rw [word_first_moment q hq, word_first_moment q hq]
  push_cast
  have h := countMass_mean j hj T
  nlinarith [congrArg (fun x => x * q i) h]

theorem mixture_pair (q : Fin m → ℝ) (hq : ∑ i, q i = 1) (j : ℕ) (hj : 0 < j) (T : ℝ)
    (i l : Fin m) (hil : i ≠ l) :
    (∑ ω, mixtureWeight q j T ω * ((mixtureCount j ω i : ℝ) * (mixtureCount j ω l : ℝ))) =
      T ^ 2 * (q i * q l) := by
  simp only [Fintype.sum_sum_type, mixtureWeight, mixtureCount, Sum.elim_inl, Sum.elim_inr,
    mul_assoc, ← Finset.mul_sum]
  rw [word_pair_moment q hq i l hil, word_pair_moment q hq i l hil]
  push_cast
  have h := countMass_factorial j hj T
  nlinarith [congrArg (fun x => x * (q i * q l)) h]

theorem mixture_factorial (q : Fin m → ℝ) (hq : ∑ i, q i = 1) (j : ℕ) (hj : 0 < j) (T : ℝ)
    (i : Fin m) :
    (∑ ω, mixtureWeight q j T ω * ((mixtureCount j ω i : ℝ) * ((mixtureCount j ω i : ℝ) - 1))) =
      T ^ 2 * q i ^ 2 := by
  simp only [Fintype.sum_sum_type, mixtureWeight, mixtureCount, Sum.elim_inl, Sum.elim_inr,
    mul_assoc, ← Finset.mul_sum]
  rw [word_factorial_moment q hq, word_factorial_moment q hq]
  push_cast
  have h := countMass_factorial j hj T
  nlinarith [congrArg (fun x => x * q i ^ 2) h]

/-- The explicit adjacent-count construction gives a relaxed selector for every
nonnegative finite load vector. Its zero-count outcome is omitted. -/
theorem exists_relaxed_collision_bound (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∃ w : Selection m → ℝ, RelaxedPrimalFeasible p w ∧
      cost w ≤ collisionCurve (∑ i, p i) + (∑ i, p i ^ 2) / 2 := by
  let T : ℝ := ∑ i, p i
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg (fun i _ => hp i)
  by_cases hTzero : T = 0
  · have hpzero : ∀ i, p i = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hp i)).mp hTzero
      exact fun i => h i (Finset.mem_univ i)
    refine ⟨0, ?_, ?_⟩
    · simp [RelaxedPrimalFeasible, hpzero]
    · simp [cost, hpzero, collisionCurve]
  · have hT : 0 < T := lt_of_le_of_ne hTnonneg (Ne.symm hTzero)
    let j := drawIndex T
    have hj := drawIndex_bounds hT
    let q : Fin m → ℝ := fun i => p i / T
    have hq : ∑ i, q i = 1 := by
      dsimp [q]
      rw [← Finset.sum_div]
      exact div_self hTzero
    have hmass := countMass_nonneg hj.1 hT.le hj.2.1 hj.2.2
    have hμ : ∀ ω : DrawWords m j, 0 ≤ mixtureWeight q j T ω := by
      intro ω
      cases ω with
      | inl v =>
        apply mul_nonneg hmass.1
        exact Finset.prod_nonneg (fun t _ => div_nonneg (hp (v t)) hT.le)
      | inr v =>
        apply mul_nonneg hmass.2
        exact Finset.prod_nonneg (fun t _ => div_nonneg (hp (v t)) hT.le)
    have hfirst : ∀ i, ∑ ω : DrawWords m j,
        mixtureWeight q j T ω * (mixtureCount j ω i : ℝ) = p i := by
      intro i
      rw [mixture_first q hq j hj.1 T i]
      dsimp [q]
      field_simp
    have hpair : ∀ i l, i ≠ l → ∑ ω : DrawWords m j,
        mixtureWeight q j T ω * ((mixtureCount j ω i : ℝ) * (mixtureCount j ω l : ℝ)) = p i * p l := by
      intro i l hil
      rw [mixture_pair q hq j hj.1 T i l hil]
      dsimp [q]
      field_simp
    have hdiag : ∀ i, ∑ ω : DrawWords m j,
        mixtureWeight q j T ω * ((mixtureCount j ω i : ℝ) * ((mixtureCount j ω i : ℝ) - 1)) = p i ^ 2 := by
      intro i
      rw [mixture_factorial q hq j hj.1 T i]
      dsimp [q]
      field_simp
    obtain ⟨w, hw, hcost⟩ := repair_count_law p (mixtureWeight q j T) (mixtureCount j) hμ hfirst hpair hdiag
    refine ⟨w, hw, ?_⟩
    rw [mixture_total q hq j T, countMass_total j hj.1 T] at hcost
    change cost w ≤ collisionCurve T + (∑ i, p i ^ 2) / 2
    rw [collisionCurve, ite_eq_right hTzero]
    exact hcost

/-- The collision construction bounds the actual exact selector optimum on the closed cube. -/
theorem value_le_collision_bound (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    value p ≤ min 1 (collisionCurve (∑ i, p i) + (∑ i, p i ^ 2) / 2) := by
  obtain ⟨w, hw, hcost⟩ := exists_relaxed_collision_bound p (fun i => (hp i).1)
  exact le_min (value_le_one p hp) ((value_le_relaxed_cost p hp w hw).trans hcost)

end Erdos1017.Selector.Collision
