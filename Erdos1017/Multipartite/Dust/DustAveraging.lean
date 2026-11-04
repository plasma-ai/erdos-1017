module

public import Erdos1017.Multipartite.CountExtension
public import Erdos1017.Multipartite.Selector.SelectorClipping
public import Erdos1017.Multipartite.Selector.SelectorCollision

/-!
# Averaging repeated types into dust cells

Replacing repeated types by `N` uniform dust cells keeps exact all-count
feasibility with an objective loss between zero and `s²/(2N)`, the quadratic
dust coefficient is an average over ordered type pairs, and the finite selector
value has an averaged all-count witness with the explicit `N`-cell error.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector

open scoped BigOperators

/-- Polarization of the symmetric zero-diagonal selector objective. -/
theorem objective_add {m : ℕ} (D : Dual m) (u v : Fin m → ℝ) :
    objective (fun i => u i + v i) D = objective u D + objective v D +
      ∑ i, ∑ j, D.beta i j * (u i * v j) := by
  unfold objective
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  have hcross : (∑ i, ∑ j, D.beta i j * (v i * u j)) =
      ∑ i, ∑ j, D.beta i j * (u i * v j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [D.beta_symm]
    ring
  rw [hcross]
  ring

/-- Combining deterministic and random counts keeps every cross interaction. -/
theorem repeatedCharge_add {m : ℕ} (D : Dual m) (b n : Fin m → ℕ) :
    repeatedCharge D (fun i => b i + n i) = repeatedCharge D b + repeatedCharge D n +
      (∑ i, ∑ j, D.beta i j * ((b i : ℝ) * n j)) -
      ∑ i, D.alpha i * (b i : ℝ) * n i := by
  have hself (i : Fin m) :
      D.alpha i * ((b i : ℝ) + n i) * ((b i : ℝ) + n i - 1) / 2 =
      D.alpha i * (b i : ℝ) * ((b i : ℝ) - 1) / 2 +
      D.alpha i * (n i : ℝ) * ((n i : ℝ) - 1) / 2 +
      D.alpha i * (b i : ℝ) * n i := by ring
  unfold repeatedCharge
  simp only [Nat.cast_add, objective_add, hself, Finset.sum_add_distrib]
  ring

/-- The averaged repeated-type linear coefficient. -/
def dustLinear {m : ℕ} (D : Dual m) (q : Fin m → ℝ) : ℝ := ∑ i, D.alpha i * q i

/-- Default self penalties contribute also when two independent draws choose the same label. -/
def dustPenalty {m : ℕ} (D : Dual m) (q : Fin m → ℝ) : ℝ :=
  (∑ i, D.alpha i * q i ^ 2) - ∑ i, ∑ j, D.beta i j * (q i * q j)

/-- Averaging independent type assignments gives the exact all-count dust polynomial. -/
theorem word_repeatedCharge_expectation {m k : ℕ} (D : Dual m) (q : Fin m → ℝ)
    (hq : ∑ i, q i = 1) :
    (∑ v : Fin k → Fin m, Collision.wordWeight q v * repeatedCharge D (Collision.wordCount v)) =
      (k : ℝ) * dustLinear D q - (k : ℝ) * (k - 1) * dustPenalty D q / 2 := by
  have hfirst (i : Fin m) :
      (∑ v : Fin k → Fin m, Collision.wordWeight q v *
        (D.alpha i * (Collision.wordCount v i : ℝ))) = D.alpha i * ((k : ℝ) * q i) := by
    simp_rw [mul_left_comm _ (D.alpha i), ← Finset.mul_sum]
    rw [Collision.word_first_moment q hq]
  have hpair (i j : Fin m) :
      (∑ v : Fin k → Fin m, Collision.wordWeight q v *
        (D.beta i j * ((Collision.wordCount v i : ℝ) * Collision.wordCount v j))) =
      D.beta i j * ((k : ℝ) * (k - 1) * q i * q j) := by
    by_cases hij : i = j
    · subst j
      simp [D.beta_diag]
    · simp_rw [mul_left_comm _ (D.beta i j), ← Finset.mul_sum]
      rw [Collision.word_pair_moment q hq i j hij]
      ring
  have hself (i : Fin m) :
      (∑ v : Fin k → Fin m, Collision.wordWeight q v *
        (D.alpha i * (Collision.wordCount v i : ℝ) * ((Collision.wordCount v i : ℝ) - 1) / 2)) =
      D.alpha i * ((k : ℝ) * (k - 1) * q i ^ 2) / 2 := by
    have hterm (v : Fin k → Fin m) : Collision.wordWeight q v *
        (D.alpha i * (Collision.wordCount v i : ℝ) * ((Collision.wordCount v i : ℝ) - 1) / 2) =
        D.alpha i / 2 * (Collision.wordWeight q v *
          ((Collision.wordCount v i : ℝ) * ((Collision.wordCount v i : ℝ) - 1))) := by ring
    simp_rw [hterm, ← Finset.mul_sum]
    rw [Collision.word_factorial_moment q hq i]
    ring
  have hexpand (v : Fin k → Fin m) :
      Collision.wordWeight q v * repeatedCharge D (Collision.wordCount v) =
      (∑ i, Collision.wordWeight q v * (D.alpha i * (Collision.wordCount v i : ℝ))) +
      (∑ i, ∑ j, Collision.wordWeight q v *
        (D.beta i j * ((Collision.wordCount v i : ℝ) * Collision.wordCount v j))) / 2 -
      ∑ i, Collision.wordWeight q v *
        (D.alpha i * (Collision.wordCount v i : ℝ) * ((Collision.wordCount v i : ℝ) - 1) / 2) := by
    unfold repeatedCharge objective
    rw [mul_sub, mul_add, mul_div]
    simp only [Finset.mul_sum]
  have hlinear : (∑ v : Fin k → Fin m, ∑ i, Collision.wordWeight q v *
      (D.alpha i * (Collision.wordCount v i : ℝ))) =
      (k : ℝ) * dustLinear D q := by
    rw [Finset.sum_comm]
    simp_rw [hfirst]
    unfold dustLinear
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hpairs : (∑ v : Fin k → Fin m, ∑ i, ∑ j, Collision.wordWeight q v *
      (D.beta i j * ((Collision.wordCount v i : ℝ) * Collision.wordCount v j))) =
      (k : ℝ) * (k - 1) * ∑ i, ∑ j, D.beta i j * (q i * q j) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpair]
    ring
  have hselves : (∑ v : Fin k → Fin m, ∑ i, Collision.wordWeight q v *
      (D.alpha i * (Collision.wordCount v i : ℝ) * ((Collision.wordCount v i : ℝ) - 1) / 2)) =
      (k : ℝ) * (k - 1) * (∑ i, D.alpha i * q i ^ 2) / 2 := by
    rw [Finset.sum_comm]
    simp_rw [hself]
    simp only [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [hexpand]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
    hlinear, hpairs, hselves]
  unfold dustPenalty
  ring

/-- Exact averaging with arbitrary fixed exterior counts. -/
theorem word_addedCharge_expectation {m k : ℕ} (D : Dual m) (q : Fin m → ℝ)
    (hq : ∑ i, q i = 1) (b : Fin m → ℕ) :
    (∑ v : Fin k → Fin m, Collision.wordWeight q v *
      repeatedCharge D (fun i => b i + Collision.wordCount v i)) =
      repeatedCharge D b + (k : ℝ) * dustLinear D q +
        (k : ℝ) * (∑ i, ∑ j, D.beta i j * ((b i : ℝ) * q j)) -
        (k : ℝ) * (∑ i, D.alpha i * (b i : ℝ) * q i) -
        (k : ℝ) * (k - 1) * dustPenalty D q / 2 := by
  have hcross : (∑ v : Fin k → Fin m, Collision.wordWeight q v *
      (∑ i, ∑ j, D.beta i j * ((b i : ℝ) * Collision.wordCount v j))) =
      (k : ℝ) * ∑ i, ∑ j, D.beta i j * ((b i : ℝ) * q j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have ht (v : Fin k → Fin m) : Collision.wordWeight q v *
        (D.beta i j * ((b i : ℝ) * Collision.wordCount v j)) =
        (D.beta i j * (b i : ℝ)) * (Collision.wordWeight q v * (Collision.wordCount v j : ℝ)) := by ring
    simp_rw [ht, ← Finset.mul_sum]
    rw [Collision.word_first_moment q hq]
    ring
  have hself : (∑ v : Fin k → Fin m, Collision.wordWeight q v *
      (∑ i, D.alpha i * (b i : ℝ) * Collision.wordCount v i)) =
      (k : ℝ) * ∑ i, D.alpha i * (b i : ℝ) * q i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have ht (v : Fin k → Fin m) : Collision.wordWeight q v *
        (D.alpha i * (b i : ℝ) * Collision.wordCount v i) =
        (D.alpha i * (b i : ℝ)) * (Collision.wordWeight q v * (Collision.wordCount v i : ℝ)) := by ring
    simp_rw [ht, ← Finset.mul_sum]
    rw [Collision.word_first_moment q hq]
    ring
  simp_rw [repeatedCharge_add]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, Collision.wordWeight_total q hq, one_mul,
    word_repeatedCharge_expectation D q hq, hcross, hself]
  ring

/-- Independent type averaging preserves every exterior-count inequality.
The final term accounts for labels already present among the exterior counts. -/
theorem averaged_count_le_one {m : ℕ} (D : Dual m) (hD : DualFeasible D)
    (halpha : ∀ i, 0 ≤ D.alpha i) (hbeta : ∀ i j, D.beta i j ≤ 0)
    (q : Fin m → ℝ) (hq₀ : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1)
    (b : Fin m → ℕ) (k : ℕ) :
    repeatedCharge D b + (k : ℝ) * dustLinear D q +
        (k : ℝ) * (∑ i, ∑ j, D.beta i j * ((b i : ℝ) * q j)) -
        (k : ℝ) * (∑ i, D.alpha i * (b i : ℝ) * q i) -
        (k : ℝ) * (k - 1) * dustPenalty D q / 2 ≤ 1 := by
  rw [← word_addedCharge_expectation D q hq b, ← Collision.wordWeight_total (k := k) q hq]
  apply Finset.sum_le_sum
  intro v _
  have hw : 0 ≤ Collision.wordWeight q v :=
    Finset.prod_nonneg (fun t _ => hq₀ (v t))
  simpa using mul_le_mul_of_nonneg_left
    (repeatedCharge_le_one D hD halpha hbeta (fun i => b i + Collision.wordCount v i)) hw

/-- The value of an averaged dust type, with the exterior masses left fixed. -/
def averagedValue {m : ℕ} (D : Dual m) (p q : Fin m → ℝ) (s : ℝ) : ℝ :=
  objective p D + s * (dustLinear D q + ∑ i, ∑ j, D.beta i j * (p i * q j)) -
    s ^ 2 * dustPenalty D q / 2

/-- Averaging loses exactly the newly added internal same-label pair penalties. -/
theorem averaging_loss {m : ℕ} (D : Dual m) (p q : Fin m → ℝ) (s : ℝ) :
    objective (fun i => p i + s * q i) D - averagedValue D p q s =
      s ^ 2 * (∑ i, D.alpha i * q i ^ 2) / 2 := by
  rw [objective_add]
  have hscale : objective (fun i => s * q i) D =
      s * dustLinear D q + s ^ 2 * (∑ i, ∑ j, D.beta i j * (q i * q j)) / 2 := by
    unfold objective dustLinear
    simp only [Finset.mul_sum, Finset.sum_div]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => by ring)
  have hcross : (∑ i, ∑ j, D.beta i j * (p i * (s * q j))) =
      s * ∑ i, ∑ j, D.beta i j * (p i * q j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hscale, hcross]
  unfold averagedValue dustPenalty
  ring

/-- A normalized assignment with atom weights at most η loses at most s²η/2. -/
theorem averaging_loss_bound {m : ℕ} (D : Dual m) (p q : Fin m → ℝ) (s η : ℝ)
    (halpha : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1)
    (hq₀ : ∀ i, 0 ≤ q i) (hqη : ∀ i, q i ≤ η) (hq : ∑ i, q i = 1) :
    0 ≤ objective (fun i => p i + s * q i) D - averagedValue D p q s ∧
      objective (fun i => p i + s * q i) D - averagedValue D p q s ≤ s ^ 2 * η / 2 := by
  rw [averaging_loss]
  have hnonneg : 0 ≤ ∑ i, D.alpha i * q i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (halpha i).1 (sq_nonneg _))
  have hbound : (∑ i, D.alpha i * q i ^ 2) ≤ η := by
    calc
      (∑ i, D.alpha i * q i ^ 2) ≤ ∑ i, η * q i := by
        apply Finset.sum_le_sum
        intro i _
        calc
          D.alpha i * q i ^ 2 ≤ q i ^ 2 := mul_le_of_le_one_left (sq_nonneg _) (halpha i).2
          _ ≤ η * q i := by nlinarith [mul_le_mul_of_nonneg_right (hqη i) (hq₀ i)]
      _ = η := by rw [← Finset.mul_sum, hq, mul_one]
  constructor
  · positivity
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (sq_nonneg s)) (by norm_num)

/-- Uniform assignments to a specified nonempty set of finite dust cells. -/
def uniformCellWeights {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ S then 1 / (S.card : ℝ) else 0

theorem uniformCellWeights_nonneg {m : ℕ} (S : Finset (Fin m)) (i : Fin m) :
    0 ≤ uniformCellWeights S i := by
  unfold uniformCellWeights
  split_ifs <;> positivity

theorem uniformCellWeights_le {m : ℕ} (S : Finset (Fin m)) (i : Fin m) :
    uniformCellWeights S i ≤ 1 / (S.card : ℝ) := by
  unfold uniformCellWeights
  split_ifs
  · exact le_rfl
  · positivity

theorem uniformCellWeights_total {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty) :
    ∑ i, uniformCellWeights S i = 1 := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  simp [uniformCellWeights, hc]

/-- The finite N-cell replacement has exact all-count feasibility and an
objective loss between zero and s²/(2N). Exterior labels are disjoint from the cells. -/
theorem uniform_cells_averaging {m : ℕ} (D : Dual m) (hD : DualFeasible D)
    (halpha : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) (hbeta : ∀ i j, D.beta i j ≤ 0)
    (S : Finset (Fin m)) (hS : S.Nonempty) (p : Fin m → ℝ) (s : ℝ) :
    (∀ (b : Fin m → ℕ), (∀ i ∈ S, b i = 0) → ∀ k : ℕ,
      repeatedCharge D b + (k : ℝ) * dustLinear D (uniformCellWeights S) +
        (k : ℝ) * (∑ i, ∑ j, D.beta i j * ((b i : ℝ) * uniformCellWeights S j)) -
        (k : ℝ) * (k - 1) * dustPenalty D (uniformCellWeights S) / 2 ≤ 1) ∧
    (0 ≤ objective (fun i => p i + s * uniformCellWeights S i) D -
      averagedValue D p (uniformCellWeights S) s) ∧
    (objective (fun i => p i + s * uniformCellWeights S i) D -
      averagedValue D p (uniformCellWeights S) s ≤ s ^ 2 / (2 * (S.card : ℝ))) := by
  have hq := uniformCellWeights_total S hS
  have hloss := averaging_loss_bound D p (uniformCellWeights S) s (1 / (S.card : ℝ))
    halpha (uniformCellWeights_nonneg S) (uniformCellWeights_le S) hq
  refine ⟨?_, hloss.1, ?_⟩
  · intro b hb k
    have hzero : (∑ i, D.alpha i * (b i : ℝ) * uniformCellWeights S i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i ∈ S
      · simp [hb i hi]
      · simp [uniformCellWeights, hi]
    have h := averaged_count_le_one D hD (fun i => (halpha i).1) hbeta
      (uniformCellWeights S) (uniformCellWeights_nonneg S) hq b k
    simpa only [hzero, mul_zero, sub_zero] using h
  · convert hloss.2 using 1; ring

/-- The quadratic dust coefficient is an average over all ordered type pairs,
using the default linear charge on repeated labels. -/
theorem dustPenalty_pair_average {m : ℕ} (D : Dual m) (q : Fin m → ℝ) :
    dustPenalty D q = ∑ i, ∑ j,
      (if i = j then D.alpha i else -D.beta i j) * (q i * q j) := by
  have hterm (i j : Fin m) :
      (if i = j then D.alpha i else -D.beta i j) * (q i * q j) =
      -D.beta i j * (q i * q j) + if j = i then D.alpha i * q i ^ 2 else 0 := by
    by_cases hij : i = j
    · subst j
      simp [D.beta_diag, pow_two]
    · simp [hij, Ne.symm hij]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    neg_mul, Finset.sum_neg_distrib]
  unfold dustPenalty
  ring

/-- Bounded finite duals average to bounded dust coefficients. -/
theorem dust_coefficients_bounded {m : ℕ} (D : Dual m) (q : Fin m → ℝ)
    (halpha : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1)
    (hbeta : ∀ i j, -1 ≤ D.beta i j ∧ D.beta i j ≤ 0)
    (hq₀ : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) :
    (0 ≤ dustLinear D q ∧ dustLinear D q ≤ 1) ∧
      (0 ≤ dustPenalty D q ∧ dustPenalty D q ≤ 1) := by
  have hlinear₀ : 0 ≤ dustLinear D q :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (halpha i).1 (hq₀ i))
  have hlinear₁ : dustLinear D q ≤ 1 := by
    rw [dustLinear, ← hq]
    exact Finset.sum_le_sum (fun i _ => mul_le_of_le_one_left (hq₀ i) (halpha i).2)
  refine ⟨⟨hlinear₀, hlinear₁⟩, ?_⟩
  rw [dustPenalty_pair_average]
  have hcoeff (i j : Fin m) :
      0 ≤ (if i = j then D.alpha i else -D.beta i j) ∧
      (if i = j then D.alpha i else -D.beta i j) ≤ 1 := by
    split_ifs
    · exact halpha i
    · exact ⟨neg_nonneg.mpr (hbeta i j).2, by linarith [(hbeta i j).1]⟩
  constructor
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hcoeff i j).1 (mul_nonneg (hq₀ i) (hq₀ j))))
  · calc
      (∑ i, ∑ j, (if i = j then D.alpha i else -D.beta i j) * (q i * q j)) ≤
          ∑ i, ∑ j, q i * q j := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum (fun j _ =>
          mul_le_of_le_one_left (mul_nonneg (hq₀ i) (hq₀ j)) (hcoeff i j).2)
      _ = 1 := by simp_rw [← Finset.mul_sum, hq, mul_one]; exact hq

/-- The actual finite selector value has an averaged all-count witness with
the explicit N-cell error. This is an algebraic dual statement, not physical primal attainment. -/
theorem exists_uniform_cell_witness {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (p : Fin m → ℝ) (s : ℝ)
    (hp : ∀ i, 0 ≤ p i + s * uniformCellWeights S i ∧
      p i + s * uniformCellWeights S i ≤ 1) :
    ∃ D : Dual m,
      (∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) ∧
      (∀ i j, -min (D.alpha i) (D.alpha j) ≤ D.beta i j ∧ D.beta i j ≤ 0) ∧
      (∀ b : Fin m → ℕ, (∀ i ∈ S, b i = 0) → ∀ k : ℕ,
        repeatedCharge D b + (k : ℝ) * dustLinear D (uniformCellWeights S) +
          (k : ℝ) * (∑ i, ∑ j, D.beta i j * ((b i : ℝ) * uniformCellWeights S j)) -
          (k : ℝ) * (k - 1) * dustPenalty D (uniformCellWeights S) / 2 ≤ 1) ∧
      (0 ≤ dustLinear D (uniformCellWeights S) ∧ dustLinear D (uniformCellWeights S) ≤ 1) ∧
      (0 ≤ dustPenalty D (uniformCellWeights S) ∧ dustPenalty D (uniformCellWeights S) ≤ 1) ∧
      (0 ≤ value (fun i => p i + s * uniformCellWeights S i) -
        averagedValue D p (uniformCellWeights S) s) ∧
      (value (fun i => p i + s * uniformCellWeights S i) -
        averagedValue D p (uniformCellWeights S) s ≤ s ^ 2 / (2 * (S.card : ℝ))) := by
  obtain ⟨D, hD, halpha, hbeta⟩ := exists_bounded_optimal
    (fun i => p i + s * uniformCellWeights S i) hp
  have hb : ∀ i j, -1 ≤ D.beta i j ∧ D.beta i j ≤ 0 := by
    intro i j
    refine ⟨?_, (hbeta i j).2⟩
    have hmin : min (D.alpha i) (D.alpha j) ≤ 1 := (min_le_left _ _).trans (halpha i).2
    linarith [(hbeta i j).1]
  have havg := uniform_cells_averaging D hD.1 halpha (fun i j => (hbeta i j).2) S hS p s
  have hbox := dust_coefficients_bounded D (uniformCellWeights S) halpha hb
    (uniformCellWeights_nonneg S) (uniformCellWeights_total S hS)
  have hvalue := optimal_objective_eq_value (fun i => p i + s * uniformCellWeights S i) hp D hD
  rw [hvalue] at havg
  exact ⟨D, halpha, hbeta, havg.1, hbox.1, hbox.2, havg.2⟩

end Erdos1017.Selector
