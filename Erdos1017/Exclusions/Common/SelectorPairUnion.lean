module

public import Erdos1017.FractionalLimit.Selector
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Two-pair union on the sum-two cube

The elementary two-pair union construction on the closed sum-two cube.
All auxiliary finite laws and moment calculations are internal to this module.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector

open scoped BigOperators

private def expect {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) : ℝ := ∑ x, w x * f x

private theorem expect_add {Ω : Type*} [Fintype Ω] (w f g : Ω → ℝ) :
    expect w (fun x => f x + g x) = expect w f + expect w g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

private theorem expect_sub {Ω : Type*} [Fintype Ω] (w f g : Ω → ℝ) :
    expect w (fun x => f x - g x) = expect w f - expect w g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

private theorem expect_independent {Ω : Type*} [Fintype Ω] (w f g : Ω → ℝ) :
    expect (fun z : Ω × Ω => w z.1 * w z.2) (fun z => f z.1 * g z.2) =
      expect w f * expect w g := by
  simp only [expect, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

private theorem bit_or (a b : Bool) : bit (a || b) = bit a + bit b - bit a * bit b := by
  cases a <;> cases b <;> norm_num [bit]

private theorem union_moments {Ω : Type*} [Fintype Ω] {n : ℕ}
    (w : Ω → ℝ) (T : Ω → Selection n) (p : Fin n → ℝ)
    (htotal : expect w (fun _ => 1) = 1)
    (hfirst : ∀ i, expect w (fun x => bit (T x i)) = p i) (i j : Fin n) :
    expect (fun z : Ω × Ω => w z.1 * w z.2)
        (fun z => bit (T z.1 i || T z.2 i)) = 2 * p i - (p i) ^ 2 ∧
      expect (fun z : Ω × Ω => w z.1 * w z.2)
        (fun z => bit (T z.1 i || T z.2 i) * bit (T z.1 j || T z.2 j)) =
        2 * p i * p j + 2 * (1 - p i - p j) *
          expect w (fun x => bit (T x i) * bit (T x j)) +
          (expect w (fun x => bit (T x i) * bit (T x j))) ^ 2 := by
  have heq : ∀ a b c d : ℝ,
      (a + b - a * b) * (c + d - c * d) =
        (a * c) * 1 + 1 * (b * d) + a * d + c * b -
          (a * c) * d - (a * c) * b - a * (b * d) - c * (b * d) + (a * c) * (b * d) := by
    intros
    ring
  have hleft : expect (fun z : Ω × Ω => w z.1 * w z.2)
      (fun z => bit (T z.1 i) * 1) = p i := by
    rw [expect_independent w (fun x => bit (T x i)) (fun _ => 1), htotal, hfirst]
    ring
  have hright : expect (fun z : Ω × Ω => w z.1 * w z.2)
      (fun z => 1 * bit (T z.2 i)) = p i := by
    rw [expect_independent w (fun _ => 1) (fun x => bit (T x i)), htotal, hfirst]
    ring
  constructor
  · simp_rw [bit_or]
    rw [expect_sub, expect_add]
    have hl : expect (fun z : Ω × Ω => w z.1 * w z.2)
        (fun z => bit (T z.1 i)) = p i := by simpa using hleft
    have hr : expect (fun z : Ω × Ω => w z.1 * w z.2)
        (fun z => bit (T z.2 i)) = p i := by simpa using hright
    rw [hl, hr, expect_independent w (fun x => bit (T x i)) (fun x => bit (T x i)), hfirst]
    ring
  · simp_rw [bit_or, heq, expect_add, expect_sub]
    simp_rw [expect_add]
    rw [expect_independent w (fun x => bit (T x i) * bit (T x j)) (fun _ => 1),
      expect_independent w (fun _ => 1) (fun x => bit (T x i) * bit (T x j)),
      expect_independent w (fun x => bit (T x i)) (fun x => bit (T x j)),
      expect_independent w (fun x => bit (T x j)) (fun x => bit (T x i)),
      expect_independent w (fun x => bit (T x i) * bit (T x j)) (fun x => bit (T x j)),
      expect_independent w (fun x => bit (T x i) * bit (T x j)) (fun x => bit (T x i)),
      expect_independent w (fun x => bit (T x i)) (fun x => bit (T x i) * bit (T x j)),
      expect_independent w (fun x => bit (T x j)) (fun x => bit (T x i) * bit (T x j)),
      expect_independent w (fun x => bit (T x i) * bit (T x j)) (fun x => bit (T x i) * bit (T x j)),
      htotal, hfirst, hfirst]
    ring

private theorem union_pair_bound (a b J : ℝ) (ha : 0 ≤ a ∧ a < 1)
    (hb : 0 ≤ b ∧ b < 1) (hJ : 0 ≤ J)
    (hbound : J ≤ a * b / (1 + (1 - a) * (1 - b))) :
    2 * a * b + 2 * (1 - a - b) * J + J ^ 2 ≤ 3 * a * b := by
  let d := 1 + (1 - a) * (1 - b)
  have hd : 0 < d := by
    have : 0 ≤ (1 - a) * (1 - b) := mul_nonneg (by linarith) (by linarith)
    dsimp [d]
    linarith
  have hab : 0 ≤ a * b := mul_nonneg ha.1 hb.1
  have hk : 0 ≤ a * b / d := div_nonneg hab hd.le
  have hconv : J ^ 2 ≤ J * (a * b / d) := by
    nlinarith [mul_nonneg hJ (sub_nonneg.mpr hbound)]
  have hend : 2 * (1 - a - b) * (a * b / d) + (a * b / d) ^ 2 ≤ a * b := by
    have hid : (a * b - (2 * (1 - a - b) * (a * b / d) + (a * b / d) ^ 2)) * d ^ 2 =
        a * b * ((a + b) * (2 - a - b) + a * b + (a * b) ^ 2) := by
      field_simp [ne_of_gt hd]
      dsimp [d]
      ring
    have hn : 0 ≤ a * b * ((a + b) * (2 - a - b) + a * b + (a * b) ^ 2) := by
      apply mul_nonneg hab
      have : 0 ≤ (a + b) * (2 - a - b) := mul_nonneg (by linarith) (by linarith)
      positivity
    nlinarith [sq_pos_of_pos hd]
  by_cases hkzero : a * b / d = 0
  · have : J = 0 := le_antisymm (hbound.trans hkzero.le) hJ
    rw [this]
    nlinarith
  · have hkpos : 0 < a * b / d := lt_of_le_of_ne hk (Ne.symm hkzero)
    have hs : 2 * (1 - a - b) + a * b / d ≤ d := by
      have : a * b / d * d = a * b := div_mul_cancel₀ _ (ne_of_gt hd)
      nlinarith
    have hscale := mul_le_mul_of_nonneg_left hs hJ
    have hlast := mul_le_mul_of_nonneg_right hbound hd.le
    have : a * b / d * d = a * b := div_mul_cancel₀ _ (ne_of_gt hd)
    nlinarith

private def pairSelection {n : ℕ} (z : Fin n × Fin n) : Selection n :=
  fun i => decide (z.1 = i ∨ z.2 = i)

private theorem pair_first {n : ℕ} (w : Fin n × Fin n → ℝ)
    (hdiag : ∀ i, w (i, i) = 0) (i : Fin n) :
    expect w (fun z => bit (pairSelection z i)) =
      (∑ j, w (i, j)) + ∑ j, w (j, i) := by
  classical
  have hterm : ∀ z, w z * bit (pairSelection z i) =
      (if z.1 = i then w z else 0) + (if z.2 = i then w z else 0) := by
    rintro ⟨a, b⟩
    by_cases ha : a = i <;> by_cases hb : b = i <;>
      simp [pairSelection, bit, ha, hb, hdiag]
  simp_rw [expect, hterm, Finset.sum_add_distrib]
  simp [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

private theorem pair_second {n : ℕ} (w : Fin n × Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    expect w (fun z => bit (pairSelection z i) * bit (pairSelection z j)) =
      w (i, j) + w (j, i) := by
  classical
  have hterm : ∀ z, w z * (bit (pairSelection z i) * bit (pairSelection z j)) =
      (if z.1 = i then if z.2 = j then w z else 0 else 0) +
        (if z.1 = j then if z.2 = i then w z else 0 else 0) := by
    rintro ⟨a, b⟩
    by_cases hai : a = i <;> by_cases haj : a = j <;>
      by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      simp_all [pairSelection, bit]
  simp_rw [expect, hterm, Finset.sum_add_distrib]
  simp [Fintype.sum_prod_type]

private def pairWeight {n : ℕ} (p : Fin n → ℝ) (z : Fin n × Fin n) : ℝ :=
  if z.1 = z.2 then 0 else
    (p z.1 / (1 - p z.1)) * p z.2 / ((∑ i, p i / (1 - p i)) + 2)

private theorem interior_law {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i < 1) (hsum : ∑ i, p i = 2) :
    (∀ z, 0 ≤ pairWeight p z) ∧
    expect (pairWeight p) (fun _ => 1) = 1 ∧
    (∀ i, expect (pairWeight p) (fun z => bit (pairSelection z i)) = p i) ∧
    ∀ i j, i ≠ j →
      expect (pairWeight p) (fun z => bit (pairSelection z i) * bit (pairSelection z j)) ≤
        p i * p j / (1 + (1 - p i) * (1 - p j)) := by
  classical
  let r := fun i => p i / (1 - p i)
  let C := (∑ i, r i) + 2
  have hr : ∀ i, 0 ≤ r i := fun i => div_nonneg (hp i).1 (by linarith [(hp i).2])
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hr i)
    dsimp [C]
    linarith
  have hden : ∀ i, 1 - p i ≠ 0 := fun i => ne_of_gt (by linarith [(hp i).2])
  have hrow : ∀ i, (∑ j, pairWeight p (i, j)) = r i * (2 - p i) / C := by
    intro i
    have hterm : ∀ j, pairWeight p (i, j) = r i / C * p j - if j = i then r i / C * p i else 0 := by
      intro j
      by_cases h : i = j
      · subst j; simp [pairWeight]
      · simp [pairWeight, h, Ne.symm h, r, C]; ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib]
    simp [← Finset.mul_sum, hsum]
    ring
  have hcol : ∀ i, (∑ j, pairWeight p (j, i)) = (∑ j, r j) * p i / C - r i * p i / C := by
    intro i
    have hterm : ∀ j, pairWeight p (j, i) = r j * p i / C - if j = i then r i * p i / C else 0 := by
      intro j
      by_cases h : j = i
      · subst j; simp [pairWeight]
      · simp [pairWeight, h, r, C]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib]
    simp [← Finset.sum_div, ← Finset.sum_mul]
  have hfirst : ∀ i, expect (pairWeight p) (fun z => bit (pairSelection z i)) = p i := by
    intro i
    rw [pair_first _ (by intro i; simp [pairWeight]), hrow, hcol]
    rw [← sub_div, ← add_div]
    apply (div_eq_iff (ne_of_gt hC)).mpr
    have hri : r i * (1 - p i) = p i := div_mul_cancel₀ _ (hden i)
    dsimp [C]
    nlinarith
  refine ⟨?_, ?_, hfirst, ?_⟩
  · intro z
    unfold pairWeight
    split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (hr _) (hp _).1) hC.le
  · have hterm : ∀ i, r i * (2 - p i) = p i + r i := by
      intro i
      dsimp [r]
      field_simp [hden i]
      ring
    simp only [expect, mul_one, Fintype.sum_prod_type]
    simp_rw [hrow, ← Finset.sum_div, hterm]
    rw [Finset.sum_add_distrib, hsum]
    dsimp [C]
    apply (div_eq_one_iff_eq (ne_of_gt hC)).mpr
    ring
  · intro i j hij
    rw [pair_second _ i j hij]
    have hrat : ∀ k, p k ≤ r k := by
      intro k
      dsimp [r]
      apply (le_div_iff₀ (by linarith [(hp k).2])).mpr
      nlinarith [(hp k).1]
    have hrest : r i + r j + (2 - p i - p j) ≤ ∑ k, r k := by
      have hnonneg : ∀ k, 0 ≤ r k - p k := fun k => sub_nonneg.mpr (hrat k)
      have htwo := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({i, j} : Finset (Fin n)))
        (fun k _ _ => hnonneg k)
      simp [hij, Finset.sum_sub_distrib, hsum] at htwo
      linarith
    have hbound : (1 - p i) + (1 - p j) + (1 - p i) * (1 - p j) * ((1 - p i) + (1 - p j)) ≤
        C * ((1 - p i) * (1 - p j)) := by
      calc
        _ = (r i + r j + (2 - p i - p j) + 2) * ((1 - p i) * (1 - p j)) := by
          dsimp [r]
          field_simp [hden i, hden j]
          ring
        _ ≤ C * ((1 - p i) * (1 - p j)) := by
          apply mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
          exact mul_nonneg (by linarith [(hp i).2]) (by linarith [(hp j).2])
    have hd : 0 < 1 + (1 - p i) * (1 - p j) := by
      have : 0 ≤ (1 - p i) * (1 - p j) := mul_nonneg (by linarith [(hp i).2]) (by linarith [(hp j).2])
      linarith
    have hc : 0 < (1 - p i) * (1 - p j) := mul_pos (by linarith [(hp i).2]) (by linarith [(hp j).2])
    simp only [pairWeight, hij, Ne.symm hij, ↓reduceIte]
    change r i * p j / C + r j * p i / C ≤ p i * p j / (1 + (1 - p i) * (1 - p j))
    rw [← add_div]
    apply (div_le_div_iff₀ hC hd).mpr
    apply (mul_le_mul_iff_left₀ hc).mp
    have hidentity : ((1 - p i) * (1 - p j)) * ((r i * p j + r j * p i) * (1 + (1 - p i) * (1 - p j))) =
        (p i * p j) * ((1 - p i) + (1 - p j) + (1 - p i) * (1 - p j) * ((1 - p i) + (1 - p j))) := by
      dsimp [r]
      field_simp [hden i, hden j]
      ring
    rw [mul_comm _ ((1 - p i) * (1 - p j)), hidentity]
    calc
      _ ≤ (p i * p j) * (C * ((1 - p i) * (1 - p j))) :=
        mul_le_mul_of_nonneg_left hbound (mul_nonneg (hp i).1 (hp j).1)
      _ = _ := by ring

private def boundaryWeight {n : ℕ} (p : Fin n → ℝ) (r : Fin n)
    (z : Fin n × Fin n) : ℝ := if z.1 = r ∧ z.2 ≠ r then p z.2 else 0

private theorem boundary_law {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc 0 1) (hsum : ∑ i, p i = 2)
    (r : Fin n) (hr : p r = 1) :
    (∀ z, 0 ≤ boundaryWeight p r z) ∧
    expect (boundaryWeight p r) (fun _ => 1) = 1 ∧
    (∀ i, expect (boundaryWeight p r) (fun z => bit (pairSelection z i)) = p i) ∧
    ∀ i j, i ≠ j →
      2 * p i * p j + 2 * (1 - p i - p j) *
        expect (boundaryWeight p r) (fun z => bit (pairSelection z i) * bit (pairSelection z j)) +
        (expect (boundaryWeight p r) (fun z => bit (pairSelection z i) * bit (pairSelection z j))) ^ 2 ≤
        3 * p i * p j := by
  classical
  have htail : (∑ i, if i = r then 0 else p i) = 1 := by
    have heq : ∀ i, (if i = r then 0 else p i) = p i - if i = r then p r else 0 := by
      intro i
      by_cases h : i = r <;> simp [h]
    simp_rw [heq]
    norm_num [Finset.sum_sub_distrib, hsum, hr]
  have hrow : ∀ i, (∑ j, boundaryWeight p r (i, j)) = if i = r then 1 else 0 := by
    intro i
    by_cases h : i = r
    · subst i
      simpa [boundaryWeight, ite_not] using htail
    · simp [boundaryWeight, h]
  have hcol : ∀ i, (∑ j, boundaryWeight p r (j, i)) = if i = r then 0 else p i := by
    intro i
    by_cases h : i = r <;> simp [boundaryWeight, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    unfold boundaryWeight
    split_ifs
    · exact (hp _).1
    · exact le_rfl
  · simp only [expect, mul_one, Fintype.sum_prod_type]
    simp_rw [hrow]
    simp
  · intro i
    rw [pair_first _ (by intro i; simp [boundaryWeight]), hrow, hcol]
    by_cases h : i = r <;> simp [h, hr]
  · intro i j hij
    rw [pair_second _ i j hij]
    by_cases hi : i = r
    · subst i
      have hj : j ≠ r := Ne.symm hij
      simp [boundaryWeight, hj, hr]
      nlinarith [sq_nonneg (p j), (hp j).1]
    · by_cases hj : j = r
      · subst j
        simp [boundaryWeight, hi, hr]
        nlinarith [sq_nonneg (p i), (hp i).1]
      · simp [boundaryWeight, hi, hj]
        nlinarith [mul_nonneg (hp i).1 (hp j).1]

private theorem exists_union_law {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc 0 1) (hsum : ∑ i, p i = 2) :
    ∃ (w : ((Fin n × Fin n) × (Fin n × Fin n)) → ℝ)
      (U : ((Fin n × Fin n) × (Fin n × Fin n)) → Selection n),
      (∀ z, 0 ≤ w z) ∧ expect w (fun _ => 1) = 1 ∧
      (∀ i, expect w (fun z => bit (U z i)) = 2 * p i - (p i) ^ 2) ∧
      ∀ i j, i ≠ j → expect w (fun z => bit (U z i) * bit (U z j)) ≤ 3 * p i * p j := by
  classical
  have hex : ∃ (w : Fin n × Fin n → ℝ),
      (∀ z, 0 ≤ w z) ∧ expect w (fun _ => 1) = 1 ∧
      (∀ i, expect w (fun z => bit (pairSelection z i)) = p i) ∧
      ∀ i j, i ≠ j →
        2 * p i * p j + 2 * (1 - p i - p j) * expect w (fun z => bit (pairSelection z i) * bit (pairSelection z j)) +
          (expect w (fun z => bit (pairSelection z i) * bit (pairSelection z j))) ^ 2 ≤ 3 * p i * p j := by
    by_cases hunit : ∃ r, p r = 1
    · obtain ⟨r, hr⟩ := hunit
      exact ⟨boundaryWeight p r, boundary_law p hp hsum r hr⟩
    · have hpi : ∀ i, 0 ≤ p i ∧ p i < 1 := by
        intro i
        exact ⟨(hp i).1, lt_of_le_of_ne (hp i).2 (by intro h; exact hunit ⟨i, h⟩)⟩
      obtain ⟨hw, ht, hf, hp2⟩ := interior_law p hpi hsum
      refine ⟨pairWeight p, hw, ht, hf, ?_⟩
      intro i j hij
      apply union_pair_bound (p i) (p j) _ (hpi i) (hpi j) _ (hp2 i j hij)
      exact Finset.sum_nonneg (fun z _ => mul_nonneg (hw z) (by unfold bit; positivity))
  obtain ⟨w, hw, ht, hf, hp2⟩ := hex
  refine ⟨fun z => w z.1 * w z.2,
    fun z i => pairSelection z.1 i || pairSelection z.2 i, ?_, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (hw _) (hw _)
  · have h := expect_independent w (fun _ => 1) (fun _ => 1)
    simpa [ht] using h
  · intro i
    exact (union_moments w pairSelection p ht hf i i).1
  · intro i j hij
    rw [(union_moments w pairSelection p ht hf i j).2]
    exact hp2 i j hij

/-- Two independent distinct pairs and their Boolean union give the four-draw bound. -/
theorem three_objective_sub_linear_sub_square_le_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc 0 1) (hsum : ∑ i, p i = 2)
    (D : Dual n) (hD : DualFeasible D)
    (hα : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1)
    (hβ : ∀ i j, D.beta i j ≤ 0) :
    3 * objective p D - (∑ i, D.alpha i * p i) - (∑ i, (p i) ^ 2) ≤ 1 := by
  obtain ⟨w, U, hw, ht, hf, hp2⟩ := exists_union_law p hp hsum
  have hupper : expect w (fun z => quadratic D (U z)) ≤ 1 := by
    rw [← ht]
    exact Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hD (U z)) (hw z))
  have hfirst : ∀ i, (∑ z, w z * (D.alpha i * bit (U z i))) = D.alpha i * (2 * p i - (p i) ^ 2) := by
    intro i
    simp_rw [mul_left_comm (w _) (D.alpha i), ← Finset.mul_sum]
    exact congrArg (fun x => D.alpha i * x) (hf i)
  have hpair : ∀ i j, (∑ z, w z * (D.beta i j * (bit (U z i) * bit (U z j)))) =
      D.beta i j * expect w (fun z => bit (U z i) * bit (U z j)) := by
    intro i j
    simp_rw [mul_left_comm (w _) (D.beta i j), ← Finset.mul_sum]
    rfl
  have hidentity : expect w (fun z => quadratic D (U z)) =
      (∑ i, D.alpha i * (2 * p i - (p i) ^ 2)) +
        (∑ i, ∑ j, D.beta i j * expect w (fun z => bit (U z i) * bit (U z j))) / 2 := by
    unfold expect quadratic objective
    simp only [mul_add, mul_div, Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => hfirst i)
    · rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [expect, Finset.mul_sum] using hpair i j
  have hlinear : 2 * (∑ i, D.alpha i * p i) - (∑ i, (p i) ^ 2) ≤
      ∑ i, D.alpha i * (2 * p i - (p i) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_le_mul_of_nonneg_right (hα i).2 (sq_nonneg (p i))]
  have hquadratic : 3 * (∑ i, ∑ j, D.beta i j * (p i * p j)) ≤
      ∑ i, ∑ j, D.beta i j * expect w (fun z => bit (U z i) * bit (U z j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      simp [D.beta_diag]
    · have h := mul_le_mul_of_nonpos_left (hp2 i j hij) (hβ i j)
      nlinarith
  unfold objective
  linarith

end Erdos1017.Selector
