module

public import Erdos1017.Multipartite.Dust.DustSingleSplit

/-!
# Completing one head type into dust

`completeType` averages completed mass of one head with the original dust while
keeping its retained atom, with an explicit new self penalty; the full repeat
tests imply every averaged dust-count constraint, coefficients stay in the unit
box, and completion removes precisely the new internal pair charge.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators

/-- Deleting the Boolean occurrence of one type removes exactly its exterior
row, including its interactions with the old dust. -/
theorem charge_erase_head {m : ℕ} (C : Coefficients m) (i : Fin m)
    (X : Selector.Selection m) (k : ℕ) :
    charge C X k = charge C (eraseSelection X i) k + Selector.bit (X i) *
      (head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * Selector.bit (X j) -
        (k : ℝ) * incident C i) := by
  let p : Fin m → ℝ := fun j => Selector.bit (eraseSelection X i j)
  have hpi : p i = 0 := by simp [p, eraseSelection, Selector.bit]
  have hback : Function.update p i (Selector.bit (X i)) = fun j => Selector.bit (X j) := by
    funext j
    by_cases hj : j = i <;> simp [p, eraseSelection, hj, Function.update_of_ne]
  have hrow : (∑ j, (DustCellRestriction.headDual C).beta i j * p j) =
      ∑ j, (DustCellRestriction.headDual C).beta i j * Selector.bit (X j) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j
      simp only [(DustCellRestriction.headDual C).beta_diag, zero_mul]
    · simp [p, eraseSelection, hj]
  have hobj : objective (Function.update p i (Selector.bit (X i))) (k : ℝ) C =
      objective p (k : ℝ) C + Selector.bit (X i) *
        (head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * p j -
          (k : ℝ) * incident C i) := by
    rw [objective_add_head C i p hpi]
    conv_rhs => rw [objective_dust_split C p, DustCellRestriction.headDual_objective]
    ring
  rw [hback, hrow] at hobj
  rw [DustCellBridge.charge_eq_objective, DustCellBridge.charge_eq_objective, hobj]
  dsimp only [p]
  ring

/-- Average newly completed mass of one head with the old dust, while keeping
its possible retained independent atom. Its new self penalty is explicit. -/
def completeType {m : ℕ} (C : Coefficients m) (i : Fin m) (P : ℝ)
    (q : Fin 2 → ℝ) : Coefficients m
  | .inl j => head C j
  | .inr (.inl (j, k)) => pair C j k
  | .inr (.inr (.inl j)) =>
      (if j = i then P else -(DustCellRestriction.headDual C).beta i j) * q 0 + incident C j * q 1
  | .inr (.inr (.inr false)) => head C i * q 0 + linear C * q 1
  | .inr (.inr (.inr true)) =>
      P * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2

/-- The exact charge is the two-type average, with the retained atom paying
its repeat penalty to every newly completed point of the same type. -/
theorem completeType_charge {m : ℕ} (C : Coefficients m) (i : Fin m) (P : ℝ)
    (q : Fin 2 → ℝ) (X : Selector.Selection m) (k : ℕ) :
    charge (completeType C i P q) X k = charge C X 0 +
      (k : ℝ) * ((head C i + ∑ j, (DustCellRestriction.headDual C).beta i j *
          Selector.bit (X j) - P * Selector.bit (X i)) * q 0 +
        (linear C - ∑ j, incident C j * Selector.bit (X j)) * q 1) -
      (k : ℝ) * ((k : ℝ) - 1) *
        (P * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2) / 2 := by
  have hinc : (∑ j, incident (completeType C i P q) j * Selector.bit (X j)) =
      (P * Selector.bit (X i) -
        ∑ j, (DustCellRestriction.headDual C).beta i j * Selector.bit (X j)) * q 0 +
        (∑ j, incident C j * Selector.bit (X j)) * q 1 := by
    have ht (j : Fin m) : incident (completeType C i P q) j * Selector.bit (X j) =
        (if j = i then P * Selector.bit (X i) else 0) * q 0 -
          (DustCellRestriction.headDual C).beta i j * Selector.bit (X j) * q 0 +
          incident C j * Selector.bit (X j) * q 1 := by
      by_cases hj : j = i
      · subst j
        simp only [incident, completeType, ↓reduceIte,
          (DustCellRestriction.headDual C).beta_diag, zero_mul]
        ring
      · simp only [incident, completeType, hj, ↓reduceIte, zero_mul, zero_sub]
        ring
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  unfold charge
  rw [hinc]
  simp only [head, pair, linear, penalty, completeType, Nat.cast_zero, zero_mul,
    mul_zero, add_zero]
  ring

/-- A retained Boolean copy and newly completed copies use the same full
repeat constraint; the old dust count remains unrestricted. -/
theorem retained_type_count_test {m : ℕ} (C : Coefficients m) (i : Fin m) (P : ℝ)
    (htest : ∀ X : Selector.Selection m, X i = false → ∀ r d : ℕ,
      (r : ℝ) * (head C i + ∑ j, (DustCellRestriction.headDual C).beta i j *
          Selector.bit (X j) - (d : ℝ) * incident C i) + charge C X d -
        P * r * ((r : ℝ) - 1) / 2 ≤ 1)
    (X : Selector.Selection m) (n d : ℕ) :
    charge C X 0 + (n : ℝ) *
      (head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * Selector.bit (X j) -
        P * Selector.bit (X i)) +
      (d : ℝ) * (linear C - ∑ j, incident C j * Selector.bit (X j)) -
      incident C i * n * d - P * n * ((n : ℝ) - 1) / 2 -
      penalty C * d * ((d : ℝ) - 1) / 2 ≤ 1 := by
  have hrow : (∑ j, (DustCellRestriction.headDual C).beta i j *
      Selector.bit (eraseSelection X i j)) =
      ∑ j, (DustCellRestriction.headDual C).beta i j * Selector.bit (X j) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j
      simp only [(DustCellRestriction.headDual C).beta_diag, zero_mul]
    · simp [eraseSelection, hj]
  have hdel := charge_erase_head C i X d
  have hdust : charge C X d = charge C X 0 +
      (d : ℝ) * (linear C - ∑ j, incident C j * Selector.bit (X j)) -
      penalty C * d * ((d : ℝ) - 1) / 2 := by
    unfold charge
    norm_num
  cases hXi : X i
  · have h := htest (eraseSelection X i) (by simp [eraseSelection]) n d
    rw [hrow] at h
    have hb : Selector.bit (X i) = 0 := by simp [hXi, Selector.bit]
    simp only [hb, zero_mul, add_zero] at hdel
    simp only [show Selector.bit false = 0 from rfl, mul_zero, sub_zero]
    nlinarith [h]
  · have h := htest (eraseSelection X i) (by simp [eraseSelection]) (n + 1) d
    rw [hrow] at h
    have hb : Selector.bit (X i) = 1 := by simp [hXi, Selector.bit]
    simp only [hb, one_mul] at hdel
    simp only [show Selector.bit true = 1 from rfl, mul_one]
    push_cast at h
    nlinarith [h]

/-- The full repeat tests imply every averaged dust-count constraint. -/
theorem completeType_tests {m : ℕ} (C : Coefficients m) (i : Fin m) (P : ℝ)
    (htest : ∀ X : Selector.Selection m, X i = false → ∀ r d : ℕ,
      (r : ℝ) * (head C i + ∑ j, (DustCellRestriction.headDual C).beta i j *
          Selector.bit (X j) - (d : ℝ) * incident C i) + charge C X d -
        P * r * ((r : ℝ) - 1) / 2 ≤ 1)
    (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1) :
    ∀ X k, charge (completeType C i P q) X k ≤ 1 := by
  intro X k
  rw [completeType_charge]
  apply two_type_average_le_one q hq₀ hq
  exact retained_type_count_test C i P htest X

/-- Averaging bounded self and pair penalties keeps every coefficient in the
same unit box. -/
theorem completeType_box {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m)
    (i : Fin m) (P : ℝ) (hP : 0 ≤ P ∧ P ≤ 1)
    (q : Fin 2 → ℝ) (hq₀ : ∀ j, 0 ≤ q j) (hq : ∑ j, q j = 1) :
    completeType C i P q ∈ Set.Icc 0 1 := by
  have hqsum : q 0 + q 1 = 1 := by simpa [Fin.sum_univ_two] using hq
  have hcoef (c : Coordinate m) : 0 ≤ C c ∧ C c ≤ 1 := ⟨hC.1.1 c, hC.1.2 c⟩
  have hmix (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
      0 ≤ a * q 0 + b * q 1 ∧ a * q 0 + b * q 1 ≤ 1 := by
    constructor
    · exact add_nonneg (mul_nonneg ha.1 (hq₀ 0)) (mul_nonneg hb.1 (hq₀ 1))
    · nlinarith [mul_le_mul_of_nonneg_right ha.2 (hq₀ 0),
        mul_le_mul_of_nonneg_right hb.2 (hq₀ 1)]
  have hcross (j : Fin m) : 0 ≤ (if j = i then P else
      -(DustCellRestriction.headDual C).beta i j) ∧
      (if j = i then P else -(DustCellRestriction.headDual C).beta i j) ≤ 1 := by
    split_ifs
    · exact hP
    · dsimp only [DustCellRestriction.headDual]
      rw [neg_neg]
      split_ifs <;> first | exact hcoef _ | exact ⟨le_rfl, zero_le_one⟩
  have hc : 0 ≤ incident C i ∧ incident C i ≤ 1 := hcoef (.inr (.inr (.inl i)))
  have hp : 0 ≤ penalty C ∧ penalty C ≤ 1 := hcoef (.inr (.inr (.inr true)))
  have hpen : 0 ≤ P * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2 ∧
      P * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2 ≤ 1 := by
    constructor
    · exact add_nonneg (add_nonneg (mul_nonneg hP.1 (sq_nonneg _))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.1) (hq₀ 0)) (hq₀ 1)))
        (mul_nonneg hp.1 (sq_nonneg _))
    · have hprod := mul_le_mul_of_nonneg_right hc.2 (mul_nonneg (hq₀ 0) (hq₀ 1))
      have hsquare : q 0 ^ 2 + 2 * q 0 * q 1 + q 1 ^ 2 = 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hP.2 (sq_nonneg (q 0)),
        mul_le_mul_of_nonneg_right hp.2 (sq_nonneg (q 1))]
  have hb (c : Coordinate m) : 0 ≤ completeType C i P q c ∧ completeType C i P q c ≤ 1 := by
    rcases c with j | (⟨j, l⟩ | (j | b))
    · exact hcoef (.inl j)
    · exact hcoef (.inr (.inl (j, l)))
    · exact hmix _ _ (hcross j) (hcoef (.inr (.inr (.inl j))))
    · cases b
      · exact hmix _ _ (hcoef (.inl i)) (hcoef (.inr (.inr (.inr false))))
      · exact hpen
  exact ⟨fun c => (hb c).1, fun c => (hb c).2⟩

/-- The averaged objective retains the full original head objective and
uses the repeat penalty on new dust points of the retained type. -/
theorem completeType_objective {m : ℕ} (C : Coefficients m) (i : Fin m) (P : ℝ)
    (q : Fin 2 → ℝ) (p : Fin m → ℝ) (s : ℝ) :
    objective p s (completeType C i P q) = objective p 0 C +
      s * ((head C i + ∑ j, (DustCellRestriction.headDual C).beta i j * p j -
          P * p i) * q 0 + (linear C - ∑ j, incident C j * p j) * q 1) -
      (P * q 0 ^ 2 + 2 * incident C i * q 0 * q 1 + penalty C * q 1 ^ 2) * s ^ 2 / 2 := by
  have hinc : (∑ j, incident (completeType C i P q) j * p j) =
      (P * p i - ∑ j, (DustCellRestriction.headDual C).beta i j * p j) * q 0 +
        (∑ j, incident C j * p j) * q 1 := by
    have ht (j : Fin m) : incident (completeType C i P q) j * p j =
        (if j = i then P * p i else 0) * q 0 -
          (DustCellRestriction.headDual C).beta i j * p j * q 0 +
          incident C j * p j * q 1 := by
      by_cases hj : j = i
      · subst j
        simp only [incident, completeType, ↓reduceIte,
          (DustCellRestriction.headDual C).beta_diag, zero_mul]
        ring
      · simp only [incident, completeType, hj, ↓reduceIte, zero_mul, zero_sub]
        ring
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  unfold objective
  rw [← Finset.sum_mul, hinc]
  simp only [head, pair, linear, penalty, completeType, mul_zero, add_zero,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_div, sub_zero]
  ring

/-- Completion removes precisely the new internal pair charge, including
pairs between a retained atom and completed mass of the same type. -/
theorem completeType_loss {m : ℕ} (C : Coefficients m) (i : Fin m) (P : ℝ)
    (q : Fin 2 → ℝ) (p : Fin m → ℝ) (hpi : p i = 0) (x s : ℝ) :
    objective (Function.update p i (x + s * q 0)) (s * q 1) C -
      objective (Function.update p i x) s (completeType C i P q) =
        P * (x * (s * q 0) + (s * q 0) ^ 2 / 2) := by
  have hrow : (∑ j, (DustCellRestriction.headDual C).beta i j *
      Function.update p i x j) = ∑ j, (DustCellRestriction.headDual C).beta i j * p j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j
      simp only [(DustCellRestriction.headDual C).beta_diag, zero_mul]
    · simp [Function.update_of_ne, hj]
  have hinc : (∑ j, incident C j * Function.update p i x j) =
      (∑ j, incident C j * p j) + incident C i * x := by
    have ht (j : Fin m) : incident C j * Function.update p i x j =
        incident C j * p j + if j = i then incident C i * x else 0 := by
      by_cases hj : j = i <;> simp [hj, Function.update_of_ne, hpi]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp
  rw [completeType_objective, objective_add_head C i p hpi,
    objective_add_head C i p hpi, hrow, hinc]
  simp only [Function.update_self, mul_zero, sub_zero]
  ring

end Erdos1017.MultipartiteDust
