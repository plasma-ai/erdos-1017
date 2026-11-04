module

public import Erdos1017.Multipartite.Dust.DustAveraging
public import Erdos1017.Multipartite.MultipartiteDust

/-!
# From cell labels to a masked dust dual

After averaging, the cell labels cease to be independent heads (`maskedDual`);
the homogeneous objective agrees with the averaged one, averaging gives a
feasible point of the finite-head all-count coefficient problem, and the finite
selector value is at most the bounded dust coefficient value plus the
finite-cell error.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.DustCellBridge

open scoped BigOperators
open Selector

/-- The old cell labels cease to be independent heads after averaging. -/
def maskedDual {m : ℕ} (D : Dual m) (S : Finset (Fin m)) : Dual m :=
  removeZeros (fun i => if i ∈ S then 0 else 1) D

def maskedMass {m : ℕ} (S : Finset (Fin m)) (p : Fin m → ℝ) (i : Fin m) : ℝ :=
  if i ∈ S then 0 else p i

def mixedRow {m : ℕ} (D : Dual m) (q : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ S then 0 else ∑ j, D.beta i j * q j

/-- A finite cell dual expressed in the finite-head homogeneous dust coordinates. -/
def coefficients {m : ℕ} (D : Dual m) (q : Fin m → ℝ) (S : Finset (Fin m)) :
    MultipartiteDust.Coefficients m
  | .inl i => (maskedDual D S).alpha i
  | .inr (.inl (i, j)) => -(maskedDual D S).beta i j
  | .inr (.inr (.inl i)) => -mixedRow D q S i
  | .inr (.inr (.inr false)) => dustLinear D q
  | .inr (.inr (.inr true)) => dustPenalty D q

theorem symmetric_half_sum {m : ℕ} (D : Dual m) (p : Fin m → ℝ) :
    (∑ i, ∑ j, D.beta i j * (p i * p j)) / 2 =
      ∑ i, ∑ j, D.beta i j * (if i < j then 1 else 0) * p i * p j := by
  have h := SelectorLinearProgram.symmetric_pair_sum (fun i j => D.beta i j * (p i * p j))
    (fun i j => by rw [D.beta_symm]; ring) (fun i => by simp [D.beta_diag])
  have htri : (∑ i, ∑ j, if i < j then D.beta i j * (p i * p j) else 0) =
      ∑ ij : SelectorLinearProgram.Pair m, D.beta ij.val.1 ij.val.2 * (p ij.val.1 * p ij.val.2) := by
    rw [← Fintype.sum_prod_type (fun ij : Fin m × Fin m =>
      if ij.1 < ij.2 then D.beta ij.1 ij.2 * (p ij.1 * p ij.2) else 0), ← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  have hterm (i j : Fin m) : D.beta i j * (if i < j then 1 else 0) * p i * p j =
      if i < j then D.beta i j * (p i * p j) else 0 := by split_ifs <;> ring
  simp_rw [hterm]
  rw [htri]
  linarith

theorem mixedRow_sum {m : ℕ} (D : Dual m) (q p : Fin m → ℝ) (S : Finset (Fin m)) :
    (∑ i, mixedRow D q S i * p i) =
      ∑ i, ∑ j, D.beta i j * (maskedMass S p i * q j) := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [mixedRow, maskedMass, hi]
  · simp only [mixedRow, maskedMass, hi, ↓reduceIte, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)

theorem maskedDual_objective {m : ℕ} (D : Dual m) (S : Finset (Fin m)) (p : Fin m → ℝ) :
    objective p (maskedDual D S) = objective (maskedMass S p) D := by
  rw [maskedDual, removeZeros_objective]
  congr 1
  funext i
  by_cases hi : i ∈ S <;> simp [maskedMass, hi]

/-- The homogeneous objective agrees exactly with the independently averaged objective. -/
theorem objective_eq_averagedValue {m : ℕ} (D : Dual m) (q p : Fin m → ℝ)
    (S : Finset (Fin m)) (s : ℝ) :
    MultipartiteDust.objective p s (coefficients D q S) =
      averagedValue D (maskedMass S p) q s := by
  rw [averagedValue, ← maskedDual_objective, ← mixedRow_sum]
  unfold MultipartiteDust.objective MultipartiteDust.head MultipartiteDust.pair
    MultipartiteDust.incident MultipartiteDust.linear MultipartiteDust.penalty coefficients objective
  rw [symmetric_half_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [← Finset.sum_mul]
  ring

/-- Rooted dust charge differs from substituting its count as a real mass
only by the diagonal correction in the number of unordered dust pairs. -/
theorem charge_eq_objective {m : ℕ} (C : MultipartiteDust.Coefficients m)
    (X : Selection m) (k : ℕ) :
    MultipartiteDust.charge C X k =
      MultipartiteDust.objective (fun i => bit (X i)) (k : ℝ) C +
        MultipartiteDust.penalty C * (k : ℝ) / 2 := by
  unfold MultipartiteDust.charge MultipartiteDust.objective
  rw [← Finset.sum_mul]
  ring

theorem mixedRow_bounds {m : ℕ} (D : Dual m) (q : Fin m → ℝ) (S : Finset (Fin m))
    (hbeta : ∀ i j, -1 ≤ D.beta i j ∧ D.beta i j ≤ 0)
    (hq₀ : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) (i : Fin m) :
    -1 ≤ mixedRow D q S i ∧ mixedRow D q S i ≤ 0 := by
  unfold mixedRow
  split_ifs
  · norm_num
  · constructor
    · calc
        -1 = ∑ j, (-1 : ℝ) * q j := by rw [← Finset.mul_sum, hq]; ring
        _ ≤ _ := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hbeta i j).1 (hq₀ j))
    · exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hbeta i j).2 (hq₀ j))

theorem coefficients_in_box {m : ℕ} (D : Dual m) (q : Fin m → ℝ) (S : Finset (Fin m))
    (halpha : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1)
    (hbeta : ∀ i j, -1 ≤ D.beta i j ∧ D.beta i j ≤ 0)
    (hq₀ : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) :
    coefficients D q S ∈ Set.Icc 0 1 := by
  have ha (i : Fin m) : 0 ≤ (maskedDual D S).alpha i ∧ (maskedDual D S).alpha i ≤ 1 := by
    by_cases hi : i ∈ S <;> simp [maskedDual, removeZeros, hi, halpha]
  have hb (i j : Fin m) : -1 ≤ (maskedDual D S).beta i j ∧ (maskedDual D S).beta i j ≤ 0 := by
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [maskedDual, removeZeros, hi, hj, hbeta]
  have hdust := dust_coefficients_bounded D q halpha hbeta hq₀ hq
  have hboth (c : MultipartiteDust.Coordinate m) :
      0 ≤ coefficients D q S c ∧ coefficients D q S c ≤ 1 := by
    rcases c with i | (⟨i, j⟩ | (i | b))
    · exact ha i
    · change 0 ≤ -(maskedDual D S).beta i j ∧ -(maskedDual D S).beta i j ≤ 1
      constructor <;> linarith [hb i j]
    · change 0 ≤ -mixedRow D q S i ∧ -mixedRow D q S i ≤ 1
      constructor <;> linarith [mixedRow_bounds D q S hbeta hq₀ hq i]
    · cases b
      · exact hdust.1
      · exact hdust.2
  exact ⟨fun c => (hboth c).1, fun c => (hboth c).2⟩

/-- Independent averaging gives a feasible point of the actual finite-head
all-count coefficient problem, with old cell-head slots set to zero. -/
theorem coefficients_feasible {m : ℕ} (D : Dual m) (q : Fin m → ℝ) (S : Finset (Fin m))
    (hD : DualFeasible D) (halpha : ∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1)
    (hbeta : ∀ i j, -1 ≤ D.beta i j ∧ D.beta i j ≤ 0)
    (hq₀ : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1) (hsupport : ∀ i, i ∉ S → q i = 0) :
    coefficients D q S ∈ MultipartiteDust.feasible m := by
  refine ⟨coefficients_in_box D q S halpha hbeta hq₀ hq, ?_⟩
  intro X k
  let b : Fin m → ℕ := fun i => if i ∈ S then 0 else if X i then 1 else 0
  have hb (i : Fin m) : (b i : ℝ) = maskedMass S (fun i => bit (X i)) i := by
    by_cases hi : i ∈ S <;> cases X i <;> simp [b, maskedMass, bit, hi]
  have hself : (∑ i, D.alpha i * (b i : ℝ) * ((b i : ℝ) - 1) / 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ S <;> cases hX : X i <;> simp [b, hi, hX]
  have hzero : (∑ i, D.alpha i * (b i : ℝ) * q i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ S
    · simp [b, hi]
    · simp [hsupport i hi]
  have havg := averaged_count_le_one D hD (fun i => (halpha i).1)
    (fun i j => (hbeta i j).2) q hq₀ hq b k
  unfold repeatedCharge at havg
  rw [hself, hzero] at havg
  simp only [sub_zero, mul_zero, hb] at havg
  rw [charge_eq_objective, objective_eq_averagedValue]
  change averagedValue D (maskedMass S (fun i => bit (X i))) q (k : ℝ) +
    dustPenalty D q * (k : ℝ) / 2 ≤ 1
  unfold averagedValue
  nlinarith [havg]

/-- The finite selector value is at most the bounded dust coefficient value
plus the explicit finite-cell error. Physical value identification is not assumed. -/
theorem selector_value_le_dust_add_error {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (p : Fin m → ℝ) (s : ℝ) (hpzero : ∀ i ∈ S, p i = 0)
    (hp : ∀ i, 0 ≤ p i + s * uniformCellWeights S i ∧
      p i + s * uniformCellWeights S i ≤ 1) :
    Selector.value (fun i => p i + s * uniformCellWeights S i) ≤
      MultipartiteDust.value p s + s ^ 2 / (2 * (S.card : ℝ)) := by
  obtain ⟨D, hD, halpha, hbeta⟩ := exists_bounded_optimal
    (fun i => p i + s * uniformCellWeights S i) hp
  have hb : ∀ i j, -1 ≤ D.beta i j ∧ D.beta i j ≤ 0 := by
    intro i j
    refine ⟨?_, (hbeta i j).2⟩
    have hmin : min (D.alpha i) (D.alpha j) ≤ 1 := (min_le_left _ _).trans (halpha i).2
    linarith [(hbeta i j).1]
  have hq := uniformCellWeights_total S hS
  have hfeas := coefficients_feasible D (uniformCellWeights S) S hD.1 halpha hb
    (uniformCellWeights_nonneg S) hq (fun i hi => by simp [uniformCellWeights, hi])
  have hbound : MultipartiteDust.objective p s (coefficients D (uniformCellWeights S) S) ≤
      MultipartiteDust.value p s := by
    apply le_csSup
    · exact (MultipartiteDust.feasible_isCompact m).image
        (MultipartiteDust.objective_continuous p s) |>.bddAbove
    · exact ⟨_, hfeas, rfl⟩
  have hmask : maskedMass S p = p := by
    funext i
    by_cases hi : i ∈ S <;> simp [maskedMass, hi, hpzero]
  rw [objective_eq_averagedValue, hmask] at hbound
  have hloss := (uniform_cells_averaging D hD.1 halpha (fun i j => (hbeta i j).2) S hS p s).2.2
  rw [optimal_objective_eq_value _ hp D hD] at hloss
  linarith

end Erdos1017.DustCellBridge
