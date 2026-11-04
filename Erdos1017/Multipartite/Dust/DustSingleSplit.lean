module

public import Erdos1017.Multipartite.Dust.DustSingleMerge

/-!
# Separating one head from merged dust

`splitOne` separates one original independent head from the merged dust type,
removing its internal pairs and retaining every exterior dust coefficient; the
restriction is a feasible bounded homogeneous dual whose objective gains the
removed internal pair charge, so completing a head cannot increase the
coefficient value.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

/-- Separate one old independent head from the merged dust type. Internal
pairs of that head are removed; every exterior dust coefficient is retained. -/
def splitOne {m : ℕ} (C : Coefficients m) (i : Fin m) : Coefficients m
  | .inl j => if j = i then linear C else head C j
  | .inr (.inl (j, k)) => if j = i then incident C k else
      if k = i then incident C j else pair C j k
  | .inr (.inr (.inl j)) => if j = i then penalty C else incident C j
  | .inr (.inr (.inr false)) => linear C
  | .inr (.inr (.inr true)) => penalty C

theorem splitOne_row {m : ℕ} (C : Coefficients m) (i j : Fin m) :
    (DustCellRestriction.headDual (splitOne C i)).beta i j =
      if j = i then 0 else -incident C j := by
  by_cases hij : j = i
  · subst j
    simpa using (DustCellRestriction.headDual (splitOne C i)).beta_diag i
  · rcases lt_or_gt_of_ne (Ne.symm hij) with h | h <;>
      simp [DustCellRestriction.headDual, pair, splitOne, hij, h, not_lt_of_gt h]

/-- Retained zero-slot head objectives are unaffected by splitting dust. -/
theorem splitOne_retained {m : ℕ} (C : Coefficients m) (i : Fin m)
    (p : Fin m → ℝ) (hpi : p i = 0) : objective p 0 (splitOne C i) = objective p 0 C := by
  have hh : (∑ j, head (splitOne C i) j * p j) = ∑ j, head C j * p j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i <;> simp [head, splitOne, hj, hpi]
  have hp : (∑ j, ∑ l, pair (splitOne C i) j l * (if j < l then 1 else 0) * p j * p l) =
      ∑ j, ∑ l, pair C j l * (if j < l then 1 else 0) * p j * p l := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hj : j = i <;> by_cases hl : l = i <;> simp [pair, splitOne, hj, hl, hpi]
  simp only [objective, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_div, sub_zero, hh, hp]

/-- Restricting a dust dual to an independent part adds precisely the removed
internal negative pair charge to its objective. -/
theorem splitOne_objective {m : ℕ} (C : Coefficients m) (i : Fin m)
    (p : Fin m → ℝ) (hpi : p i = 0) (x s : ℝ) :
    objective (Function.update p i x) s (splitOne C i) =
      objective p (s + x) C + penalty C * x ^ 2 / 2 := by
  have hr : (∑ j, (DustCellRestriction.headDual (splitOne C i)).beta i j * p j) =
      -(∑ j, incident C j * p j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [splitOne_row]
    by_cases hj : j = i <;> simp [hj, hpi]
  have hi : (∑ j, incident (splitOne C i) j * p j) = ∑ j, incident C j * p j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i <;> simp [incident, splitOne, hj, hpi]
  rw [objective_add_head (splitOne C i) i p hpi, splitOne_retained C i p hpi, hr, hi,
    objective_dust_split C p (s + x), DustCellRestriction.headDual_objective]
  simp only [head, incident, linear, penalty, splitOne, ↓reduceIte]
  ring

/-- Each separated-head count is Boolean, so the dust restriction passes all
rooted tests with that head counted as one additional dust point. -/
theorem splitOne_charge {m : ℕ} (C : Coefficients m) (i : Fin m)
    (X : Selector.Selection m) (k : ℕ) :
    charge (splitOne C i) X k =
      charge C (eraseSelection X i) (k + if X i then 1 else 0) := by
  let p := fun j => Selector.bit (eraseSelection X i j)
  have hpi : p i = 0 := by simp [p, eraseSelection, Selector.bit]
  have hback : Function.update p i (Selector.bit (X i)) = fun j => Selector.bit (X j) := by
    funext j
    by_cases hj : j = i <;> simp [Function.update_of_ne, hj, p, eraseSelection]
  rw [DustCellBridge.charge_eq_objective, ← hback,
    splitOne_objective C i p hpi, DustCellBridge.charge_eq_objective]
  dsimp only [p]
  cases hXi : X i <;> simp [Selector.bit, penalty, splitOne]
  ring

/-- Separating a dust type is an actual feasible bounded homogeneous dual. -/
theorem splitOne_feasible {m : ℕ} (C : Coefficients m) (hC : C ∈ feasible m) (i : Fin m) :
    splitOne C i ∈ feasible m := by
  have hcoef (j : Coordinate m) : 0 ≤ C j ∧ C j ≤ 1 := ⟨hC.1.1 j, hC.1.2 j⟩
  have hb (j : Coordinate m) : 0 ≤ splitOne C i j ∧ splitOne C i j ≤ 1 := by
    rcases j with j | (⟨j, l⟩ | (j | b))
    · dsimp only [splitOne]
      split_ifs
      · exact hcoef (.inr (.inr (.inr false)))
      · exact hcoef (.inl j)
    · dsimp only [splitOne]
      split_ifs
      · exact hcoef (.inr (.inr (.inl l)))
      · exact hcoef (.inr (.inr (.inl j)))
      · exact hcoef (.inr (.inl (j, l)))
    · dsimp only [splitOne]
      split_ifs
      · exact hcoef (.inr (.inr (.inr true)))
      · exact hcoef (.inr (.inr (.inl j)))
    · cases b
      · exact hcoef (.inr (.inr (.inr false)))
      · exact hcoef (.inr (.inr (.inr true)))
  refine ⟨⟨fun j => (hb j).1, fun j => (hb j).2⟩, ?_⟩
  intro X k
  rw [splitOne_charge]
  exact hC.2 _ _

/-- Completing a head cannot increase the coefficient value. -/
theorem single_merge_le_value {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (i : Fin m) :
    value (Function.update p i 0) (s + p i) ≤ value p s := by
  obtain ⟨C, hC, heq⟩ := exists_value_eq (Function.update p i 0) (s + p i)
  have h := splitOne_objective C i (Function.update p i 0) (by simp) (p i) s
  have hback : Function.update (Function.update p i 0) i (p i) = p := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [hback] at h
  have hbound := objective_le_value p s (splitOne C i) (splitOne_feasible C hC i)
  have hp : 0 ≤ penalty C := hC.1.1 (.inr (.inr (.inr true)))
  have hcorrection := mul_nonneg hp (sq_nonneg (p i))
  rw [heq]
  linarith

/-- Source (D) for one arbitrary completed head, including existing dust. -/
theorem single_merge_value_error {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (i : Fin m)
    (hpi : 0 ≤ p i) (hs : 0 ≤ s) :
    0 ≤ value p s - value (Function.update p i 0) (s + p i) ∧
      value p s - value (Function.update p i 0) (s + p i) ≤ (p i) ^ 2 / 2 := by
  constructor
  · exact sub_nonneg.mpr (single_merge_le_value p s i)
  · linarith [value_le_single_merge p s i hpi hs]

end Erdos1017.MultipartiteDust
