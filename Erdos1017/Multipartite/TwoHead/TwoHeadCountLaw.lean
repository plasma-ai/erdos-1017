module

public import Erdos1017.Multipartite.Dust.DustSingleMerge
public import Erdos1017.Multipartite.MultipartiteDensitySelection
public import Erdos1017.LowerBound.Repeat
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# Count law for one secondary head and dust

Exact fixed-profile optimization for an anchor, one secondary independent head
and dust. The upper bound averages the count tests against an explicit finite
law; the matching bounded dual proves equality. Optimizing these profile values
at a prescribed density is not part of this module.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.TwoHeadCountLaw

def cellValue (j t : ℕ) (x S : ℝ) : ℝ :=
  let J : ℝ := (j : ℝ) * ((j : ℝ) + 1)
  x * (1 - (t : ℝ) * ((t : ℝ) + 1) / J) +
    (2 * (j : ℝ) - 2 * ((j : ℝ) - (t : ℝ)) * x) * S / J - S ^ 2 / J

def floorMoment (t : ℕ) (S : ℝ) : ℝ := (t : ℝ) * (2 * S - (t : ℝ) - 1)

def conditionalMoment (x S : ℝ) (t : ℕ) : ℝ :=
  (S ^ 2 - x * floorMoment t S) / (1 - x)

def dual (j t : ℕ) : MultipartiteDust.Coefficients 1
  | .inl _ => 1 - (t : ℝ) * ((t : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1))
  | .inr (.inl _) => 0
  | .inr (.inr (.inl _)) =>
      2 * ((j : ℝ) - (t : ℝ)) / ((j : ℝ) * ((j : ℝ) + 1))
  | .inr (.inr (.inr false)) => 2 * (j : ℝ) / ((j : ℝ) * ((j : ℝ) + 1))
  | .inr (.inr (.inr true)) => 2 / ((j : ℝ) * ((j : ℝ) + 1))

theorem dual_feasible (j t : ℕ) (hj : 0 < j) (htj : t ≤ j) :
    dual j t ∈ MultipartiteDust.feasible 1 := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have htj' : (t : ℝ) ≤ j := by exact_mod_cast htj
  have hJ : 0 < (j : ℝ) * ((j : ℝ) + 1) := by positivity
  have hprod : (t : ℝ) * ((t : ℝ) + 1) ≤ (j : ℝ) * ((j : ℝ) + 1) := by
    nlinarith
  have hbox (c : MultipartiteDust.Coordinate 1) : 0 ≤ dual j t c ∧ dual j t c ≤ 1 := by
    rcases c with i | (ij | (i | b))
    · change 0 ≤ 1 - (t : ℝ) * ((t : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) ∧
        1 - (t : ℝ) * ((t : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) ≤ 1
      have hr0 : 0 ≤ (t : ℝ) * ((t : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) := by positivity
      have hr1 := (div_le_one hJ).mpr hprod
      constructor <;> linarith
    · exact ⟨le_rfl, zero_le_one⟩
    · change 0 ≤ 2 * ((j : ℝ) - (t : ℝ)) / ((j : ℝ) * ((j : ℝ) + 1)) ∧ _
      constructor
      · exact div_nonneg (by linarith) hJ.le
      · apply (div_le_one hJ).mpr
        nlinarith
    · cases b
      · change 0 ≤ 2 * (j : ℝ) / ((j : ℝ) * ((j : ℝ) + 1)) ∧ _
        constructor
        · positivity
        · apply (div_le_one hJ).mpr
          nlinarith
      · change 0 ≤ 2 / ((j : ℝ) * ((j : ℝ) + 1)) ∧ _
        constructor
        · positivity
        · apply (div_le_one hJ).mpr
          nlinarith
  refine ⟨⟨fun c => (hbox c).1, fun c => (hbox c).2⟩, ?_⟩
  intro X k
  have heq : MultipartiteDust.charge (dual j t) X k =
      if X 0 then
        1 + ((k : ℝ) * (2 * (t : ℝ) + 1 - (k : ℝ)) -
          (t : ℝ) * ((t : ℝ) + 1)) / ((j : ℝ) * ((j : ℝ) + 1))
      else (k : ℝ) * (2 * (j : ℝ) + 1 - (k : ℝ)) /
        ((j : ℝ) * ((j : ℝ) + 1)) := by
    cases hX : X 0 <;>
      simp [MultipartiteDust.charge, MultipartiteDust.head, MultipartiteDust.pair,
        MultipartiteDust.linear, MultipartiteDust.incident, MultipartiteDust.penalty,
        dual, Selector.bit, hX] <;> ring
  rw [heq]
  split_ifs
  · have h := Repeat.discrete_quadratic_bound t k
    have hd : ((k : ℝ) * (2 * (t : ℝ) + 1 - (k : ℝ)) -
        (t : ℝ) * ((t : ℝ) + 1)) / ((j : ℝ) * ((j : ℝ) + 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hJ.le
    linarith
  · exact (div_le_one hJ).mpr (Repeat.discrete_quadratic_bound j k)

theorem dual_objective (j t : ℕ) (x S : ℝ) :
    MultipartiteDust.objective (fun _ : Fin 1 => x) S (dual j t) = cellValue j t x S := by
  simp [MultipartiteDust.objective, MultipartiteDust.head, MultipartiteDust.pair,
    MultipartiteDust.linear, MultipartiteDust.incident, MultipartiteDust.penalty, dual, cellValue]
  ring

theorem cellValue_le_value (j t : ℕ) (hj : 0 < j) (htj : t ≤ j) (x S : ℝ) :
    cellValue j t x S ≤ MultipartiteDust.value (fun _ : Fin 1 => x) S := by
  rw [← dual_objective]
  exact MultipartiteDust.objective_le_value _ _ _ (dual_feasible j t hj htj)

/-- Exact first and factorial second moments turn any nonnegative finite
count law into an upper bound for the actual one-head coefficient value. -/
theorem value_le_count_law {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (b : Ω → Bool) (k : Ω → ℕ) (hw : ∀ ω, 0 ≤ w ω)
    (x S : ℝ) (hx : (∑ ω, w ω * Selector.bit (b ω)) = x)
    (hS : (∑ ω, w ω * (k ω : ℝ)) = S)
    (hcross : (∑ ω, w ω * Selector.bit (b ω) * (k ω : ℝ)) = x * S)
    (hfactor : (∑ ω, w ω * (k ω : ℝ) * ((k ω : ℝ) - 1)) = S ^ 2) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S ≤ ∑ ω, w ω := by
  obtain ⟨C, hC, heq⟩ := MultipartiteDust.exists_value_eq (fun _ : Fin 1 => x) S
  have hcharge (ω : Ω) : w ω * MultipartiteDust.charge C (fun _ : Fin 1 => b ω) (k ω) =
      MultipartiteDust.head C 0 * (w ω * Selector.bit (b ω)) +
        MultipartiteDust.linear C * (w ω * (k ω : ℝ)) -
        MultipartiteDust.incident C 0 * (w ω * Selector.bit (b ω) * (k ω : ℝ)) -
        (MultipartiteDust.penalty C / 2) *
          (w ω * (k ω : ℝ) * ((k ω : ℝ) - 1)) := by
    simp [MultipartiteDust.charge]
    ring
  have hmoment : (∑ ω, w ω * MultipartiteDust.charge C (fun _ : Fin 1 => b ω) (k ω)) =
      MultipartiteDust.objective (fun _ : Fin 1 => x) S C := by
    rw [Finset.sum_congr rfl (fun ω _ => hcharge ω)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hx, hS, hcross, hfactor]
    simp [MultipartiteDust.objective]
    ring
  rw [heq, ← hmoment]
  exact Finset.sum_le_sum (fun ω _ => by
    simpa using mul_le_mul_of_nonneg_left (hC.2 (fun _ => b ω) (k ω)) (hw ω))

def headSelection : Fin 4 → Bool := ![true, true, false, false]

def dustCount (j t : ℕ) : Fin 4 → ℕ := ![t, t + 1, j, j + 1]

def weight (j t : ℕ) (x S : ℝ) : Fin 4 → ℝ :=
  ![x * ((t : ℝ) + 1 - S), x * (S - (t : ℝ)),
    (1 - x) * ((j : ℝ) * S - conditionalMoment x S t) / (j : ℝ),
    (1 - x) * (conditionalMoment x S t - ((j : ℝ) - 1) * S) / ((j : ℝ) + 1)]

theorem weight_nonneg (j t : ℕ) {x S : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hj : 0 < j) (htlo : (t : ℝ) ≤ S) (hthi : S ≤ (t : ℝ) + 1)
    (hjlo : ((j : ℝ) - 1) * S ≤ conditionalMoment x S t)
    (hjhi : conditionalMoment x S t ≤ (j : ℝ) * S) :
    ∀ ω, 0 ≤ weight j t x S ω := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  intro ω
  fin_cases ω
  · change 0 ≤ x * ((t : ℝ) + 1 - S)
    exact mul_nonneg hx (by linarith)
  · change 0 ≤ x * (S - (t : ℝ))
    exact mul_nonneg hx (by linarith)
  · change 0 ≤ (1 - x) * ((j : ℝ) * S - conditionalMoment x S t) / (j : ℝ)
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hj0.le
  · change 0 ≤ (1 - x) * (conditionalMoment x S t - ((j : ℝ) - 1) * S) / ((j : ℝ) + 1)
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

theorem weight_moments (j t : ℕ) {x S : ℝ} (hx1 : x < 1) (hj : 0 < j) :
    (∑ ω, weight j t x S ω * Selector.bit (headSelection ω)) = x ∧
      (∑ ω, weight j t x S ω * (dustCount j t ω : ℝ)) = S ∧
      (∑ ω, weight j t x S ω * Selector.bit (headSelection ω) * (dustCount j t ω : ℝ)) = x * S ∧
      (∑ ω, weight j t x S ω * (dustCount j t ω : ℝ) * ((dustCount j t ω : ℝ) - 1)) = S ^ 2 := by
  have hj0 : (j : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hj)
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hx' : 1 - x ≠ 0 := by linarith
  norm_num [Fin.sum_univ_succ, weight, headSelection, dustCount, Selector.bit,
    conditionalMoment, floorMoment]
  constructor
  · ring
  constructor
  · field_simp
    ring
  constructor
  · ring
  · field_simp
    ring

theorem weight_sum (j t : ℕ) {x S : ℝ} (hx1 : x < 1) (hj : 0 < j) :
    (∑ ω, weight j t x S ω) = cellValue j t x S := by
  have hj0 : (j : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hj)
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hx' : 1 - x ≠ 0 := by linarith
  norm_num [Fin.sum_univ_succ, weight, conditionalMoment, floorMoment, cellValue]
  field_simp
  ring

/-- At every admissible count cell, the explicit law and matching dual
identify the actual fixed-profile value. -/
theorem value_eq_cell (j t : ℕ) {x S : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hj : 0 < j) (htj : t ≤ j) (htlo : (t : ℝ) ≤ S) (hthi : S ≤ (t : ℝ) + 1)
    (hjlo : ((j : ℝ) - 1) * S ≤ conditionalMoment x S t)
    (hjhi : conditionalMoment x S t ≤ (j : ℝ) * S) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S = cellValue j t x S := by
  have hm := weight_moments j t (S := S) hx1 hj
  apply le_antisymm
  · have h := value_le_count_law (weight j t x S) headSelection (dustCount j t)
      (weight_nonneg j t hx hx1 hj htlo hthi hjlo hjhi) x S
      hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
    rwa [weight_sum j t hx1 hj] at h
  · exact cellValue_le_value j t hj htj x S

def selectedIndex (x S : ℝ) : ℕ :=
  ⌈conditionalMoment x S ⌊S⌋₊ / S⌉₊

theorem conditionalMoment_ge_sq (t : ℕ) {x S : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hS : 0 ≤ S) (htlo : (t : ℝ) ≤ S) (hthi : S ≤ (t : ℝ) + 1) :
    S ^ 2 ≤ conditionalMoment x S t := by
  have hdiff : 0 ≤ S ^ 2 - floorMoment t S := by
    have hp := mul_nonneg (sub_nonneg.mpr htlo) (show 0 ≤ (t : ℝ) + 1 - S by linarith)
    unfold floorMoment
    nlinarith
  unfold conditionalMoment
  apply (le_div_iff₀ (by linarith : 0 < 1 - x)).mpr
  nlinarith [mul_nonneg hx hdiff]

/-- The floor and ceiling select an actual admissible count cell, including
zero secondary mass and an integer dust mean. -/
theorem selectedIndex_spec {x S : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hS : 0 < S) :
    0 < selectedIndex x S ∧ ⌊S⌋₊ ≤ selectedIndex x S ∧
      ((selectedIndex x S : ℝ) - 1) * S < conditionalMoment x S ⌊S⌋₊ ∧
      conditionalMoment x S ⌊S⌋₊ ≤ (selectedIndex x S : ℝ) * S := by
  have hR := conditionalMoment_ge_sq ⌊S⌋₊ hx hx1 hS.le
    (Nat.floor_le hS.le) (Nat.lt_floor_add_one S).le
  have hRpos : 0 < conditionalMoment x S ⌊S⌋₊ := (sq_pos_of_pos hS).trans_le hR
  have hratio : 0 < conditionalMoment x S ⌊S⌋₊ / S := div_pos hRpos hS
  have hjlo := Nat.ceil_lt_add_one hratio.le
  have hjhi := Nat.le_ceil (conditionalMoment x S ⌊S⌋₊ / S)
  have hSratio : S ≤ conditionalMoment x S ⌊S⌋₊ / S :=
    (le_div_iff₀ hS).mpr (by simpa only [pow_two] using hR)
  refine ⟨Nat.ceil_pos.mpr hratio, ?_, ?_, ?_⟩
  · have h := (Nat.floor_le hS.le).trans (hSratio.trans hjhi)
    exact_mod_cast h
  · apply (lt_div_iff₀ hS).mp
    change (⌈conditionalMoment x S ⌊S⌋₊ / S⌉₊ : ℝ) - 1 < _
    linarith
  · exact (div_le_iff₀ hS).mp hjhi

/-- The closed count law computes the actual value at every nonbalanced
profile with positive dust. No count-cell premise is left unproved. -/
theorem value_eq_selected {x S : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hS : 0 < S) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S =
      cellValue (selectedIndex x S) ⌊S⌋₊ x S := by
  have hj := selectedIndex_spec hx hx1 hS
  exact value_eq_cell _ _ hx hx1 hj.1 hj.2.1 (Nat.floor_le hS.le)
    (Nat.lt_floor_add_one S).le hj.2.2.1.le hj.2.2.2

/-- Omitting the singleton leaves a subprobability count law. -/
theorem weight_sum_le_one (j t : ℕ) {x S : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hj : 0 < j) (htj : t ≤ j) (htlo : (t : ℝ) ≤ S) (hthi : S ≤ (t : ℝ) + 1)
    (hjlo : ((j : ℝ) - 1) * S ≤ conditionalMoment x S t)
    (hjhi : conditionalMoment x S t ≤ (j : ℝ) * S) :
    (∑ ω, weight j t x S ω) ≤ 1 := by
  rw [weight_sum j t hx1 hj, ← value_eq_cell j t hx hx1 hj htj htlo hthi hjlo hjhi]
  exact MultipartiteDust.value_le_one _ (fun _ => ⟨hx, hx1.le⟩) S
    (by linarith [show (0 : ℝ) ≤ t from Nat.cast_nonneg t])

theorem value_zero_dust {x : ℝ} (hx : 0 ≤ x) :
    MultipartiteDust.value (fun _ : Fin 1 => x) 0 = x := by
  apply le_antisymm
  · obtain ⟨C, hC, heq⟩ := MultipartiteDust.exists_value_eq (fun _ : Fin 1 => x) 0
    rw [heq]
    simp only [MultipartiteDust.objective, Fin.sum_univ_one, zero_mul,
      mul_zero, sub_zero, add_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
      lt_self_iff_false, ↓reduceIte]
    exact mul_le_of_le_one_left hx (hC.1.2 _)
  · have h := cellValue_le_value 1 0 (by decide) (by decide) x 0
    simpa [cellValue] using h

theorem value_unit_head {S : ℝ} (hS : 0 ≤ S) :
    MultipartiteDust.value (fun _ : Fin 1 => (1 : ℝ)) S = 1 := by
  apply le_antisymm
  · exact MultipartiteDust.value_le_one _ (fun _ => ⟨by norm_num, le_rfl⟩) S hS
  · let C : MultipartiteDust.Coefficients 1 := fun c => match c with
      | .inl _ => 1
      | _ => 0
    have hbox (c : MultipartiteDust.Coordinate 1) : 0 ≤ C c ∧ C c ≤ 1 := by
      rcases c with i | (ij | (i | b)) <;> simp [C]
    have hC : C ∈ MultipartiteDust.feasible 1 := by
      refine ⟨⟨fun c => (hbox c).1, fun c => (hbox c).2⟩, ?_⟩
      intro X k
      have heq : MultipartiteDust.charge C X k = Selector.bit (X 0) := by
        simp only [MultipartiteDust.charge, Fin.sum_univ_one, MultipartiteDust.head,
          MultipartiteDust.pair, MultipartiteDust.linear, MultipartiteDust.incident,
          MultipartiteDust.penalty, C, one_mul, zero_mul, mul_zero, sub_zero, add_zero,
          zero_div]
      rw [heq]
      cases hX : X 0 <;>
        simp [Selector.bit]
    have h := MultipartiteDust.objective_le_value (fun _ : Fin 1 => (1 : ℝ)) S C hC
    simpa [MultipartiteDust.objective, MultipartiteDust.head, MultipartiteDust.pair,
      MultipartiteDust.linear, MultipartiteDust.incident, MultipartiteDust.penalty, C] using h

theorem cellValue_three_one (x S : ℝ) :
    cellValue 3 1 x S = (10 * x + (6 - 4 * x) * S - S ^ 2) / 12 := by
  norm_num [cellValue]
  ring

end Erdos1017.TwoHeadCountLaw
