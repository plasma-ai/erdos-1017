module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomPenaltyPositivity
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomCountMoments

/-!
# Own row bounds and count guards of the four-region system

From the four-region shifted rows, the own contact bonus and copy-gain budgets,
derives the three own count-row differences, the strict half-delta penalty
floors, `ell < v` from the forbidden `A`-`E` fill and `u < b` from neutral
stationarity, assembling the own count guards.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- Actual four-region shifted rows, allowing arbitrary AB charge t and
AR charge s. BR and the other five-coordinate charges remain literal. -/
structure FourRegionShiftedRows (x : Coefficients) (a b u e t s ell nu : ℝ) : Prop where
  A : t * b + s * u + ell * (b + u) = nu
  B : t * a + x 0 * u + x 1 * e + ell * (a + u + e) = nu
  R : s * a + x 0 * b - x 2 * u - x 4 * e + ell * (a + b + u + e) = nu
  E : x 1 * b - x 4 * u - x 3 * e + ell * (b + u + e) = nu

/-- The same original shifted scalar rows yield all three own count-row
differences; no original multiplier is transferred to another active dual. -/
theorem FourRegionShiftedRows.ownCountRows {x : Coefficients} {a b u e ell nu : ℝ}
    (h : FourRegionShiftedRows x a b u e 1 (-x 0) ell nu) : OwnCountRows x a b u e ell := by
  constructor
  · nlinarith only [h.A, h.E]
  · nlinarith only [h.A, h.B]
  · nlinarith only [h.A, h.R]

/-- The own E-row and total mass give the exact positive-row identity. -/
theorem FourRegionShiftedRows.own_E_charge {x : Coefficients} {a b u e ell nu : ℝ}
    (h : FourRegionShiftedRows x a b u e 1 (-x 0) ell nu)
    (hmass : a + b + u + e = 1) :
    (nu - ell) + ell * a = b * x 1 - x 4 * u - x 3 * e := by
  have hm := congrArg (fun z : ℝ => ell * z) hmass
  nlinarith only [h.E, hm]

/-- Strict present BE and AR floors and positive E mass force a<b from
actual old shifted rows, before any optimal-face compactness is used. -/
theorem FourRegionShiftedRows.a_lt_b {x : Coefficients} {a b u e ell nu : ℝ}
    (h : FourRegionShiftedRows x a b u e 1 (-x 0) ell nu)
    (hh : 0 < x 0) (hu : 0 ≤ u) (he : 0 < e)
    (hAR : 0 < ell - x 0) (hBE : 0 < ell + x 1) : a < b := by
  have hell : 0 < ell := by linarith
  have hrow := h.ownCountRows.BA
  have hpos := mul_pos hBE he
  have hnonneg := mul_nonneg hh.le hu
  by_contra hn
  have hprod := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 + ell)
    (by linarith : b - a ≤ 0)
  nlinarith only [hrow, hpos, hnonneg, hprod]

/-- Local no-positive-gain quadratic budgets force the linear gain to be
nonpositive. This is an actual small-positive-mass argument. -/
theorem linear_gain_nonpos_of_quadratic_budget (L P : ℝ) (hP : 0 ≤ P)
    (hbudget : ∃ eps : ℝ, 0 < eps ∧ ∀ s : ℝ, 0 < s → s ≤ eps →
      s * L - P * s ^ 2 / 2 ≤ 0) : L ≤ 0 := by
  obtain ⟨eps, heps, hbudget⟩ := hbudget
  by_contra h
  have hL : 0 < L := lt_of_not_ge h
  let s := min eps (L / (P + 1))
  have hs : 0 < s := lt_min heps (div_pos hL (by linarith))
  have hseps : s ≤ eps := min_le_left _ _
  have hsmall : s * (P + 1) ≤ L :=
    (le_div_iff₀ (by linarith : 0 < P + 1)).mp (min_le_right _ _)
  have hlinear : 0 < L - P * s / 2 := by nlinarith
  have hgain := mul_pos hs hlinear
  have hmax := hbudget s hs hseps
  nlinarith only [hgain, hmax]

/-- Budgets of the three finite-count copy edits. The fully feasible model
construction and the objective comparison are proved where these budgets are used. -/
structure CopyGainBudgets (x : Coefficients) (a b ell gamma : ℝ) : Prop where
  RR : ∃ eps : ℝ, 0 < eps ∧ ∀ s : ℝ, 0 < s → s ≤ eps →
    s * (gamma - b * x 2) - x 2 * s ^ 2 / 2 ≤ 0
  EE : ∃ eps : ℝ, 0 < eps ∧ ∀ s : ℝ, 0 < s → s ≤ eps →
    s * (gamma + ell * a - b * x 3) - x 3 * s ^ 2 / 2 ≤ 0
  RE : ∃ eps : ℝ, 0 < eps ∧ ∀ s : ℝ, 0 < s → s ≤ eps →
    s * (gamma + x 0 * a - b * x 4) - x 2 * s ^ 2 / 2 ≤ 0

/-- The actual three no-gain budgets give their coefficient bounds rather
than assuming the final strict penalty floors. -/
theorem CopyGainBudgets.penalty_bounds {x : Coefficients} {a b ell gamma : ℝ}
    (h : CopyGainBudgets x a b ell gamma) (hx : x ∈ feasible) :
    gamma ≤ b * x 2 ∧ gamma + ell * a ≤ b * x 3 ∧ gamma + x 0 * a ≤ b * x 4 := by
  have hp := linear_gain_nonpos_of_quadratic_budget _ _ hx.1 h.RR
  have hq := linear_gain_nonpos_of_quadratic_budget _ _ hx.2.1 h.EE
  have hr := linear_gain_nonpos_of_quadratic_budget _ _ hx.1 h.RE
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The same own contact bonus and genuine copy budgets yield all three
strict half-delta floors. No floor or positive r is an input. -/
theorem CopyGainBudgets.strict_penalty_floors {x : Coefficients} {a b ell gamma : ℝ}
    (h : CopyGainBudgets x a b ell gamma) (hx : x ∈ feasible)
    (ha : 0 ≤ a) (hb : 0 < b) (hell : 0 ≤ ell) (hh : 0 ≤ x 0)
    (hbonus : b * (1 - ell) < 2 * gamma) :
    (1 - ell) / 2 < x 2 ∧ (1 - ell) / 2 < x 3 ∧ (1 - ell) / 2 < x 4 := by
  obtain ⟨hp, hq, hr⟩ := h.penalty_bounds hx
  have hq' : gamma ≤ b * x 3 := by nlinarith [mul_nonneg hell ha]
  have hr' : gamma ≤ b * x 4 := by nlinarith [mul_nonneg hh ha]
  have hfloor (z : ℝ) (hz : gamma ≤ b * z) : (1 - ell) / 2 < z := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hb.le
    nlinarith only [hm, hz, hbonus]
  exact ⟨hfloor _ hp, hfloor _ hq', hfloor _ hr'⟩

/-- All count tests after genuinely filling the A-E rectangle at charge
-ell. The two original atoms still have Boolean multiplicity. -/
def filledCountTest (x : Coefficients) (ell : ℝ) : Bool → Bool → ℕ → ℕ → ℝ
  | false, false, k, l => unanchoredTest k l x
  | false, true, k, l => countTest k l x
  | true, false, k, l => -x 0 * k - ell * l + unanchoredTest k l x
  | true, true, k, l => 1 + (x 1 - ell) * l + unanchoredTest k l x

/-- ell>=v makes every newly added A-E clique test feasible, using only
genuine original all-count tests and derived nonnegative penalties. -/
theorem filled_count_tests_of_v_le_ell (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hh : 0 ≤ x 0) (hell : 0 ≤ ell) (hr : 0 ≤ x 4) (hv : x 1 ≤ ell) :
    ∀ A B k l, filledCountTest x ell A B k l ≤ 1 := by
  have hu (k l : ℕ) : unanchoredTest k l x ≤ 0 := by
    have hk : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
      simpa using TightCounts.gap_nonneg 0 k
    have hl : 0 ≤ (l : ℝ) * ((l : ℝ) - 1) := by
      simpa using TightCounts.gap_nonneg 0 l
    have hp := mul_nonneg hx.1 hk
    have hq := mul_nonneg hx.2.1 hl
    have hmix := mul_nonneg (mul_nonneg hr (Nat.cast_nonneg k)) (Nat.cast_nonneg l)
    rw [unanchoredTest_apply]
    nlinarith only [hp, hq, hmix]
  intro A B k l
  cases A <;> cases B
  · exact (hu k l).trans zero_le_one
  · exact hx.2.2.1 k l
  · have hH := mul_nonneg hh (Nat.cast_nonneg k)
    have hE := mul_nonneg hell (Nat.cast_nonneg l)
    change -x 0 * k - ell * l + unanchoredTest k l x ≤ 1
    nlinarith [hu k l]
  · have hchange := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (Nat.cast_nonneg l)
    change 1 + (x 1 - ell) * l + unanchoredTest k l x ≤ 1
    linarith [hu k l]

/-- The physical prohibition of this precise feasible A-E fill
forces ell<v; feasibility of all new clique counts is constructed here. -/
theorem ell_lt_v_of_forbidden_filled_counts (x : Coefficients) (hx : x ∈ feasible)
    (ell : ℝ) (hh : 0 ≤ x 0) (hell : 0 ≤ ell) (hr : 0 ≤ x 4)
    (hforbid : ¬∀ A B k l, filledCountTest x ell A B k l ≤ 1) : ell < x 1 := by
  by_contra h
  exact hforbid (filled_count_tests_of_v_le_ell x hx ell hh hell hr (le_of_not_gt h))

/-- Equality u=b is incompatible with actual own stationarity of the
explicit neutral AB-down/AR-up competitor. The new multiplier is its own. -/
theorem neutral_stationary_impossible {x : Coefficients}
    {a b u e ell nu ell' nu' delta : ℝ}
    (ha : 0 < a) (he : 0 < e) (hd : 0 < delta) (hub : u = b)
    (h : FourRegionShiftedRows x a b u e 1 (-x 0) ell nu)
    (h' : FourRegionShiftedRows x a b u e (1 - delta) (-x 0 + delta) ell' nu') : False := by
  have hA := h.A
  have hE := h.E
  have hB := h.B
  have hA' := h'.A
  have hE' := h'.E
  have hB' := h'.B
  rw [hub] at hA hE hB hA' hE' hB'
  have hgap : (ell' - ell) * e = 0 := by nlinarith only [hA, hE, hA', hE']
  have hell : ell' = ell := by
    have hz := (mul_eq_zero.mp hgap).resolve_right (ne_of_gt he)
    linarith only [hz]
  rw [hell] at hA' hB'
  have hnu : nu' = nu := by nlinarith only [hA, hA']
  have hgain := mul_pos ha hd
  nlinarith only [hB, hB', hnu, hgain]

/-- Weak demand u<=b becomes strict from actual own stationarity of the
explicit small neutral feasible active competitor. No final strictness,
new-row equality or multiplier transfer is assumed. -/
theorem u_lt_b_of_neutral_stationarity {x : Coefficients} {a b u e ell nu : ℝ}
    (hx : x ∈ feasible) (hh : 0 < x 0) (ha : 0 < a) (he : 0 < e) (hub : u ≤ b)
    (h : FourRegionShiftedRows x a b u e 1 (-x 0) ell nu)
    (hneutral : ∀ delta : ℝ, 0 < delta → delta ≤ x 0 → delta ≤ x 2 → u = b →
      ∃ ell' nu', FourRegionShiftedRows x a b u e
        (1 - delta) (-x 0 + delta) ell' nu') : u < b := by
  have hp := p_pos_of_h_pos x hx hh
  by_contra hn
  have heq : u = b := le_antisymm hub (le_of_not_gt hn)
  let delta := min (x 0) (x 2) / 2
  have hd : 0 < delta := half_pos (lt_min hh hp)
  have hdh : delta ≤ x 0 := by
    have hm := min_le_left (x 0) (x 2)
    dsimp only [delta]
    linarith
  have hdp : delta ≤ x 2 := by
    have hm := min_le_right (x 0) (x 2)
    dsimp only [delta]
    linarith
  obtain ⟨ell', nu', h'⟩ := hneutral delta hd hdh hdp heq
  exact neutral_stationary_impossible ha he hd heq h h'

/-- The numerical own-data adapter constructs the actual count guards
from original shifted rows, strict present floors, genuine competitor
budgets and the exact filled-AE prohibition. No final guard is supplied. -/
theorem ownCountGuards_of_row_competitors {x : Coefficients} {a b u e ell nu : ℝ}
    (hx : x ∈ feasible) (hh : 0 < x 0) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 ≤ u) (he : 0 < e) (hmass : a + b + u + e = 1)
    (hrows : FourRegionShiftedRows x a b u e 1 (-x 0) ell nu)
    (hell : 1 / 2 < ell) (hgamma : 0 < nu - ell)
    (hAR : 0 < ell - x 0) (hRR : 0 < ell - x 2)
    (hEE : 0 < ell - x 3) (hRE : 0 < ell - x 4) (hBE : 0 < ell + x 1)
    (hub : u ≤ b)
    (hneutral : ∀ delta : ℝ, 0 < delta → delta ≤ x 0 → delta ≤ x 2 → u = b →
      ∃ ell' nu', FourRegionShiftedRows x a b u e
        (1 - delta) (-x 0 + delta) ell' nu')
    (hmax : ∀ y ∈ feasible, objective a b u e y ≤ objective a b u e x)
    (hcopy : CopyGainBudgets x a b ell (nu - ell))
    (hbonus : b * (1 - ell) < 2 * (nu - ell))
    (hforbid : ¬∀ A B k l, filledCountTest x ell A B k l ≤ 1) :
    a < b ∧ u < b ∧ OwnCountRows x a b u e ell ∧ OwnCountGuards x ell := by
  have hab := hrows.a_lt_b hh hu he hAR hBE
  have hbu := u_lt_b_of_neutral_stationarity hx hh ha he hub hrows hneutral
  have hell0 : 0 ≤ ell := by linarith
  have hE := hrows.own_E_charge hmass
  obtain ⟨hpos, _⟩ := positive_coefficients_and_contact_of_own_E_row hbu he x hx hh
    ha.le hb.le hu hell0 hgamma hE hmax
  have hv := ell_lt_v_of_forbidden_filled_counts x hx ell hh.le hell0 (hpos 4).le hforbid
  obtain ⟨hp, hq, hr⟩ := hcopy.strict_penalty_floors hx ha.le hb hell0 hh.le hbonus
  have hvone := hx.2.2.1 0 1
  norm_num [countTest_apply] at hvone
  refine ⟨hab, hbu, hrows.ownCountRows, ?_⟩
  exact ⟨hh, hell, by linarith, by linarith, by linarith, by linarith,
    hv, hvone, hp, hq, hr⟩

end Erdos1017.TwoAtomCountGate
