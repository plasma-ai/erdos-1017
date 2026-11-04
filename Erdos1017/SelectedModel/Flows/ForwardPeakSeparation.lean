module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Separated peak of summable endpoint masses

A summable family with a positive coordinate attains a positive maximum, and
summable endpoint masses with their original-dual budget give a uniformly
separated positive peak (`IsSeparatedPeak`), unique by its positive common gap.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos1017.ForwardPeak

/-- A peak label separated by the same displayed gap from every other
coordinate, without a finiteness assumption on the original label type. -/
def IsSeparatedPeak {ι : Type*} (a : ι → ℝ) (Δ : ℝ) (i : ι) : Prop :=
  ∀ j, j ≠ i → a j + Δ ≤ a i

/-- The actual supremum includes zero, so pure dust and the empty atomic
index type both have peak mass zero. -/
def massPeak {ι : Type*} (a : ι → ℝ) : ℝ := sSup (insert 0 (range a))

/-- Peak ordering and the actual total-mass bound control the square gap. -/
theorem square_gap_le_mass_gap {T b : ℝ} (hbT : b ≤ T) (htotal : T + b ≤ 1) :
    T ^ 2 - b ^ 2 ≤ T - b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hbT) (sub_nonneg.mpr htotal)]

/-- At slopes at least one, the original dual budget gives the gamma gap. -/
theorem gamma_le_peak_sub {T b ell hF gamma : ℝ}
    (hbT : b ≤ T) (htotal : T + b ≤ 1) (hsquares : T ^ 2 + b ^ 2 ≤ hF)
    (hell : 1 ≤ ell) (hbudget : gamma ≤ 2 * T ^ 2 - ell * hF) :
    gamma ≤ T - b := by
  have hF0 : 0 ≤ hF := (add_nonneg (sq_nonneg _) (sq_nonneg _)).trans hsquares
  have hprod : hF ≤ ell * hF := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hell) hF0]
  have hgap : gamma ≤ T ^ 2 - b ^ 2 := by linarith
  exact hgap.trans (square_gap_le_mass_gap hbT htotal)

/-- Below slope one, strict endpoint missing-mass improvement gives a
strict delta gap from the actual original-density budget identity. -/
theorem delta_lt_peak_sub {T b ell h hF gamma delta : ℝ}
    (hbT : b ≤ T) (htotal : T + b ≤ 1) (hsquares : T ^ 2 + b ^ 2 ≤ hF)
    (hell : ell < 1) (hreturn : hF < h)
    (hidentity : gamma = (1 - ell) * h + delta)
    (hbudget : gamma ≤ 2 * T ^ 2 - ell * hF) :
    delta < T - b := by
  have hslack : 0 < (1 - ell) * (h - hF) :=
    mul_pos (sub_pos.mpr hell) (sub_pos.mpr hreturn)
  have hgap : delta < T ^ 2 - b ^ 2 := by nlinarith
  exact hgap.trans_le (square_gap_le_mass_gap hbT htotal)

/-- The common forward gap keeps the original slope branch explicit. -/
def peakGap (ell gamma delta : ℝ) : ℝ := if 1 ≤ ell then gamma else delta

theorem peakGap_pos {ell gamma delta : ℝ} (hgamma : 0 < gamma) (hdelta : 0 < delta) :
    0 < peakGap ell gamma delta := by
  unfold peakGap
  split_ifs <;> assumption

theorem peakGap_le_peak_sub {T b ell h hF gamma delta : ℝ}
    (hbT : b ≤ T) (htotal : T + b ≤ 1) (hsquares : T ^ 2 + b ^ 2 ≤ hF)
    (hreturn : hF < h) (hidentity : gamma = (1 - ell) * h + delta)
    (hbudget : gamma ≤ 2 * T ^ 2 - ell * hF) :
    peakGap ell gamma delta ≤ T - b := by
  unfold peakGap
  split_ifs with hell
  · exact gamma_le_peak_sub hbT htotal hsquares hell hbudget
  · exact (delta_lt_peak_sub hbT htotal hsquares (lt_of_not_ge hell) hreturn hidentity hbudget).le

/-- A summable real family with a positive coordinate attains an
actual positive maximum. Only a finite excursion above that coordinate is
used; the original family itself may be infinite or uncountable. -/
theorem exists_positive_max_of_summable {ι : Type*} (a : ι → ℝ) (hsum : Summable a)
    (hpositive : ∃ i, 0 < a i) :
    ∃ j, 0 < a j ∧ ∀ i, a i ≤ a j := by
  classical
  obtain ⟨i₀, hi₀⟩ := hpositive
  have hsmall : ∀ᶠ i in cofinite, a i < a i₀ :=
    hsum.tendsto_cofinite_zero.eventually_lt_const hi₀
  have hfinite : {i | a i₀ ≤ a i}.Finite := by
    simpa only [eventually_cofinite, not_lt] using hsmall
  let s := hfinite.toFinset
  have hi₀s : i₀ ∈ s := by simp [s]
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image a ⟨i₀, hi₀s⟩
  have hij : a i₀ ≤ a j := hmax i₀ hi₀s
  refine ⟨j, hi₀.trans_le hij, ?_⟩
  intro i
  by_cases hi : a i₀ ≤ a i
  · exact hmax i (by simpa [s] using hi)
  · exact (le_of_not_ge hi).trans hij

/-- The positive budget excludes pure dust, then summability constructs the
peak rather than assuming a largest atomic part. -/
theorem exists_positive_peak_of_budget {ι : Type*} (a : ι → ℝ) (hsum : Summable a)
    (ha : ∀ i, 0 ≤ a i) {gamma ell hF : ℝ} (hgamma : 0 < gamma)
    (hell : 0 ≤ ell) (hF0 : 0 ≤ hF)
    (hbudget : gamma ≤ 2 * (massPeak a) ^ 2 - ell * hF) :
    ∃ j, 0 < a j ∧ (∀ i, a i ≤ a j) ∧ massPeak a = a j := by
  have hpositive : ∃ i, 0 < a i := by
    by_contra hn
    have hzero (i : ι) : a i = 0 :=
      le_antisymm (le_of_not_gt (fun hi => hn ⟨i, hi⟩)) (ha i)
    have hset : insert (0 : ℝ) (range a) = {0} := by
      ext x
      simp only [mem_insert_iff, mem_range, mem_singleton_iff]
      constructor
      · rintro (hx | ⟨i, hx⟩)
        · exact hx
        · exact hx.symm.trans (hzero i)
      · intro hx
        exact Or.inl hx
    have hp : massPeak a = 0 := by rw [massPeak, hset, csSup_singleton]
    rw [hp] at hbudget
    nlinarith [mul_nonneg hell hF0]
  obtain ⟨j, hj, hmax⟩ := exists_positive_max_of_summable a hsum hpositive
  have hbdd : BddAbove (insert 0 (range a)) := by
    refine ⟨a j, ?_⟩
    rintro x (rfl | ⟨i, rfl⟩)
    · exact hj.le
    · exact hmax i
  have heq : massPeak a = a j := by
    apply le_antisymm
    · apply csSup_le (by exact ⟨0, mem_insert _ _⟩)
      rintro x (rfl | ⟨i, rfl⟩)
      · exact hj.le
      · exact hmax i
    · exact le_csSup hbdd (Or.inr (mem_range_self j))
  exact ⟨j, hj, hmax, heq⟩

/-- Actual summable endpoint masses and their old-dual budget construct a
uniformly separated positive peak on the unchanged original label type. -/
theorem exists_separated_peak_of_summable_budget {ι : Type*}
    (a : ι → ℝ) (hsum : Summable a) (ha : ∀ i, 0 ≤ a i) (htotal : (∑' i, a i) ≤ 1)
    {gamma delta ell h hF : ℝ} (hgamma : 0 < gamma) (hdelta : 0 < delta) (hell : 0 ≤ ell)
    (hsquares : (∑' i, (a i) ^ 2) ≤ hF) (hreturn : hF < h)
    (hidentity : gamma = (1 - ell) * h + delta)
    (hbudget : gamma ≤ 2 * (massPeak a) ^ 2 - ell * hF) :
    ∃ j, 0 < a j ∧ massPeak a = a j ∧ 0 < peakGap ell gamma delta ∧
      IsSeparatedPeak a (peakGap ell gamma delta) j := by
  classical
  have hF0 : 0 ≤ hF := (tsum_nonneg (fun i => sq_nonneg (a i))).trans hsquares
  obtain ⟨j, hj, hmax, hpeak⟩ := exists_positive_peak_of_budget a hsum ha hgamma hell hF0 hbudget
  have hone (i : ι) : a i ≤ 1 := (hsum.le_tsum i (fun k _ => ha k)).trans htotal
  have hsq : Summable (fun i => (a i) ^ 2) :=
    hsum.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => by nlinarith [ha i, hone i])
  refine ⟨j, hj, hpeak, peakGap_pos hgamma hdelta, ?_⟩
  intro i hij
  have hmass : a j + a i ≤ 1 := by
    simpa only [Finset.sum_pair hij.symm] using
      (hsum.sum_le_tsum {j, i} (fun k _ => ha k)).trans htotal
  have hpair : (a j) ^ 2 + (a i) ^ 2 ≤ hF := by
    simpa only [Finset.sum_pair hij.symm] using
      (hsq.sum_le_tsum {j, i} (fun k _ => sq_nonneg (a k))).trans hsquares
  have hb : gamma ≤ 2 * (a j) ^ 2 - ell * hF := by simpa only [hpeak] using hbudget
  have hg := peakGap_le_peak_sub (hmax i) hmass hpair hreturn hidentity hb
  linarith

/-- A positive common gap makes the actual peak label unique. -/
theorem IsSeparatedPeak.unique {ι : Type*} {a : ι → ℝ} {Δ : ℝ} {i j : ι}
    (hi : IsSeparatedPeak a Δ i) (hj : IsSeparatedPeak a Δ j) (hΔ : 0 < Δ) : i = j := by
  by_contra hne
  have h₁ := hi j (fun he => hne he.symm)
  have h₂ := hj i hne
  linarith

end Erdos1017.ForwardPeak
