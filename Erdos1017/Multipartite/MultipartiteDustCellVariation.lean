module

public import Erdos1017.Multipartite.Dust.CountableDustCellSurgery
public import Erdos1017.Multipartite.MultipartiteGamma

/-!
# Dust-cell surgery at a selected optimum

A positive dust cell can become an independent head with twice the original dust
row, with an exact original-head/anchor correction preserving density, and this
surgery forces the internal dust penalty above the stationary dust row.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- A positive dust cell becomes an actual independent head with twice the
old dust row. An exact old-head/anchor correction preserves density. -/
theorem dust_cell_local_max {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (hi : 0 < x.2 i) (hs : 0 < MultipartiteProfiles.dust x) :
    ∃ η : ℝ, 0 < η ∧ ∀ z r : ℝ, 0 < z → z < η → |r| < η →
      2 * (1 - x.2 i) * r + 2 * r ^ 2 + z ^ 2 = 0 →
      z * (dustRow x.2 (MultipartiteProfiles.dust x) D - penalty D) -
        (headRow x.2 (MultipartiteProfiles.dust x) D i -
          anchorRow x.2 (MultipartiteProfiles.dust x) D) * r - head D i * r ^ 2 +
        (incident D i + linear D - penalty D) * z * r + 3 * penalty D * z ^ 2 / 2 ≤ 0 := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.1.2
  have hsum := MultipartiteProfiles.atoms_summable hx.1
  have hsqsum := MultipartiteProfiles.squares_summable hx.1
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hx hε hxvalue).1
  let b := Real.sqrt (∑' k, (x.2 k) ^ 2)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = ∑' k, (x.2 k) ^ 2 := Real.sq_sqrt (tsum_nonneg fun k => sq_nonneg _)
  have hb1 : b < 1 := by nlinarith
  have hpb (k : ℕ) : x.2 k ≤ b := by
    have hk := hsqsum.le_tsum k (fun _ _ => sq_nonneg _)
    nlinarith [hp k]
  let η := min (x.2 i / 4) (min (MultipartiteProfiles.dust x / 2) ((1 - b) / 4))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hηi : η ≤ x.2 i / 4 := min_le_left _ _
  have hηs : η ≤ MultipartiteProfiles.dust x / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηb : η ≤ (1 - b) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, ?_⟩
  intro z r hz hzη hr hconstraint
  have hr' := abs_lt.mp hr
  have hcorr : 0 ≤ x.2 i - r := by linarith
  have hsd : 0 ≤ MultipartiteProfiles.dust x - z := by linarith
  have ha : 0 < 1 + r := by linarith
  let q := Function.update x.2 i (x.2 i - r)
  have hq (k : ℕ) : 0 ≤ q k := by
    by_cases hk : k = i
    · subst k
      simpa [q] using hcorr
    · simpa [q, Function.update_of_ne, hk] using hp k
  have hqsum : Summable q := hsum.update i _
  have hqsq : Summable (fun k => (q k) ^ 2) := by
    have heq : (fun k => (q k) ^ 2) = Function.update (fun k => (x.2 k) ^ 2) i ((x.2 i - r) ^ 2) := by
      funext k
      by_cases hk : k = i <;> simp [q, Function.update_of_ne, hk]
    rw [heq]
    exact hsqsum.update i _
  let p := prependMass z q
  have hp' : ∀ k, 0 ≤ p k := prependMass_nonneg q hq z hz.le
  have hp1' (k : ℕ) : p k ≤ 1 + r := by
    cases k with
    | zero => change z ≤ 1 + r; linarith
    | succ k =>
      change q k ≤ 1 + r
      by_cases hk : k = i
      · subst k
        simp only [q, Function.update_self]
        linarith [hpb i]
      · simp only [q, Function.update_of_ne hk]
        linarith [hpb k]
  have htotal : 1 + r + (MultipartiteProfiles.dust x - z) + (∑' k, p k) = 1 + x.1 := by
    rw [show p = prependMass z q from rfl, prependMass_tsum q hqsum z,
      show q = Function.update x.2 i (x.2 i - r) from rfl,
      (hsum.hasSum.update i (x.2 i - r)).tsum_eq,
      MultipartiteProfiles.dust_eq_sub_tsum hx.1]
    ring
  have hqmoment : (∑' k, (q k) ^ 2) = (∑' k, (x.2 k) ^ 2) - 2 * x.2 i * r + r ^ 2 := by
    have hqdef : q = Function.update x.2 i (x.2 i + (-r)) := by
      dsimp only [q]
      congr 1
    rw [hqdef, square_tsum_update x.2 hsqsum i (-r)]
    ring
  have hmoment : (1 + r) ^ 2 + (∑' k, (p k) ^ 2) =
      2 * ε * (1 + r + (MultipartiteProfiles.dust x - z) + ∑' k, p k) ^ 2 := by
    rw [htotal, show p = prependMass z q from rfl, prependMass_square_tsum q hqsq z, hqmoment]
    have hold : 1 + (∑' k, (x.2 k) ^ 2) = 2 * ε * (1 + x.1) ^ 2 := hx.2
    nlinarith
  have hpen : 0 ≤ penalty (prependDustHead D) := hD.1.1 _
  have hraw := physicalObjective_le_density_maximum_of_bounded_tests hε hmax hxvalue.le
    (prependDustHead D) 3 (by norm_num) (prependDustHead_bound hD) (prependDustHead_tests hD) hpen
    (1 + r) ha p hp' hp1' (prependMass_summable q hqsum z)
    (MultipartiteProfiles.dust x - z) hsd hmoment
  rw [htotal] at hraw
  have hden : 0 < (1 + x.1) ^ 2 := by
    have hx0 : 0 ≤ x.1 := hx.1.1.1.1
    positivity
  have hbound := (div_le_div_iff_of_pos_right hden).mp hraw
  have hcorrObj : physicalObjective (1 + r) q (MultipartiteProfiles.dust x) D =
      objective x.2 (MultipartiteProfiles.dust x) D -
        (headRow x.2 (MultipartiteProfiles.dust x) D i - anchorRow x.2 (MultipartiteProfiles.dust x) D) * r -
        head D i * r ^ 2 := by
    rw [physicalObjective_eq_objective, show q = Function.update x.2 i (x.2 i - r) from rfl,
      objective_update hD x.2 hp hsum (MultipartiteProfiles.dust x) i _ hcorr,
      anchorRow_update hD x.2 hp hsum (MultipartiteProfiles.dust x) i]
    ring
  have hnewObj := physicalObjective_prependDustHead_gain hD q hq hqsum (1 + r) z
    (MultipartiteProfiles.dust x) hz.le
  rw [hcorrObj, show q = Function.update x.2 i (x.2 i - r) from rfl,
    dustRow_head_update hD x.2 hp hsum (MultipartiteProfiles.dust x) i] at hnewObj
  rw [show p = prependMass z q from rfl, hnewObj, hopt] at hbound
  nlinarith

/-- The actual independent dust-cell surgery forces the internal dust
penalty above the stationary dust row. -/
theorem dust_penalty_floor {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (hi : 0 < x.2 i) (hs : 0 < MultipartiteProfiles.dust x) :
    dustRow x.2 (MultipartiteProfiles.dust x) D ≤ penalty D := by
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hx hε hxvalue).1
  have hiQ := (MultipartiteProfiles.squares_summable hx.1).le_tsum i (fun _ _ => sq_nonneg _)
  have hpi : x.2 i < 1 := by nlinarith
  obtain ⟨η, hη, hlocal⟩ := dust_cell_local_max hε hx hmax hxvalue hD hopt i hi hs
  have hlinear := Variation.tangent_linear_nonpos_of_right_local_max
    1 (2 * (1 - x.2 i)) 0 2
    (dustRow x.2 (MultipartiteProfiles.dust x) D - penalty D)
    (-(headRow x.2 (MultipartiteProfiles.dust x) D i - anchorRow x.2 (MultipartiteProfiles.dust x) D))
    (3 * penalty D / 2) ((incident D i + linear D - penalty D) / 2) (-head D i)
    (by linarith) η hη (by
      intro z r hz hzη hr hroot
      have hconstraint : 2 * (1 - x.2 i) * r + 2 * r ^ 2 + z ^ 2 = 0 := by nlinarith
      have h := hlocal z r hz hzη hr hconstraint
      convert h using 1
      ring)
  exact sub_nonpos.mp hlinear

end Erdos1017.MultipartiteCountableDual
