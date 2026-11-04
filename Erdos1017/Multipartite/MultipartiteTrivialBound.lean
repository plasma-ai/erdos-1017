module

public import Erdos1017.Multipartite.MultipartiteExcessSelection

/-!
# Elementary star-cost bound and the low-density comparison

The countable value obeys the elementary star-cost bound, the normalized
fractional value is at most the edge density, and below density one quarter this
gives the comparison with `B` (`normalizedValue_le_benchmark_of_le_quarter`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Bounded sign charges give the elementary star-cost bound for every
actual countable objective. -/
theorem objective_le_total {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) :
    objective p s D ≤ s + ∑' i, p i := by
  have hheads : Summable (fun i => head D i * p i) :=
    hsum.of_nonneg_of_le (fun i => mul_nonneg (hD.1.1 _) (hp i))
      (fun i => mul_le_of_le_one_left (hp i) (hD.1.2 _))
  have hheadsum : (∑' i, head D i * p i) ≤ ∑' i, p i :=
    hheads.tsum_le_tsum (fun i => mul_le_of_le_one_left (hp i) (hD.1.2 _)) hsum
  have hlinear : linear D * s ≤ s := mul_le_of_le_one_left hs (hD.1.2 _)
  have hpairs : 0 ≤ ∑' z : ℕ × ℕ,
      if z.1 < z.2 then pair D z.1 z.2 * p z.1 * p z.2 else 0 := by
    apply tsum_nonneg
    intro z
    split_ifs
    · exact mul_nonneg (mul_nonneg (hD.1.1 _) (hp _)) (hp _)
    · rfl
  have hincidents : 0 ≤ ∑' i, incident D i * p i * s :=
    tsum_nonneg fun i => mul_nonneg (mul_nonneg (hD.1.1 _) (hp i)) hs
  have hpenalty : 0 ≤ penalty D * s ^ 2 / 2 := by
    exact div_nonneg (mul_nonneg (hD.1.1 _) (sq_nonneg _)) (by norm_num)
  unfold objective
  linarith

end Erdos1017.MultipartiteCountableDual

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators

/-- The actual countable value obeys the elementary star-cost bound. -/
theorem limitValue_le_total {L : ℝ} {x : Profile} (hx : x ∈ space L) : limitValue x ≤ x.1 := by
  obtain ⟨D, hD, hopt⟩ := MultipartiteCountableDual.exists_profile_optimal hx
  rw [hopt]
  have h := MultipartiteCountableDual.objective_le_total hD x.2 hx.1.1.2 (atoms_summable hx)
    (dust x) (dust_nonneg hx)
  exact h.trans (by rw [dust_eq_sub_tsum hx]; linarith)

/-- The square moment is bounded by the square of the actual total mass. -/
theorem squareMoment_le_total_sq {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    (∑' i, (x.2 i) ^ 2) ≤ x.1 ^ 2 := by
  have hp : ∀ i, 0 ≤ x.2 i := hx.1.1.2
  have hsum := atoms_summable hx
  have hsumT : (∑' i, x.2 i) ≤ x.1 := by
    have h := dust_nonneg hx
    rw [dust_eq_sub_tsum hx] at h
    linarith
  have hpoint (i : ℕ) : (x.2 i) ^ 2 ≤ x.1 * x.2 i := by
    have hi := (hsum.le_tsum i (fun _ _ => hp _)).trans hsumT
    nlinarith [mul_nonneg (sub_nonneg.mpr hi) (hp i)]
  have h := (squares_summable hx).tsum_le_tsum hpoint (hsum.mul_left x.1)
  rw [tsum_mul_left] at h
  have htotal := mul_le_mul_of_nonneg_left hsumT hx.1.1.1
  nlinarith

/-- The normalized actual fractional value is at most its actual graph
edge density, including countably many heads and genuine clique dust. -/
theorem normalizedValue_le_density {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    normalizedValue x ≤ density x := by
  have hM : 0 < 1 + x.1 := by linarith [hx.1.1.1]
  have hC := limitValue_le_total hx
  have hQ := squareMoment_le_total_sq hx
  have hdensity : density x = (x.1 + (x.1 ^ 2 - ∑' i, (x.2 i) ^ 2) / 2) / (1 + x.1) ^ 2 := by
    unfold density missingDensity
    field_simp
    ring
  rw [hdensity]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- The complete actual normalized profile comparison below density one
quarter follows from the proved benchmark identity. -/
theorem normalizedValue_le_benchmark_of_le_quarter {L : ℝ} {x : Profile}
    (hx : x ∈ space L) (hd : density x ≤ 1 / 4) : normalizedValue x ≤ benchmark (density x) := by
  rw [benchmark_of_le_quarter hd]
  exact normalizedValue_le_density hx

end Erdos1017.MultipartiteProfiles
