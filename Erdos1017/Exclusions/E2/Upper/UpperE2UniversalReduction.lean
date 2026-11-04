module

public import Erdos1017.Exclusions.E2.Upper.UpperE2UniversalBoundaryCertificates

/-!
# Reduction of the original price to the enlarged domain

`originalReciprocal` and `originalPrice` are the original reciprocal allowance
and positive-price scalar before enlargement; every original positive-price
configuration is bounded by the enlarged scalar on its feasible domain, and the
original positive-price scalar is strictly negative on its resource domain
(`originalPrice_neg`).
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.UpperE2UniversalScalar

/-- The original reciprocal allowance uses its original hole mass,
whole-atom moment and own-part denominator. -/
def originalReciprocal (A b u z q : ℝ) : ℝ :=
  let k := A - z
  let alpha := min (1 - 2 * A - b) (Real.sqrt q)
  (1 - A - b - u) / k + q / (k * (k - alpha))

/-- The necessary original positive-price scalar before enlargement. -/
def originalPrice (A b u z q ell gamma : ℝ) : ℝ :=
  (b * ell - gamma) * originalReciprocal A b u z q +
    (ell - 1 / 2) * z +
    min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell) / 2 -
    ell * (A - b) - 2 * gamma / 5

/-- The original shared moment and missing-row cap pay the entire
enlarged constant domain, including its new positive-price mass floor. -/
theorem original_domain_enlarges {A b u z q ell gamma : ℝ}
    (hA : (1 / 3 : ℝ) ≤ A) (hb : b ∈ Icc (0 : ℝ) (1 - 2 * A))
    (hz : 0 ≤ z) (hzu : z ≤ u)
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hgamma : gammaFloor ell ≤ gamma) (hprice : 0 ≤ b * ell - gamma)
    (hcap : z ≤ min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell))
    (hq : 0 ≤ q)
    (hpack : q + z ^ 2 ≤ 3509 / 14884 - A ^ 2 - b ^ 2 -
      2 * b * (1 - A - b - u)) :
    b ∈ Icc (77 / 1098 : ℝ) (1 / 4) ∧ z ∈ Icc (0 : ℝ) b ∧
      1547 / 4026 - b + (4 / 5 : ℝ) * z ≤ 2 / 3 - b - u ∧
      2 / 3 - b - u ≤ 2 / 3 - b - z ∧
      q ≤ enlargedQ b z (2 / 3 - b - u) := by
  have hell0 : 0 < ell := by linarith only [hell.1]
  have hbthird : b ≤ 1 / 3 := by linarith only [hA, hb.2]
  have hbprice := mul_le_mul_of_nonneg_right hell.2
    (show 0 ≤ b + 23 / 100 by linarith only [hb.1])
  have hb0 : (77 / 1098 : ℝ) ≤ b := by
    dsimp only [gammaFloor] at hgamma
    nlinarith only [hgamma, hprice, hbprice]
  have hzgeom := le_trans hcap (min_le_left _ _)
  have hzrow := (le_div_iff₀ hell0).mp (le_trans hcap (min_le_right _ _))
  have hzb : z ≤ b := by linarith only [hzgeom, hA]
  have hAell := mul_nonneg (sub_nonneg.mpr hA) hell0.le
  have hellz := mul_nonneg (sub_nonneg.mpr hell.1) hz
  have hellK := mul_nonneg (sub_nonneg.mpr hell.2) (by norm_num : (0 : ℝ) ≤ 7 / 300)
  have heta : 1547 / 4026 - b + (4 / 5 : ℝ) * z ≤ 2 / 3 - b - u := by
    dsimp only [gammaFloor] at hgamma
    nlinarith only [hzrow, hgamma, hAell, hellz, hellK]
  have hmoment := mul_nonneg (sub_nonneg.mpr hA)
    (show 0 ≤ A + 1 / 3 - 2 * b by linarith only [hA, hbthird])
  have hQ : q ≤ enlargedQ b z (2 / 3 - b - u) := by
    dsimp only [enlargedQ]
    nlinarith only [hpack, hmoment]
  have hetab := mul_nonneg hb.1 (sub_nonneg.mpr heta)
  have hdrop : (1 / 3 : ℝ) ^ 2 - b ^ 2 + 2 * b * (1547 / 4026) ≤
      3509 / 14884 := by
    have hzprod := mul_nonneg hb.1 hz
    dsimp only [enlargedQ] at hQ
    nlinarith only [hQ, hq, sq_nonneg z, hetab, hzprod]
  have hbquarter : b < 1 / 4 := by
    by_contra! hn
    have hprod := mul_nonneg (sub_nonneg.mpr hn)
      (show 0 ≤ 2 * (1547 / 4026 : ℝ) - b - 1 / 4 by linarith only [hbthird])
    nlinarith only [hprod, hdrop]
  exact ⟨⟨hb0, hbquarter.le⟩, ⟨hz, hzb⟩, heta, by linarith only [hzu], hQ⟩

/-- The enlarged moment cap pays every smaller moment's pole before
the mass or moment is changed. -/
theorem enlarged_smaller_moment_pole {b z eta q : ℝ}
    (hb : b ∈ Icc (77 / 1098 : ℝ) (1 / 4))
    (hz : z ∈ Icc (0 : ℝ) b)
    (heta : 1547 / 4026 - b + (4 / 5 : ℝ) * z ≤ eta)
    (hq : 0 ≤ q) (hQ : q ≤ enlargedQ b z eta) :
    1 / 200 < (1 / 3 - z) - min (1 / 3 - b) (Real.sqrt q) := by
  have hpole := enlarged_pole_pos hb hz heta (hq.trans hQ)
  have hsqrt := Real.sqrt_le_sqrt hQ
  have hmin := min_le_min_left (1 / 3 - b) hsqrt
  linarith only [hpole, hmin]

/-- A common positive pole licenses simultaneous enlargement of the
numerators and decrease of both reciprocal denominator factors. -/
theorem reciprocal_resource_mono {eta eta' k k' alpha alpha' q q' : ℝ}
    (heta : 0 ≤ eta) (heta' : eta ≤ eta')
    (hq : 0 ≤ q) (hqq : q ≤ q')
    (hk : k' ≤ k) (ha : alpha ≤ alpha') (ha' : 0 ≤ alpha')
    (hpole : 0 < k' - alpha') :
    eta / k + q / (k * (k - alpha)) ≤
      eta' / k' + q' / (k' * (k' - alpha')) := by
  have hk' : 0 < k' := by linarith only [ha', hpole]
  have hk0 : 0 < k := lt_of_lt_of_le hk' hk
  have hgap : k' - alpha' ≤ k - alpha := by linarith only [hk, ha]
  have hden' : 0 < k' * (k' - alpha') := mul_pos hk' hpole
  have hden : 0 < k * (k - alpha) := mul_pos hk0 (lt_of_lt_of_le hpole hgap)
  have hdenle : k' * (k' - alpha') ≤ k * (k - alpha) :=
    mul_le_mul hk hgap hpole.le hk0.le
  apply add_le_add
  · apply (div_le_div_iff₀ hk0 hk').mpr
    have h1 := mul_le_mul_of_nonneg_right heta' hk'.le
    have h2 := mul_le_mul_of_nonneg_left hk (heta.trans heta')
    linarith only [h1, h2]
  · apply (div_le_div_iff₀ hden hden').mpr
    have h1 := mul_le_mul_of_nonneg_right hqq hden'.le
    have h2 := mul_le_mul_of_nonneg_left hdenle (hq.trans hqq)
    linarith only [h1, h2]

/-- The relaxed scalar fixes the universal mass and intercept floor,
while keeping the original multiplier until its final enlargement. -/
def relaxedPrice (b u z I ell : ℝ) : ℝ :=
  (ell * (b + 23 / 100) - 16477 / 67100) * I + (ell - 1 / 2) * z +
    min b (7 / 300 + (1 - u - 3 * (16477 / 67100)) / ell) / 2 -
    ell * (1 / 3 - b) - 2 * gammaFloor ell / 5

/-- The capped reciprocal row loses at most the paid linear allowance
when the multiplier increases, including either active cap branch. -/
theorem capped_reciprocal_difference {b K t x y L : ℝ}
    (hL : 0 < L) (hx : L ≤ x) (hxy : x ≤ y) (hb : K ≤ b) :
    min b (K + t / x) - min b (K + t / y) ≤ (y - x) * (b - K) / L := by
  have hx0 : 0 < x := lt_of_lt_of_le hL hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hright : 0 ≤ (y - x) * (b - K) / L :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hb)) hL.le
  by_cases hactive : b ≤ K + t / y
  · rw [min_eq_left hactive]
    exact (sub_nonpos.mpr (min_le_left _ _)).trans hright
  · rw [min_eq_right (le_of_not_ge hactive)]
    have ht : t / y ≤ b - K := by linarith only [le_of_not_ge hactive]
    have hfactor : 0 ≤ (y - x) / x := div_nonneg (sub_nonneg.mpr hxy) hx0.le
    have hdiff : t / x - t / y = (t / y) * ((y - x) / x) := by
      field_simp
    have hscaled := mul_le_mul_of_nonneg_right ht hfactor
    have hden : (b - K) * ((y - x) / x) ≤ (y - x) * (b - K) / L := by
      simp only [← mul_div_assoc]
      apply (div_le_div_iff₀ hx0 hL).mpr
      have h := mul_le_mul_of_nonneg_left hx
        (mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hxy))
      nlinarith only [h]
    have hstart := min_le_right b (K + t / x)
    linarith only [hstart, hdiff, hscaled, hden]

/-- The exact multiplier increment is positive on the entire enlarged
head-mass interval. -/
theorem relaxed_increment_pos {b : ℝ}
    (hb : b ∈ Icc (77 / 1098 : ℝ) (1 / 4)) :
    0 < 3 * (b + 23 / 100) * (1547 / 4026 - b) + b - 1 / 3 +
      2 * (23 / 100) / 5 - (b - 7 / 300) / (2 * (4 / 5)) := by
  have hprod := mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hb.2)
  norm_num at *
  nlinarith only [hprod, hb.1, hb.2]

/-- The finite-difference cap bound pays the increase to the closed
upper multiplier endpoint. No interval endpoint is divided by zero. -/
theorem relaxedPrice_le_endpoint {b u z I ell : ℝ}
    (hb : b ∈ Icc (77 / 1098 : ℝ) (1 / 4)) (hz : 0 ≤ z)
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hI : 3 * (1547 / 4026 - b) ≤ I) :
    relaxedPrice b u z I ell ≤ relaxedPrice b u z I (9 / 11) := by
  have hcap := capped_reciprocal_difference (K := 7 / 300)
    (t := 1 - u - 3 * (16477 / 67100)) (by norm_num : (0 : ℝ) < 4 / 5)
    hell.1 hell.2 (show (7 / 300 : ℝ) ≤ b by linarith only [hb.1])
  have hIprod := mul_nonneg (show 0 ≤ b + 23 / 100 by linarith only [hb.1])
    (sub_nonneg.mpr hI)
  have hinc := relaxed_increment_pos hb
  have hpaid := mul_nonneg (sub_nonneg.mpr hell.2)
    (show 0 ≤ (b + 23 / 100) * I + z - (1 / 3 - b) +
      2 * (23 / 100) / 5 - (b - 7 / 300) / (2 * (4 / 5)) by
        nlinarith only [hIprod, hinc, hz])
  dsimp only [relaxedPrice, gammaFloor]
  norm_num only at *
  nlinarith only [hcap, hpaid]

/-- The reciprocal on the paid enlarged domain uses its maximal moment. -/
def enlargedReciprocal (b z eta : ℝ) : ℝ :=
  let k := 1 / 3 - z
  let Q := enlargedQ b z eta
  eta / k + Q / (k * (k - min (1 / 3 - b) (Real.sqrt Q)))

/-- The same enlarged pole pays the original reciprocal comparison,
including the increase of the original moment to its shared inventory cap. -/
theorem originalReciprocal_le_enlarged {A b u z q : ℝ}
    (hA : (1 / 3 : ℝ) ≤ A)
    (hb : b ∈ Icc (77 / 1098 : ℝ) (1 / 4)) (hz : z ∈ Icc (0 : ℝ) b)
    (heta : 1547 / 4026 - b + (4 / 5 : ℝ) * z ≤ 2 / 3 - b - u)
    (heta0 : 0 ≤ 1 - A - b - u)
    (hq : 0 ≤ q) (hQ : q ≤ enlargedQ b z (2 / 3 - b - u)) :
    originalReciprocal A b u z q ≤ enlargedReciprocal b z (2 / 3 - b - u) := by
  have hpole := enlarged_pole_pos hb hz heta (hq.trans hQ)
  have halpha : 0 ≤ min (1 / 3 - b)
      (Real.sqrt (enlargedQ b z (2 / 3 - b - u))) :=
    le_min (by linarith only [hb.2]) (Real.sqrt_nonneg _)
  exact reciprocal_resource_mono heta0 (by linarith only [hA]) hq hQ
    (by linarith only [hA])
    (min_le_min (by linarith only [hA]) (Real.sqrt_le_sqrt hQ)) halpha
    (by linarith only [hpole])

/-- The enlarged reciprocal retains the lower mass resource needed for
the finite multiplier increment. -/
theorem enlargedReciprocal_lower {b z eta : ℝ}
    (hb : b ∈ Icc (77 / 1098 : ℝ) (1 / 4)) (hz : z ∈ Icc (0 : ℝ) b)
    (heta : 1547 / 4026 - b + (4 / 5 : ℝ) * z ≤ eta)
    (hQ : 0 ≤ enlargedQ b z eta) :
    3 * (1547 / 4026 - b) ≤ enlargedReciprocal b z eta := by
  have heta0 : 0 ≤ eta := by linarith only [heta, hb.2, hz.1]
  have hk : 0 < 1 / 3 - z := by linarith only [hz.2, hb.2]
  have hpole := enlarged_pole_pos hb hz heta hQ
  have hcorrection : 0 ≤ enlargedQ b z eta /
      ((1 / 3 - z) * ((1 / 3 - z) -
        min (1 / 3 - b) (Real.sqrt (enlargedQ b z eta)))) :=
    div_nonneg hQ (mul_nonneg hk.le (by linarith only [hpole]))
  have hthree : 3 * eta ≤ eta / (1 / 3 - z) := by
    apply (le_div_iff₀ hk).mpr
    have hprod := mul_nonneg heta0 hz.1
    nlinarith only [hprod]
  dsimp only [enlargedReciprocal]
  linarith only [hcorrection, hthree, heta, hz.1]

/-- Lowering the intercept and universal mass, and enlarging the
original moment, all use the one already paid enlarged reciprocal. -/
theorem originalPrice_le_relaxed {A b u z q ell gamma : ℝ}
    (hA : (1 / 3 : ℝ) ≤ A)
    (hb : b ∈ Icc (77 / 1098 : ℝ) (1 / 4)) (hz : z ∈ Icc (0 : ℝ) b)
    (heta : 1547 / 4026 - b + (4 / 5 : ℝ) * z ≤ 2 / 3 - b - u)
    (heta0 : 0 ≤ 1 - A - b - u)
    (hq : 0 ≤ q) (hQ : q ≤ enlargedQ b z (2 / 3 - b - u))
    (hell : 0 < ell) (hgamma : gammaFloor ell ≤ gamma)
    (hprice : 0 ≤ b * ell - gamma) :
    originalPrice A b u z q ell gamma ≤
      relaxedPrice b u z (enlargedReciprocal b z (2 / 3 - b - u)) ell := by
  have hrecip := originalReciprocal_le_enlarged hA hb hz heta heta0 hq hQ
  have hI0 : 0 ≤ enlargedReciprocal b z (2 / 3 - b - u) :=
    (show 0 ≤ 3 * (1547 / 4026 - b) by linarith only [hb.2]).trans
      (enlargedReciprocal_lower hb hz heta (hq.trans hQ))
  have hmul := (mul_le_mul_of_nonneg_left hrecip hprice).trans
    (mul_le_mul_of_nonneg_right
      (show b * ell - gamma ≤ ell * (b + 23 / 100) - 16477 / 67100 by
        dsimp only [gammaFloor] at hgamma
        nlinarith only [hgamma]) hI0)
  have hAell := mul_nonneg (sub_nonneg.mpr hA) hell.le
  have hnum : 1 - u - 2 * ell * A - 3 * gamma ≤
      ell * (7 / 300) + (1 - u - 3 * (16477 / 67100)) := by
    dsimp only [gammaFloor] at hgamma
    nlinarith only [hgamma, hAell]
  have hdiv := div_le_div_of_nonneg_right hnum hell.le
  have hrewrite : (ell * (7 / 300) + (1 - u - 3 * (16477 / 67100))) / ell =
      7 / 300 + (1 - u - 3 * (16477 / 67100)) / ell := by
    field_simp [hell.ne']
  rw [hrewrite] at hdiv
  have hcap := min_le_min (show 1 - 3 * A + b ≤ b by linarith only [hA]) hdiv
  dsimp only [originalPrice, relaxedPrice, gammaFloor]
  dsimp only [gammaFloor] at hgamma
  norm_num only at *
  nlinarith only [hmul, hcap, hAell, hgamma]

/-- At the closed multiplier endpoint the relaxed scalar is exactly
the enlarged five-boundary expression, with its actual moving cap. -/
theorem relaxedPrice_endpoint_eq_enlarged (b u z : ℝ) :
    relaxedPrice b u z (enlargedReciprocal b z (2 / 3 - b - u)) (9 / 11) =
      (9 / 11) * enlargedF b z (2 / 3 - b - u) := by
  have hcap : 7 / 300 + (1 - u - 3 * (16477 / 67100 : ℝ)) / (9 / 11) =
      ((2 / 3 - b - u) + b - 1547 / 4026) / (9 / 11) := by ring
  dsimp only [relaxedPrice, enlargedF, enlargedReciprocal, gammaFloor]
  rw [hcap]
  ring

/-- Every original positive-price configuration is bounded by the
enlarged scalar on its proved feasible domain. -/
theorem originalPrice_le_enlargedF {A b u z q ell gamma : ℝ}
    (hA : (1 / 3 : ℝ) ≤ A) (hb : b ∈ Icc (0 : ℝ) (1 - 2 * A))
    (hz : 0 ≤ z) (hzu : z ≤ u) (heta0 : 0 ≤ 1 - A - b - u)
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hgamma : gammaFloor ell ≤ gamma) (hprice : 0 ≤ b * ell - gamma)
    (hcap : z ≤ min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell))
    (hq : 0 ≤ q)
    (hpack : q + z ^ 2 ≤ 3509 / 14884 - A ^ 2 - b ^ 2 -
      2 * b * (1 - A - b - u)) :
    originalPrice A b u z q ell gamma ≤
      (9 / 11) * enlargedF b z (2 / 3 - b - u) := by
  obtain ⟨hb', hz', heta, _, hQ⟩ :=
    original_domain_enlarges hA hb hz hzu hell hgamma hprice hcap hq hpack
  calc
    _ ≤ relaxedPrice b u z (enlargedReciprocal b z (2 / 3 - b - u)) ell :=
      originalPrice_le_relaxed hA hb' hz' heta heta0 hq hQ
        (by linarith only [hell.1]) hgamma hprice
    _ ≤ relaxedPrice b u z (enlargedReciprocal b z (2 / 3 - b - u)) (9 / 11) :=
      relaxedPrice_le_endpoint hb' hz hell
        (enlargedReciprocal_lower hb' hz' heta (hq.trans hQ))
    _ = _ := relaxedPrice_endpoint_eq_enlarged b u z

/-- The original positive-price scalar is strictly negative on its
actual resource domain; all enlarged boundary signs are proved internally. -/
theorem originalPrice_neg {A b u z q ell gamma : ℝ}
    (hA : (1 / 3 : ℝ) ≤ A) (hb : b ∈ Icc (0 : ℝ) (1 - 2 * A))
    (hz : 0 ≤ z) (hzu : z ≤ u) (heta0 : 0 ≤ 1 - A - b - u)
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hgamma : gammaFloor ell ≤ gamma) (hprice : 0 ≤ b * ell - gamma)
    (hcap : z ≤ min (1 - 3 * A + b) ((1 - u - 2 * ell * A - 3 * gamma) / ell))
    (hq : 0 ≤ q)
    (hpack : q + z ^ 2 ≤ 3509 / 14884 - A ^ 2 - b ^ 2 -
      2 * b * (1 - A - b - u)) :
    originalPrice A b u z q ell gamma < 0 := by
  obtain ⟨hb', hz', heta, huet, hQ⟩ :=
    original_domain_enlarges hA hb hz hzu hell hgamma hprice hcap hq hpack
  have hnegative := enlargedF_neg hb' hz' heta huet (hq.trans hQ)
  have hupper := originalPrice_le_enlargedF hA hb hz hzu heta0 hell hgamma hprice
    hcap hq hpack
  exact hupper.trans_lt (mul_neg_of_pos_of_neg (by norm_num) hnegative)

end Erdos1017.UpperE2UniversalScalar
