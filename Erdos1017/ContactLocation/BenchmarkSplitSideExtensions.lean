module

public import Erdos1017.ContactLocation.BenchmarkSplitCurvature

/-!
# Analytic split extensions on either side of a cusp

This module defines the analytic split extension `splitDensityExtension` of each
index, `C²` with strictly negative curvature below density one half, and shows
that at a reciprocal cusp the benchmark agrees on the left with the extension of
index `m-1` and on the right with that of index `m`.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Erdos1017.Benchmark

def splitDensityExtension (j : ℕ) (d : ℝ) : ℝ :=
  splitPolynomial j (Real.sqrt (1 - 2 * d))

private theorem split_cusp_sqrt (m : ℕ) (hm : 0 < m) :
    Real.sqrt (1 - 2 * ((1 - 1 / (m : ℝ) ^ 2) / 2)) = 1 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have heq : 1 - 2 * ((1 - 1 / (m : ℝ) ^ 2) / 2) = (1 / (m : ℝ)) ^ 2 := by ring
  rw [heq, Real.sqrt_sq (by positivity)]

/-- Every reciprocal cusp with count at least three lies strictly inside
the actual split-active band. -/
theorem split_cusp_mem_band (m : ℕ) (hm : 3 ≤ m) :
    (1 - 1 / (m : ℝ) ^ 2) / 2 ∈ Ioo (1 / 2 - epsilonStar) (1 / 2) := by
  have hmreal : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hsqrt : Real.sqrt (21 : ℝ) < 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21), Real.sqrt_nonneg (21 : ℝ)]
  have hstar : (1 / 18 : ℝ) < epsilonStar := by
    unfold epsilonStar
    linarith
  have hsq : (9 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hrecip : 1 / (m : ℝ) ^ 2 ≤ (1 / 9 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hsq
  constructor
  · linarith
  · have : 0 < 1 / (m : ℝ) ^ 2 := by positivity
    linarith

/-- Each analytic split extension is C² below density one half. -/
theorem splitDensityExtension_contDiffAt (j : ℕ) {d : ℝ} (hd : d < 1 / 2) :
    ContDiffAt ℝ 2 (splitDensityExtension j) d := by
  have hinner : ContDiffAt ℝ 2 (fun x : ℝ => 1 - 2 * x) d := by fun_prop
  have hs := hinner.sqrt (show 1 - 2 * d ≠ 0 by linarith)
  unfold splitDensityExtension splitPolynomial
  exact (((contDiffAt_const.mul (hs.pow 2)).add
    (contDiffAt_const.mul hs)).sub contDiffAt_const).div_const _

/-- Ordinary second derivative of a positive-index analytic split extension. -/
theorem splitDensityExtension_second_deriv (j : ℕ) (hj : 0 < j)
    {d : ℝ} (hd : d < 1 / 2) :
    deriv (deriv (splitDensityExtension j)) d =
      -2 / ((j : ℝ) * Real.sqrt (1 - 2 * d) ^ 3) := by
  have hnear : ∀ᶠ x in nhds d, x < 1 / 2 := Iio_mem_nhds hd
  have heq : deriv (splitDensityExtension j) =ᶠ[nhds d]
      (fun x : ℝ => 2 * (2 * (j : ℝ) + 1) / ((j : ℝ) * ((j : ℝ) + 1)) -
        2 / ((j : ℝ) * Real.sqrt (1 - 2 * x))) := by
    filter_upwards [hnear] with x hx
    exact (splitPolynomial_density_hasDerivAt j hj hx).deriv
  rw [heq.deriv_eq]
  exact (splitPolynomial_density_slope_hasDerivAt j hj hd).deriv

/-- Ordinary curvature of every positive-index analytic split extension
is strictly negative below density one half. -/
theorem splitDensityExtension_second_deriv_neg (j : ℕ) (hj : 0 < j)
    {d : ℝ} (hd : d < 1 / 2) :
    deriv (deriv (splitDensityExtension j)) d < 0 := by
  rw [splitDensityExtension_second_deriv j hj hd]
  exact splitPolynomial_density_curvature_neg j hj hd

/-- On the left of the reciprocal cusp, the actual benchmark agrees with
the analytic split extension having index `m-1`, including the cusp. -/
theorem benchmark_split_cusp_left_eventually (m : ℕ) (hm : 3 ≤ m) :
    benchmark =ᶠ[nhdsWithin ((1 - 1 / (m : ℝ) ^ 2) / 2)
      (Iic ((1 - 1 / (m : ℝ) ^ 2) / 2))] splitDensityExtension (m - 1) := by
  let d : ℝ := (1 - 1 / (m : ℝ) ^ 2) / 2
  have hr : Real.sqrt (1 - 2 * d) = 1 / (m : ℝ) := split_cusp_sqrt m (by omega)
  have hmleft : (0 : ℝ) < (m - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hmorder : ((m - 1 : ℕ) : ℝ) < m := by exact_mod_cast (show m - 1 < m by omega)
  have hupper : Real.sqrt (1 - 2 * d) < 1 / ((m - 1 : ℕ) : ℝ) := by
    rw [hr]
    exact one_div_lt_one_div_of_lt hmleft hmorder
  have hc : ContinuousAt (fun x : ℝ => Real.sqrt (1 - 2 * x)) d := by fun_prop
  have hnear := hc.eventually (isOpen_Iio.mem_nhds hupper)
  have hband := benchmark_split_eventually (split_cusp_mem_band m hm)
  filter_upwards [hband.filter_mono nhdsWithin_le_nhds,
    hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hxB hxupper hxside
  have hxle : x ≤ d := hxside
  have hxlower : 1 / (m : ℝ) ≤ Real.sqrt (1 - 2 * x) := by
    rw [← hr]
    exact Real.sqrt_le_sqrt (by linarith)
  have hcast2 : ((m - 2 : ℕ) : ℝ) + 2 = m := by exact_mod_cast (show m - 2 + 2 = m by omega)
  have hcast1 : ((m - 2 : ℕ) : ℝ) + 1 = ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show m - 2 + 1 = m - 1 by omega)
  have hcell : Real.sqrt (1 - 2 * x) ∈
      Icc (1 / (((m - 2 : ℕ) : ℝ) + 2)) (1 / (((m - 2 : ℕ) : ℝ) + 1)) := by
    rw [hcast2, hcast1]
    exact ⟨hxlower, hxupper.le⟩
  rw [hxB]
  simpa only [show m - 2 + 1 = m - 1 by omega, splitDensityExtension] using
    splitValue_on_cell (m - 2) hcell

/-- On the right of the reciprocal cusp, the actual benchmark agrees with
the analytic split extension having index `m`, including the cusp. -/
theorem benchmark_split_cusp_right_eventually (m : ℕ) (hm : 3 ≤ m) :
    benchmark =ᶠ[nhdsWithin ((1 - 1 / (m : ℝ) ^ 2) / 2)
      (Ici ((1 - 1 / (m : ℝ) ^ 2) / 2))] splitDensityExtension m := by
  let d : ℝ := (1 - 1 / (m : ℝ) ^ 2) / 2
  have hr : Real.sqrt (1 - 2 * d) = 1 / (m : ℝ) := split_cusp_sqrt m (by omega)
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hlower : 1 / ((m : ℝ) + 1) < Real.sqrt (1 - 2 * d) := by
    rw [hr]
    exact one_div_lt_one_div_of_lt hm0 (by linarith)
  have hc : ContinuousAt (fun x : ℝ => Real.sqrt (1 - 2 * x)) d := by fun_prop
  have hnear := hc.eventually (isOpen_Ioi.mem_nhds hlower)
  have hband := benchmark_split_eventually (split_cusp_mem_band m hm)
  filter_upwards [hband.filter_mono nhdsWithin_le_nhds,
    hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hxB hxlower hxside
  have hxle : d ≤ x := hxside
  have hxupper : Real.sqrt (1 - 2 * x) ≤ 1 / (m : ℝ) := by
    rw [← hr]
    exact Real.sqrt_le_sqrt (by linarith)
  have hcast1 : ((m - 1 : ℕ) : ℝ) + 1 = m := by exact_mod_cast (show m - 1 + 1 = m by omega)
  have hcast2 : ((m - 1 : ℕ) : ℝ) + 2 = (m : ℝ) + 1 := by
    exact_mod_cast (show m - 1 + 2 = m + 1 by omega)
  have hcell : Real.sqrt (1 - 2 * x) ∈
      Icc (1 / (((m - 1 : ℕ) : ℝ) + 2)) (1 / (((m - 1 : ℕ) : ℝ) + 1)) := by
    rw [hcast2, hcast1]
    exact ⟨hxlower.le, hxupper⟩
  rw [hxB]
  simpa only [show m - 1 + 1 = m by omega, splitDensityExtension] using
    splitValue_on_cell (m - 1) hcell

/-- The ordinary derivative of the left analytic extension at the cusp
is the negative upper own-slope endpoint. -/
theorem split_cusp_left_hasDerivAt (m : ℕ) (hm : 3 ≤ m) :
    HasDerivAt (splitDensityExtension (m - 1)) (-(2 - 2 / (m : ℝ)))
      ((1 - 1 / (m : ℝ) ^ 2) / 2) := by
  have h := splitPolynomial_density_hasDerivAt (m - 1) (by omega)
    (split_cusp_mem_band m hm).2
  rw [split_cusp_sqrt m (by omega)] at h
  change HasDerivAt (fun x : ℝ => splitPolynomial (m - 1) (Real.sqrt (1 - 2 * x))) _ _
  convert h using 1
  have hs := split_cusp_left_own_slope m (by omega)
  linarith

/-- The ordinary derivative of the right analytic extension at the cusp
is the negative lower own-slope endpoint. -/
theorem split_cusp_right_hasDerivAt (m : ℕ) (hm : 3 ≤ m) :
    HasDerivAt (splitDensityExtension m)
      (-(2 - 2 / (m : ℝ) - 2 / ((m : ℝ) + 1)))
      ((1 - 1 / (m : ℝ) ^ 2) / 2) := by
  have h := splitPolynomial_density_hasDerivAt m (by omega)
    (split_cusp_mem_band m hm).2
  rw [split_cusp_sqrt m (by omega)] at h
  change HasDerivAt (fun x : ℝ => splitPolynomial m (Real.sqrt (1 - 2 * x))) _ _
  convert h using 1
  have hs := split_cusp_right_own_slope m (by omega)
  linarith

end Erdos1017.Benchmark
