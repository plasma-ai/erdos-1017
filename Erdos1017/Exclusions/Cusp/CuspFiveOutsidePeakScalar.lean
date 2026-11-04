module

public import Erdos1017.Exclusions.Cusp.BenchmarkSplitCubicEnvelopes

/-!
# Scalar exit for the fifth-cusp outside peak

At the fifth cusp the reverse split gap lies below the tenth missing-density
threshold, and the nineteen-twentieths split envelope with the reverse square
cap and forward cubic gives the contradiction (`outside_contradiction`).
-/

@[expose] public section

namespace Erdos1017.CuspFiveOutsidePeakScalar

/-- The actual reverse split gap at the fifth cusp lies below the tenth
missing-density threshold. Both possible higher split cells are excluded. -/
theorem missing_lt_tenth {ell r : ℝ} (hell : 19 / 15 < ell)
    (hr : 1 / 5 < r) (hrange : r ^ 2 < 5 / 32)
    (hgap : 0 < Benchmark.splitValue r - 4 / 125 - ell * (r ^ 2 - 1 / 25) / 2) :
    r ^ 2 < 1 / 10 := by
  have hbase : 0 < Benchmark.splitValue r - 4 / 125 -
      (19 / 15) * (r ^ 2 - 1 / 25) / 2 := by
    have hp := mul_pos (sub_pos.mpr hell) (show 0 < r ^ 2 - 1 / 25 by nlinarith)
    nlinarith only [hgap, hp]
  have hthird : r < 1 / 3 := by
    by_contra hn
    have hcell : r ∈ Set.Icc (1 / (((1 : ℕ) : ℝ) + 2)) (1 / (((1 : ℕ) : ℝ) + 1)) :=
      ⟨by linarith, by nlinarith⟩
    rw [Benchmark.splitValue_on_cell 1 hcell] at hbase
    norm_num [Benchmark.splitPolynomial] at hbase
    nlinarith [sq_nonneg (44 * r - 15)]
  by_contra hn
  have hsq : 1 / 10 ≤ r ^ 2 := le_of_not_gt hn
  have hcell : r ∈ Set.Icc (1 / (((2 : ℕ) : ℝ) + 2)) (1 / (((2 : ℕ) : ℝ) + 1)) :=
    ⟨by nlinarith, by linarith⟩
  rw [Benchmark.splitValue_on_cell 2 hcell] at hbase
  norm_num [Benchmark.splitPolynomial] at hbase
  have hlower : 127 / 400 < r := by nlinarith only [hbase, hsq]
  nlinarith [sq_nonneg (r - 19 / 60)]

/-- The existing nineteen-twentieths split envelope already pays the fifth
outside-peak exit. The reverse square cap and the forward cubic force
incompatible bounds on the same original normalized peak. -/
theorem outside_contradiction {delta R : ℝ} (_hdelta : 0 < delta)
    (hdeltaCap : delta ≤ 1 / 3) (hR : 0 < R)
    (hsq : R ^ 2 < (5 / 2) * delta)
    (hforward : delta < (2 / 5 + delta) * R ^ 2 - (19 / 50) * R ^ 3) : False := by
  have hR2 : R ^ 2 < 5 / 6 := by nlinarith only [hsq, hdeltaCap]
  have hRcap : R < 19 / 20 := by nlinarith only [hR2, hR]
  have hscaled := mul_lt_mul_of_pos_right
    (show (2 / 5) * R ^ 2 < delta by nlinarith only [hsq])
    (show 0 < 1 - R ^ 2 by linarith only [hR2])
  have hsign := mul_nonneg (show 0 ≤ 19 / 20 - R by linarith only [hRcap])
    (pow_nonneg hR.le 3)
  nlinarith only [hforward, hscaled, hsign]

end Erdos1017.CuspFiveOutsidePeakScalar
