module

public import Erdos1017.Benchmark.BenchmarkContactGeometry
public import Erdos1017.Benchmark.BenchmarkFamilyGuards
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Curvature of the benchmark on strict split cells

Inside the open split-active band both benchmark branches agree with the split
curve near every point, so on a strict split cell the benchmark is `C²` with
explicit first and second derivatives, and the second derivative is strictly
negative (`benchmark_second_deriv_neg_split_cell`).
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Erdos1017.Benchmark

/-- Both literal benchmark branches agree with the split curve throughout
an open neighborhood of every point in the actual split-active band. -/
theorem benchmark_split_eventually {d : ℝ}
    (hband : d ∈ Ioo (1 / 2 - epsilonStar) (1 / 2)) :
    benchmark =ᶠ[nhds d] (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x))) := by
  have hnear : ∀ᶠ x in nhds d, x ∈ Ioo (1 / 2 - epsilonStar) (1 / 2) :=
    Ioo_mem_nhds hband.1 hband.2
  filter_upwards [hnear] with x hx
  have hxq : ¬x ≤ 1 / 4 := by linarith [hx.1, epsilonStar_lt_tenth]
  have hxS : 1 / 2 - x ≤ epsilonStar := by linarith [hx.1]
  have hxC : 1 / 2 - x ≤ epsilonC :=
    hxS.trans (epsilonStar_lt_tenth.trans tenth_lt_epsilonC).le
  have hx0 : 1 / 2 - x ≠ 0 := by linarith [hx.2]
  simp only [benchmark, hxq, ite_false, hx.2, ite_true, mixedCurve, hxS,
    twoHeadCurve, hx0, hxC, max_self]
  congr 2
  ring

private theorem split_cell_eventually (n : ℕ) {d : ℝ}
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    (fun x : ℝ => splitValue (Real.sqrt (1 - 2 * x))) =ᶠ[nhds d]
      (fun x : ℝ => splitPolynomial (n + 1) (Real.sqrt (1 - 2 * x))) := by
  have hc : ContinuousAt (fun x : ℝ => Real.sqrt (1 - 2 * x)) d := by fun_prop
  have hnear := hc.eventually (isOpen_Ioo.mem_nhds hcell)
  filter_upwards [hnear] with x hx
  exact splitValue_on_cell n ⟨hx.1.le, hx.2.le⟩

private theorem splitPolynomial_density_contDiffAt (j : ℕ) {d : ℝ}
    (hd : d < 1 / 2) :
    ContDiffAt ℝ 2 (fun x : ℝ => splitPolynomial j (Real.sqrt (1 - 2 * x))) d := by
  have hinner : ContDiffAt ℝ 2 (fun x : ℝ => 1 - 2 * x) d := by fun_prop
  have hs := hinner.sqrt (show 1 - 2 * d ≠ 0 by linarith)
  unfold splitPolynomial
  exact (((contDiffAt_const.mul (hs.pow 2)).add
    (contDiffAt_const.mul hs)).sub contDiffAt_const).div_const _

/-- The actual benchmark is C² at every strict split-cell point inside
the actual open split-active band. The cell formula is derived. -/
theorem benchmark_contDiffAt_split_cell (n : ℕ) {d : ℝ}
    (hband : d ∈ Ioo (1 / 2 - epsilonStar) (1 / 2))
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    ContDiffAt ℝ 2 benchmark d := by
  exact (splitPolynomial_density_contDiffAt (n + 1) hband.2).congr_of_eventuallyEq
    ((benchmark_split_eventually hband).trans (split_cell_eventually n hcell))

/-- Exact first derivative of the actual benchmark on a strict split cell. -/
theorem benchmark_hasDerivAt_split_cell (n : ℕ) {d : ℝ}
    (hband : d ∈ Ioo (1 / 2 - epsilonStar) (1 / 2))
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    HasDerivAt benchmark
      (2 * (2 * ((n + 1 : ℕ) : ℝ) + 1) /
        (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) -
          2 / (((n + 1 : ℕ) : ℝ) * Real.sqrt (1 - 2 * d))) d := by
  exact (splitValue_density_hasDerivAt n hcell).congr_of_eventuallyEq
    (benchmark_split_eventually hband)

/-- Exact second derivative of the actual benchmark on a strict split cell. -/
theorem benchmark_second_deriv_split_cell (n : ℕ) {d : ℝ}
    (hband : d ∈ Ioo (1 / 2 - epsilonStar) (1 / 2))
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    deriv (deriv benchmark) d =
      -2 / (((n + 1 : ℕ) : ℝ) * Real.sqrt (1 - 2 * d) ^ 3) := by
  rw [((benchmark_split_eventually hband).deriv).deriv_eq]
  exact (splitValue_density_deriv_hasDerivAt n hcell).deriv

/-- Strict negativity belongs to the actual benchmark, with both the
active band and the strict split-cell guards retained. -/
theorem benchmark_second_deriv_neg_split_cell (n : ℕ) {d : ℝ}
    (hband : d ∈ Ioo (1 / 2 - epsilonStar) (1 / 2))
    (hcell : Real.sqrt (1 - 2 * d) ∈
      Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    deriv (deriv benchmark) d < 0 := by
  rw [benchmark_second_deriv_split_cell n hband hcell]
  exact splitPolynomial_density_curvature_neg (n + 1) (by omega) hband.2

end Erdos1017.Benchmark
