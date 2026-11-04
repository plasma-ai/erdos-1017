module

public import Erdos1017.Benchmark.BenchmarkHeadCountGuards

/-!
# One-sided slopes of the benchmark at the corner

The crossing of the two families lies in the strict rational crossing box inside
their stationary overlap, and at the corner the left density derivative of the
benchmark is the `E₂` slope while the right derivative is the `W` slope.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Erdos1017.Benchmark

/-- The literal equality of the two actual families lies in the strict
rational crossing box and in the interior of their stationary overlap. -/
theorem crossing_contact_location {e : ℝ} (he : e ∈ Icc epsilonC epsilonD)
    (heq : twoHeadCurve e = mixedCurve e) :
    e ∈ Ioo (23243416 / (2 * 10 ^ 8)) (23243417 / (2 * 10 ^ 8)) ∧
      e ∈ Ioo epsilonC epsilonD := by
  obtain ⟨e₀, hbox, _, huniq⟩ := exists_unique_crossing_on_overlap
  have hident := huniq e he heq
  rw [hident]
  refine ⟨hbox, ?_⟩
  constructor
  · linarith [epsilonC_lt_nine_eightieths, hbox.1]
  · linarith [eighth_lt_epsilonD, hbox.2]

private theorem benchmark_eq_max {d : ℝ} (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    benchmark d = max (mixedCurve (1 / 2 - d)) (twoHeadCurve (1 / 2 - d)) := by
  simp only [Erdos1017.benchmark, not_le.mpr hd.1, ite_false, hd.2, ite_true]

private theorem half_sub_hasDerivAt {f : ℝ → ℝ} {a d : ℝ}
    (h : HasDerivAt f a (1 / 2 - d)) : HasDerivAt (fun x => f (1 / 2 - x)) (-a) d := by
  convert h.comp d ((hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)) using 1
  · rfl
  · ring

/-- At the actual corner the left density derivative is the E2 slope;
the right derivative is the W slope. Both are derived from the same
family crossing, rather than supplied as a multiplier identification. -/
theorem benchmark_corner_one_sided_derivatives {d : ℝ}
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (he : 1 / 2 - d ∈ Icc epsilonC epsilonD)
    (heq : twoHeadCurve (1 / 2 - d) = mixedCurve (1 / 2 - d)) :
    HasDerivWithinAt benchmark
      (-((4 - 3 * twoHeadInverse (1 / 2 - d)) / (3 * twoHeadInverse (1 / 2 - d)))) (Iic d) d ∧
    HasDerivWithinAt benchmark
      (-((mixedInverse (1 / 2 - d) + 1) / (3 * mixedInverse (1 / 2 - d)))) (Ici d) d := by
  have hloc := (crossing_contact_location he heq).2
  have hstar : epsilonStar < 1 / 2 - d := by
    linarith [hloc.1, epsilonStar_lt_tenth, tenth_lt_epsilonC]
  have hquarter : 1 / 2 - d < (1 / 4 : ℝ) := by linarith [hd.1]
  have hnear : ∀ᶠ x in nhds d, 1 / 2 - x ∈ Ioo epsilonC epsilonD :=
    (show ContinuousAt (fun x : ℝ => 1 / 2 - x) d by fun_prop).eventually
      (isOpen_Ioo.mem_nhds hloc)
  have hdom : ∀ᶠ x in nhds d, x ∈ Ioo (1 / 4 : ℝ) (1 / 2) := Ioo_mem_nhds hd.1 hd.2
  constructor
  · have hder := (half_sub_hasDerivAt (twoHeadCurve_hasDerivAt ⟨hloc.1, hquarter⟩)).hasDerivWithinAt
      (s := Iic d)
    apply hder.congr_of_eventuallyEq _ (by rw [benchmark_eq_max hd, heq, max_self])
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxd hleft
    have hxdle : x ≤ d := hleft
    have hm := family_difference_strictMonoOn.monotoneOn he
      ⟨hx.1.le, hx.2.le⟩ (by linarith)
    have hact : mixedCurve (1 / 2 - x) ≤ twoHeadCurve (1 / 2 - x) := by
      rw [heq] at hm
      linarith
    rw [benchmark_eq_max hxd, max_eq_right hact]
  · have hder := (half_sub_hasDerivAt (mixedCurve_hasDerivAt ⟨hstar, hloc.2⟩)).hasDerivWithinAt
      (s := Ici d)
    apply hder.congr_of_eventuallyEq _ (by rw [benchmark_eq_max hd, heq, max_self])
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxd hright
    have hdle : d ≤ x := hright
    have hm := family_difference_strictMonoOn.monotoneOn
      ⟨hx.1.le, hx.2.le⟩ he (by linarith)
    have hact : twoHeadCurve (1 / 2 - x) ≤ mixedCurve (1 / 2 - x) := by
      rw [heq] at hm
      linarith
    rw [benchmark_eq_max hxd, max_eq_left hact]

end Erdos1017.Benchmark
