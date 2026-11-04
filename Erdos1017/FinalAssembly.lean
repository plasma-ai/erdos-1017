module

public import Erdos1017.FullBenchmarkUpper
public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateRoot

/-!
# Assembly of Erdős Problem 1017: clique partitions of graphs of given size

`FullBenchmarkUpper` derives the fractional upper bound and the uniform
asymptotic formula from the contact exclusions and the integer transfer,
assuming that the fixed-point cover of the large-atom middle-E2 parameter box
closes. The kernel-checked certificate `cover_root` discharges that premise.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017

/-- The checked finite cover closes the global fractional benchmark
upper bound at every density in the full feasible interval. -/
theorem densityLimit_le_benchmark (d : ℝ) (hd : d ∈ Icc (0 : ℝ) (1 / 2)) :
    FractionalGraph.densityLimit d ≤ benchmark d :=
  densityLimit_le_benchmark_of_cover MiddleE2LargeUniversal.FixedPoint.cover_root d hd

/-- The checked global upper bound and the same-graph integer transfer
give the uniform asymptotic theorem. -/
theorem uniform_asymptotic_proved : UniformAsymptotic :=
  uniformAsymptotic_of_cover MiddleE2LargeUniversal.FixedPoint.cover_root

end Erdos1017
