module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The explicit benchmark

The benchmark `B` of the uniform asymptotic formula. Root and inverse
parameters are specified by infima of their exact algebraic solution sets.
Root existence and uniqueness are proved below.
Inverse correctness and branch matching are proved in `BenchmarkProperties`,
and full continuity is proved in `BenchmarkContinuity`; none is an assumption
of these definitions. `Challenge.lean` repeats every definition in this file;
Comparator requires them to agree exactly.
-/

@[expose] public section

namespace Erdos1017
namespace Benchmark

/-- The index `j = max 1 ⌈(1 - r) / r⌉₊` of the split value at `r`. -/
noncomputable def splitIndex (r : ℝ) : ℕ := max 1 ⌈(1 - r) / r⌉₊

/-- The split value `H(r) = (2(j + 1)r - (2j + 1)r² - 1) / (j(j + 1))`, with
`j = splitIndex r`, and `H(0) = 0`. -/
noncomputable def splitValue (r : ℝ) : ℝ :=
  if r = 0 then 0 else
    let j : ℝ := splitIndex r
    (-(2 * j + 1) * r ^ 2 + 2 * (j + 1) * r - 1) / (j * (j + 1))

/-- The upper end `(3 + √21)/6` of the interval of mixed parameters. -/
noncomputable def sigmaZero : ℝ := (3 + Real.sqrt 21) / 6

/-- The missing-edge density `(51 - 9√21)/100` up to which `W` is the split value. -/
noncomputable def epsilonStar : ℝ := (51 - 9 * Real.sqrt 21) / 100

/-- The denominator `s² + 8s + 2` of the mixed family's density and value. -/
def mixedDenominator (s : ℝ) : ℝ := s ^ 2 + 8 * s + 2

/-- The missing-edge density of the mixed family at the parameter `s`. -/
noncomputable def mixedDensity (s : ℝ) : ℝ :=
  (2 + 16 * s + 33 * s ^ 2 - 15 * s ^ 4) / (2 * mixedDenominator s ^ 2)

/-- The dual-certificate value of the mixed family at the parameter `s`. -/
noncomputable def mixedValue (s : ℝ) : ℝ :=
  (6 + 46 * s + 85 * s ^ 2 - 16 * s ^ 3 - 16 * s ^ 4) /
    (6 * mixedDenominator s ^ 2)

/-- The cubic `29s³ - 16s² - 14s - 2`, whose root in `[1, 11/10]` is `σ_d`. -/
def mixedRootPolynomial (s : ℝ) : ℝ := 29 * s ^ 3 - 16 * s ^ 2 - 14 * s - 2

/-- The root `σ_d` of `mixedRootPolynomial` in `[1, 11/10]`, as the infimum of the roots there. -/
noncomputable def sigmaD : ℝ :=
  sInf {s : ℝ | s ∈ Set.Icc 1 (11 / 10) ∧ mixedRootPolynomial s = 0}

/-- The missing-edge density of the mixed family at `σ_d`, beyond which `W(e) = e`. -/
noncomputable def epsilonD : ℝ := mixedDensity sigmaD

/-- For `e ∈ [epsilonStar, epsilonD]`, the mixed parameter in `[σ_d, (3 + √21)/6]`
with missing-edge density `e`, as the infimum of the solutions. -/
noncomputable def mixedInverse (e : ℝ) : ℝ :=
  sInf {s : ℝ | s ∈ Set.Icc sigmaD sigmaZero ∧ mixedDensity s = e}

/-- The curve `W`: the split value `H(√(2e))` up to `epsilonStar`, the mixed
family's value up to `epsilonD`, and `e` beyond. -/
noncomputable def mixedCurve (e : ℝ) : ℝ :=
  if e ≤ epsilonStar then splitValue (Real.sqrt (2 * e))
  else if e ≤ epsilonD then mixedValue (mixedInverse e)
  else e

/-- The denominator `z² + z - 1` of the two-head family's density and value. -/
def twoHeadDenominator (z : ℝ) : ℝ := z ^ 2 + z - 1

/-- The missing-edge density of the two-head family at the parameter `z`. -/
noncomputable def twoHeadDensity (z : ℝ) : ℝ :=
  z ^ 2 * (13 * z ^ 2 - 16 * z + 5) / (16 * twoHeadDenominator z ^ 2)

/-- The dual-certificate value of the two-head family at the parameter `z`. -/
noncomputable def twoHeadValue (z : ℝ) : ℝ :=
  twoHeadDensity z + (3 * z - 2) ^ 2 * (1 - z) * (3 * z - 1) /
    (24 * twoHeadDenominator z ^ 2)

/-- The quartic `-95z⁴ + 18z³ + 193z² - 168z + 40`, whose root in `[3/4, 4/5]` is `z_c`. -/
def twoHeadRootPolynomial (z : ℝ) : ℝ :=
  -95 * z ^ 4 + 18 * z ^ 3 + 193 * z ^ 2 - 168 * z + 40

/-- The root `z_c` of `twoHeadRootPolynomial` in `[3/4, 4/5]`, as the infimum of the roots there. -/
noncomputable def zC : ℝ :=
  sInf {z : ℝ | z ∈ Set.Icc (3 / 4) (4 / 5) ∧ twoHeadRootPolynomial z = 0}

/-- The missing-edge density `e_c` of the two-head family at `z_c`. -/
noncomputable def epsilonC : ℝ := twoHeadDensity zC

/-- For `e ∈ [epsilonC, 1/4]`, the two-head parameter in `[2/3, z_c]` with
missing-edge density `e`, as the infimum of the solutions. -/
noncomputable def twoHeadInverse (e : ℝ) : ℝ :=
  sInf {z : ℝ | z ∈ Set.Icc (2 / 3) zC ∧ twoHeadDensity z = e}

/-- The curve `E₂`: zero at `e = 0`, the split value `H(√(2e))` up to `e_c`, and
the two-head family's value beyond. -/
noncomputable def twoHeadCurve (e : ℝ) : ℝ :=
  if e = 0 then 0
  else if e ≤ epsilonC then splitValue (Real.sqrt (2 * e))
  else twoHeadValue (twoHeadInverse e)

/-- The mixed cutoff polynomial has a root in its defining interval. -/
theorem mixedRoot_exists :
    ∃ s ∈ Set.Icc (1 : ℝ) (11 / 10), mixedRootPolynomial s = 0 := by
  have hc : Continuous mixedRootPolynomial := by unfold mixedRootPolynomial; fun_prop
  exact intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 11 / 10) hc.continuousOn
    (by norm_num [mixedRootPolynomial] : (0 : ℝ) ∈
      Set.Icc (mixedRootPolynomial 1) (mixedRootPolynomial (11 / 10)))

/-- The two-head cutoff polynomial has a root in its defining interval. -/
theorem twoHeadRoot_exists :
    ∃ z ∈ Set.Icc (3 / 4 : ℝ) (4 / 5), twoHeadRootPolynomial z = 0 := by
  have hc : Continuous twoHeadRootPolynomial := by unfold twoHeadRootPolynomial; fun_prop
  exact intermediate_value_Icc' (by norm_num : (3 / 4 : ℝ) ≤ 4 / 5) hc.continuousOn
    (by norm_num [twoHeadRootPolynomial] : (0 : ℝ) ∈
      Set.Icc (twoHeadRootPolynomial (4 / 5)) (twoHeadRootPolynomial (3 / 4)))

/-- Strict increase makes the mixed cutoff root unique. -/
theorem mixedRootPolynomial_strictMonoOn :
    StrictMonoOn mixedRootPolynomial (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have h2 : (x - 1) ^ 2 ≤ (y - 1) ^ 2 := by gcongr
  have h3 : (x - 1) ^ 3 ≤ (y - 1) ^ 3 := by gcongr
  have heq (s : ℝ) : mixedRootPolynomial s =
      29 * (s - 1) ^ 3 + 71 * (s - 1) ^ 2 + 41 * (s - 1) - 3 := by
    unfold mixedRootPolynomial
    ring
  rw [heq x, heq y]
  linarith

/-- Strict decrease makes the two-head cutoff root unique. -/
theorem twoHeadRootPolynomial_strictAntiOn :
    StrictAntiOn twoHeadRootPolynomial (Set.Ici (3 / 4)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x - 3 / 4 := sub_nonneg.mpr hx
  have h2 : (x - 3 / 4) ^ 2 ≤ (y - 3 / 4) ^ 2 := by gcongr
  have h3 : (x - 3 / 4) ^ 3 ≤ (y - 3 / 4) ^ 3 := by gcongr
  have h4 : (x - 3 / 4) ^ 4 ≤ (y - 3 / 4) ^ 4 := by gcongr
  have heq (z : ℝ) : twoHeadRootPolynomial z =
      25 / 256 - 135 / 16 * (z - 3 / 4) - 697 / 8 * (z - 3 / 4) ^ 2 -
        267 * (z - 3 / 4) ^ 3 - 95 * (z - 3 / 4) ^ 4 := by
    unfold twoHeadRootPolynomial
    ring
  rw [heq x, heq y]
  linarith

/-- The infimum defining the mixed cutoff is itself a root in the interval. -/
theorem sigmaD_spec : sigmaD ∈ Set.Icc (1 : ℝ) (11 / 10) ∧ mixedRootPolynomial sigmaD = 0 := by
  have hc : Continuous mixedRootPolynomial := by unfold mixedRootPolynomial; fun_prop
  apply (isClosed_Icc.inter (isClosed_eq hc continuous_const)).csInf_mem
  · exact mixedRoot_exists
  · exact ⟨1, fun s hs => hs.1.1⟩

/-- The infimum defining the two-head cutoff is itself a root in the interval. -/
theorem zC_spec : zC ∈ Set.Icc (3 / 4 : ℝ) (4 / 5) ∧ twoHeadRootPolynomial zC = 0 := by
  have hc : Continuous twoHeadRootPolynomial := by unfold twoHeadRootPolynomial; fun_prop
  apply (isClosed_Icc.inter (isClosed_eq hc continuous_const)).csInf_mem
  · exact twoHeadRoot_exists
  · exact ⟨3 / 4, fun z hz => hz.1.1⟩

/-- Uniqueness of the mixed cutoff root: any root `s` of `mixedRootPolynomial`
in `[1, 11/10]` equals `σ_D`. -/
theorem mixedRoot_unique {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (11 / 10))
    (hroot : mixedRootPolynomial s = 0) : s = sigmaD := by
  apply mixedRootPolynomial_strictMonoOn.injOn hs.1 sigmaD_spec.1.1
  exact hroot.trans sigmaD_spec.2.symm

/-- Uniqueness of the two-head cutoff root: any root `z` of
`twoHeadRootPolynomial` in `[3/4, 4/5]` equals `z_C`. -/
theorem twoHeadRoot_unique {z : ℝ} (hz : z ∈ Set.Icc (3 / 4 : ℝ) (4 / 5))
    (hroot : twoHeadRootPolynomial z = 0) : z = zC := by
  apply twoHeadRootPolynomial_strictAntiOn.injOn hz.1 zC_spec.1.1
  exact hroot.trans zC_spec.2.symm

end Benchmark

/-- The benchmark `B`: `d` up to density `1/4`, the larger of `W` and `E₂` at
`1/2 - d` below density `1/2`, and zero from `1/2` on. -/
noncomputable def benchmark (d : ℝ) : ℝ :=
  if d ≤ 1 / 4 then d
  else if d < 1 / 2 then
    max (Benchmark.mixedCurve (1 / 2 - d)) (Benchmark.twoHeadCurve (1 / 2 - d))
  else 0

/-- The benchmark is the identity up to density one quarter: `B(d) = d` whenever `d ≤ 1/4`. -/
theorem benchmark_of_le_quarter {d : ℝ} (h : d ≤ 1 / 4) : benchmark d = d := by
  exact ite_eq_left h

/-- The benchmark vanishes at density zero: `B(0) = 0`. -/
@[simp] theorem benchmark_zero : benchmark 0 = 0 := by
  apply benchmark_of_le_quarter
  positivity

/-- The benchmark vanishes at density one half: `B(1/2) = 0`. -/
@[simp] theorem benchmark_half : benchmark (1 / 2) = 0 := by
  norm_num [benchmark]

end Erdos1017
