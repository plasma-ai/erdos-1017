module

public import Erdos1017.Benchmark.BenchmarkE2Activity
public import Erdos1017.Benchmark.BenchmarkHeadCountGuards
public import Erdos1017.Exclusions.Common.E2.E2PrivateCurvatureCertificates
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Curvature of the benchmark at `E₂` contact

This module defines the contact density `e2ContactDensity` and its inverse
parameter `e2ContactParameter`; the inverse identity holds on `(0, 1/4)`, the
inverse is `C²` at every `q ∈ (0, 1/5]`, and the benchmark is `C²` at each such
contact density with second derivative given by the `E₂` curvature formula.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Erdos1017.Benchmark

open LowerE2Scalar

/-- The actual graph density corresponding to the stationary E2 parameter. -/
def e2ContactDensity (q : ℝ) : ℝ := (1 - missingMass q) / 2

/-- The actual inverse q coordinate, using the existing algebraic inverse. -/
def e2ContactParameter (d : ℝ) : ℝ := 3 * twoHeadInverse (1 / 2 - d) - 2

private theorem contDiffAt_inverse_of_left_inverse {f g : ℝ → ℝ} {a r : ℝ}
    (hf : ContDiffAt ℝ 2 f a) (hf1 : HasDerivAt f r a) (hr : r ≠ 0)
    (hleft : ∀ᶠ x in nhds a, g (f x) = x) : ContDiffAt ℝ 2 g (f a) := by
  have hstrict := hf.hasStrictFDerivAt' (hf1.hasFDerivAt_equiv hr) (by norm_num)
  have heq := hstrict.localInverse_unique hleft
  have hc := hf.to_localInverse (hf1.hasFDerivAt_equiv hr) (by norm_num)
  exact hc.congr_of_eventuallyEq heq

/-- Every legal positive E2 parameter gives an interior graph density. -/
theorem e2_density_mem {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    e2ContactDensity q ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
  have he := e2_q_density_mem hq
  constructor <;> dsimp only [e2ContactDensity] <;>
    linarith [he.1, he.2, tenth_lt_epsilonC]

/-- The parameter inverse is correct on an open interval containing every
legal q, including one fifth. No branch comparison is needed for inversion. -/
theorem e2ContactParameter_e2ContactDensity {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) (1 / 4)) : e2ContactParameter (e2ContactDensity q) = q := by
  have he : 1 / 2 - e2ContactDensity q = missingMass q / 2 := by
    unfold e2ContactDensity
    ring
  unfold e2ContactParameter
  rw [he, twoHeadInverse_e2_q_of_lt_quarter hq]
  ring

private theorem e2ContactDensity_hasDerivAt {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt e2ContactDensity (-deriv missingMass q / 2) q := by
  have hh := (E2PrivateCurvature.missingMass_hasDerivAt hq).differentiableAt.hasDerivAt
  convert ((hasDerivAt_const q (1 : ℝ)).sub hh).div_const 2 using 1
  · rfl
  · ring

private theorem e2ContactDensity_deriv_pos {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    0 < deriv e2ContactDensity q := by
  rw [(e2ContactDensity_hasDerivAt hq.1.le).deriv,
    (E2PrivateCurvature.missingMass_hasDerivAt hq.1.le).deriv]
  have hR := denominator_pos hq.1.le
  have hF := E2PrivateCurvature.derivativeFactor_pos ⟨hq.1.le, hq.2⟩
  have hq2 : 0 < q + 2 := by linarith [hq.1]
  have hneg : -9 * (q + 2) * E2PrivateCurvature.derivativeFactor q /
      (4 * denominator q ^ 3) < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith
    · positivity
  linarith

private theorem e2ContactDensity_contDiffAt {q : ℝ} (hq : 0 ≤ q) :
    ContDiffAt ℝ 2 e2ContactDensity q := by
  have hR := ne_of_gt (denominator_pos hq)
  have hh : ContDiffAt ℝ 2 missingMass q := by
    unfold missingMass
    apply ContDiffAt.div
    · fun_prop
    · unfold denominator
      fun_prop
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hR)
  exact (contDiffAt_const.sub hh).div_const 2

/-- The actual existing q inverse is C², derived from the rational density
map and its proved inverse identity through the inverse function theorem. -/
theorem e2ContactParameter_contDiffAt {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    ContDiffAt ℝ 2 e2ContactParameter (e2ContactDensity q) := by
  have hf := e2ContactDensity_contDiffAt hq.1.le
  have hf1 := (e2ContactDensity_hasDerivAt hq.1.le).differentiableAt.hasDerivAt
  have hne := ne_of_gt (e2ContactDensity_deriv_pos hq)
  apply contDiffAt_inverse_of_left_inverse hf hf1 hne
  filter_upwards [Ioo_mem_nhds hq.1 (by linarith [hq.2] : q < 1 / 4)] with x hx
  exact e2ContactParameter_e2ContactDensity hx

/-- The derivative of the actual inverse follows from the local inverse
identity and the nonzero derivative of the same original density map. -/
theorem e2ContactParameter_hasDerivAt {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    HasDerivAt e2ContactParameter (deriv e2ContactDensity q)⁻¹ (e2ContactDensity q) := by
  have hg := (e2ContactParameter_contDiffAt hq).differentiableAt (by norm_num)
  have hf := (e2ContactDensity_hasDerivAt hq.1.le).differentiableAt.hasDerivAt
  have hcomp := hg.hasDerivAt.comp q hf
  have hleft : ∀ᶠ x in nhds q, e2ContactParameter (e2ContactDensity x) = x := by
    filter_upwards [Ioo_mem_nhds hq.1 (by linarith [hq.2] : q < 1 / 4)] with x hx
    exact e2ContactParameter_e2ContactDensity hx
  have hleft' : (e2ContactParameter ∘ e2ContactDensity) =ᶠ[nhds q] (fun x : ℝ => x) := hleft
  have hid : HasDerivAt (fun x : ℝ => x)
      (deriv e2ContactParameter (e2ContactDensity q) * deriv e2ContactDensity q) q :=
    hcomp.congr_of_eventuallyEq hleft'.symm
  have hprod := hid.unique (hasDerivAt_id q)
  have hratio : deriv e2ContactParameter (e2ContactDensity q) =
      (deriv e2ContactDensity q)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff (ne_of_gt (e2ContactDensity_deriv_pos hq))).mpr hprod
  simpa only [hratio] using hg.hasDerivAt

/-- C² regularity of the actual two-head inverse at every legal E2 density
is a consequence of the constructed q inverse, rather than an input. -/
theorem twoHeadInverse_contDiffAt_e2_q {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    ContDiffAt ℝ 2 twoHeadInverse (missingMass q / 2) := by
  have harg : 1 / 2 - missingMass q / 2 = e2ContactDensity q := by
    unfold e2ContactDensity
    ring
  have hg : ContDiffAt ℝ 2 e2ContactParameter (1 / 2 - missingMass q / 2) :=
    harg.symm ▸ e2ContactParameter_contDiffAt hq
  have hinner : ContDiffAt ℝ 2 (fun e => e2ContactParameter (1 / 2 - e))
      (missingMass q / 2) := hg.comp (missingMass q / 2) (by fun_prop)
  have hc : ContDiffAt ℝ 2 (fun e => (e2ContactParameter (1 / 2 - e) + 2) / 3)
      (missingMass q / 2) := (hinner.add contDiffAt_const).div_const 3
  convert hc using 1
  funext e
  unfold e2ContactParameter
  have he : 1 / 2 - (1 / 2 - e) = e := by ring
  rw [he]
  ring

private theorem twoHeadValue_contDiffAt {z : ℝ} (hz : 2 / 3 ≤ z) :
    ContDiffAt ℝ 2 twoHeadValue z := by
  have hR := ne_of_gt (twoHeadDenominator_pos hz)
  have hdensity : ContDiffAt ℝ 2 twoHeadDensity z := by
    unfold twoHeadDensity
    apply ContDiffAt.div
    · fun_prop
    · unfold twoHeadDenominator
      fun_prop
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hR)
  change ContDiffAt ℝ 2 (fun w => twoHeadDensity w +
    (3 * w - 2) ^ 2 * (1 - w) * (3 * w - 1) / (24 * twoHeadDenominator w ^ 2)) z
  apply hdensity.add
  apply ContDiffAt.div
  · fun_prop
  · unfold twoHeadDenominator
    fun_prop
  · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hR)

private theorem strict_twoHead_eventually {d : ℝ}
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (he : epsilonC < 1 / 2 - d)
    (hactive : mixedCurve (1 / 2 - d) < twoHeadCurve (1 / 2 - d)) :
    ∀ᶠ x in nhds d, x ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ epsilonC < 1 / 2 - x ∧
      mixedCurve (1 / 2 - x) < twoHeadCurve (1 / 2 - x) := by
  have he0 : 0 < 1 / 2 - d := by linarith [hd.2]
  have hehi : 1 / 2 - d < 1 / 4 := by linarith [hd.1]
  have hm := (mixedCurve_continuousOn (1 / 2 - d) ⟨he0.le, hehi.le⟩).continuousAt
    (Icc_mem_nhds he0 hehi)
  have ht := (twoHeadCurve_continuousOn (1 / 2 - d) ⟨he0.le, hehi.le⟩).continuousAt
    (Icc_mem_nhds he0 hehi)
  have hmc : ContinuousAt (fun x : ℝ => mixedCurve (1 / 2 - x)) d := hm.comp (by fun_prop)
  have htc : ContinuousAt (fun x : ℝ => twoHeadCurve (1 / 2 - x)) d := ht.comp (by fun_prop)
  have hec : ContinuousAt (fun x : ℝ => 1 / 2 - x) d := by fun_prop
  have hnearE : ∀ᶠ x in nhds d, epsilonC < 1 / 2 - x :=
    hec.eventually (eventually_gt_nhds he)
  filter_upwards [Ioo_mem_nhds hd.1 hd.2, hnearE, hmc.eventually_lt htc hactive]
    with x hx hxe hxa
  exact ⟨hx, hxe, hxa⟩

private theorem benchmark_twoHead_eventually {d : ℝ}
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (he : epsilonC < 1 / 2 - d)
    (hactive : mixedCurve (1 / 2 - d) < twoHeadCurve (1 / 2 - d)) :
    benchmark =ᶠ[nhds d] (fun x => twoHeadValue (twoHeadInverse (1 / 2 - x))) := by
  filter_upwards [strict_twoHead_eventually hd he hactive] with x hx
  have he0 : 1 / 2 - x ≠ 0 := by linarith [hx.1.2]
  rw [show benchmark x = max (mixedCurve (1 / 2 - x)) (twoHeadCurve (1 / 2 - x)) by
    simp only [benchmark, not_le.mpr hx.1.1, ite_false, hx.1.2, ite_true],
    max_eq_right hx.2.2.le]
  simp only [twoHeadCurve, he0, ite_false, not_le.mpr hx.2.1]

private theorem benchmark_twoHead_hasDerivAt_of_strict {d : ℝ}
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (he : epsilonC < 1 / 2 - d)
    (hactive : mixedCurve (1 / 2 - d) < twoHeadCurve (1 / 2 - d)) :
    HasDerivAt benchmark
      (-((4 - 3 * twoHeadInverse (1 / 2 - d)) / (3 * twoHeadInverse (1 / 2 - d)))) d := by
  have hs := twoHeadStationary_hasDerivAt ⟨he, by linarith [hd.1]⟩
  have hf : HasDerivAt (fun x => twoHeadValue (twoHeadInverse (1 / 2 - x)))
      (-((4 - 3 * twoHeadInverse (1 / 2 - d)) / (3 * twoHeadInverse (1 / 2 - d)))) d := by
    convert hs.comp d ((hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)) using 1
    · rfl
    · ring
  exact hf.congr_of_eventuallyEq (benchmark_twoHead_eventually hd he hactive)

/-- The actual benchmark is C² at every legal positive E2 contact density.
Both the inverse regularity and strict branch selection are derived. -/
theorem benchmark_contDiffAt_e2_q {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    ContDiffAt ℝ 2 benchmark (e2ContactDensity q) := by
  have he := e2_q_density_mem hq
  have hd := e2_density_mem hq
  have harg : 1 / 2 - e2ContactDensity q = missingMass q / 2 := by
    unfold e2ContactDensity
    ring
  have hInv : ContDiffAt ℝ 2 twoHeadInverse (1 / 2 - e2ContactDensity q) := by
    simpa only [harg] using twoHeadInverse_contDiffAt_e2_q hq
  have hinner : ContDiffAt ℝ 2 (fun x => twoHeadInverse (1 / 2 - x)) (e2ContactDensity q) :=
    hInv.comp (e2ContactDensity q) (by fun_prop)
  have hi := (twoHeadInverse_spec ⟨he.1.le, he.2.le⟩).1.1
  have hv : ContDiffAt ℝ 2 twoHeadValue (twoHeadInverse (1 / 2 - e2ContactDensity q)) := by
    rw [harg]
    exact twoHeadValue_contDiffAt hi
  have hc := hv.comp (e2ContactDensity q) hinner
  apply hc.congr_of_eventuallyEq
  apply benchmark_twoHead_eventually hd
  · simpa only [harg] using he.1
  · simpa only [harg] using mixedCurve_lt_twoHeadCurve_e2_q hq

/-- The first derivative belongs to the actual selected benchmark branch,
with the original E2 slope expressed in its q parameter. -/
theorem benchmark_hasDerivAt_e2_q {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    HasDerivAt benchmark (-multiplier q) (e2ContactDensity q) := by
  have he := e2_q_density_mem hq
  have harg : 1 / 2 - e2ContactDensity q = missingMass q / 2 := by
    unfold e2ContactDensity
    ring
  have hfirst := benchmark_twoHead_hasDerivAt_of_strict (e2_density_mem hq)
    (by simpa only [harg] using he.1)
    (by simpa only [harg] using mixedCurve_lt_twoHeadCurve_e2_q hq)
  convert hfirst using 1
  rw [harg, twoHeadInverse_e2_q hq]
  have hq2 : q + 2 ≠ 0 := by linarith [hq.1]
  have h2q : 2 + q ≠ 0 := by linarith [hq.1]
  unfold multiplier
  field_simp
  ring

/-- The actual benchmark's second derivative is the exact E2 curvature
formula, including at q = 1/5. Neighboring branch activity follows
from strict dominance, rather than extending the closed q guard. -/
theorem benchmark_second_deriv_e2_q {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    deriv (deriv benchmark) (e2ContactDensity q) = E2PrivateCurvature.curvature q := by
  have he := e2_q_density_mem hq
  have harg : 1 / 2 - e2ContactDensity q = missingMass q / 2 := by
    unfold e2ContactDensity
    ring
  have hnear := strict_twoHead_eventually (e2_density_mem hq)
    (by simpa only [harg] using he.1)
    (by simpa only [harg] using mixedCurve_lt_twoHeadCurve_e2_q hq)
  have hderiv : deriv benchmark =ᶠ[nhds (e2ContactDensity q)]
      (fun x => -multiplier (e2ContactParameter x)) := by
    filter_upwards [hnear] with x hx
    rw [(benchmark_twoHead_hasDerivAt_of_strict hx.1 hx.2.1 hx.2.2).deriv]
    have hix := twoHeadInverse_spec ⟨hx.2.1.le, by linarith [hx.1.1]⟩
    have hiz : twoHeadInverse (1 / 2 - x) ≠ 0 := by linarith [hix.1.1]
    unfold multiplier e2ContactParameter
    field_simp
    ring
  have hQ0 := e2ContactParameter_e2ContactDensity
    (show q ∈ Ioo (0 : ℝ) (1 / 4) from ⟨hq.1, by linarith [hq.2]⟩)
  have houter := (E2PrivateCurvature.multiplier_hasDerivAt hq.1.le).neg
  have hcomposed := houter.comp_of_eq (e2ContactDensity q)
    (e2ContactParameter_hasDerivAt hq) hQ0.symm
  have hsecond := (hcomposed.congr_of_eventuallyEq hderiv).deriv
  rw [hsecond, (e2ContactDensity_hasDerivAt hq.1.le).deriv,
    (E2PrivateCurvature.missingMass_hasDerivAt hq.1.le).deriv]
  have hR := ne_of_gt (denominator_pos hq.1.le)
  have hF := ne_of_gt (E2PrivateCurvature.derivativeFactor_pos ⟨hq.1.le, hq.2⟩)
  have hq2 : q + 2 ≠ 0 := by linarith [hq.1]
  unfold E2PrivateCurvature.curvature
  field_simp
  ring

end Erdos1017.Benchmark
