module

public import Erdos1017.Benchmark.BenchmarkProperties
public import Erdos1017.Benchmark.SplitCurve
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.Lattice

/-!
# Continuity of the benchmark

The mixed and two-head inverses, rational branches and curves are continuous,
with their values at zero and at one quarter, and the benchmark is continuous on
its full density domain (`benchmark_continuousOn`).
-/

@[expose] public section

namespace Erdos1017.Benchmark

/-- `mixedInverse` is continuous on `[ε*, ε_D]`. -/
theorem mixedInverse_continuousOn : ContinuousOn mixedInverse (Set.Icc epsilonStar epsilonD) := by
  have horder : sigmaD ≤ sigmaZero := by linarith [sigmaD_spec.1.2, sigmaZero_bounds.1]
  have hmap : Set.MapsTo mixedDensity (Set.Icc sigmaD sigmaZero) (Set.Icc epsilonStar epsilonD) := by
    intro s hs
    constructor
    · rw [← mixedDensity_sigmaZero]
      exact mixedDensity_strictAntiOn.antitoneOn hs ⟨horder, le_rfl⟩ hs.2
    · exact mixedDensity_strictAntiOn.antitoneOn ⟨le_rfl, horder⟩ hs hs.1
  let e : Set.Icc sigmaD sigmaZero ≃ Set.Icc epsilonStar epsilonD := {
    toFun := fun s => ⟨mixedDensity s, hmap s.property⟩
    invFun := fun x => ⟨mixedInverse x, (mixedInverse_spec x.property).1⟩
    left_inv := fun s => Subtype.ext (mixedInverse_unique (hmap s.property) s.property rfl).symm
    right_inv := fun x => Subtype.ext (mixedInverse_spec x.property).2 }
  have hc : Continuous e := mixedDensity_continuousOn.domRestrict.subtype_mk _
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_subtype_val.comp hc.continuous_symm_of_equiv_compact_to_t2

/-- `twoHeadInverse` is continuous on `[ε_C, 1/4]`. -/
theorem twoHeadInverse_continuousOn : ContinuousOn twoHeadInverse (Set.Icc epsilonC (1 / 4)) := by
  have horder : (2 / 3 : ℝ) ≤ zC := by linarith [zC_spec.1.1]
  have hmap : Set.MapsTo twoHeadDensity (Set.Icc (2 / 3) zC) (Set.Icc epsilonC (1 / 4)) := by
    intro z hz
    constructor
    · exact twoHeadDensity_strictAntiOn.antitoneOn hz ⟨horder, le_rfl⟩ hz.2
    · rw [← twoHeadDensity_two_thirds]
      exact twoHeadDensity_strictAntiOn.antitoneOn ⟨le_rfl, horder⟩ hz hz.1
  let e : Set.Icc (2 / 3) zC ≃ Set.Icc epsilonC (1 / 4) := {
    toFun := fun z => ⟨twoHeadDensity z, hmap z.property⟩
    invFun := fun x => ⟨twoHeadInverse x, (twoHeadInverse_spec x.property).1⟩
    left_inv := fun z => Subtype.ext (twoHeadInverse_unique (hmap z.property) z.property rfl).symm
    right_inv := fun x => Subtype.ext (twoHeadInverse_spec x.property).2 }
  have hc : Continuous e := twoHeadDensity_continuousOn.domRestrict.subtype_mk _
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_subtype_val.comp hc.continuous_symm_of_equiv_compact_to_t2

/-- The split junction of `W` is positive: `0 < ε*`. -/
theorem epsilonStar_pos : 0 < epsilonStar := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  unfold epsilonStar
  nlinarith

/-- The end of the mixed branch of `W` satisfies `ε_D < 1/4`. -/
theorem epsilonD_lt_quarter : epsilonD < 1 / 4 := by
  have hc : ContinuousOn mixedDensity (Set.Icc 1 sigmaZero) := by
    intro s hs
    have hd := mixedDenominator_pos (by linarith [hs.1] : 0 ≤ s)
    unfold mixedDenominator at hd
    unfold mixedDensity mixedDenominator
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hm : StrictAntiOn mixedDensity (Set.Icc 1 sigmaZero) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
    intro s hs
    have hs1 := (interior_subset hs).1
    have hs0 : 0 < s := by linarith
    rw [(mixedDensity_hasDerivAt hs0.le).deriv]
    apply div_neg_of_neg_of_pos
    · have : 0 < 2 + 24 * s + 93 * s ^ 2 + 120 * s ^ 3 := by positivity
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs0) this
    · exact pow_pos (mixedDenominator_pos hs0.le) 3
  have h := hm.antitoneOn (show (1 : ℝ) ∈ Set.Icc 1 sigmaZero from
    ⟨le_rfl, by linarith [sigmaZero_bounds.1]⟩)
    (show sigmaD ∈ Set.Icc 1 sigmaZero from
      ⟨sigmaD_spec.1.1, by linarith [sigmaD_spec.1.2, sigmaZero_bounds.1]⟩) sigmaD_spec.1.1
  norm_num [mixedDensity, mixedDenominator] at h
  change mixedDensity sigmaD < 1 / 4
  unfold mixedDensity mixedDenominator
  linarith

/-- The split branch `e ↦ H(√(2e))` is continuous on `[0, 1/4]`. -/
theorem splitDensity_continuousOn :
    ContinuousOn (fun e : ℝ => splitValue (Real.sqrt (2 * e))) (Set.Icc 0 (1 / 4)) := by
  apply splitValue_continuousOn.comp (by fun_prop)
  intro e he
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  apply (Real.sqrt_le_iff).mpr
  constructor <;> nlinarith [he.2]

/-- The mixed branch `e ↦ mixedValue (mixedInverse e)` is continuous on `[ε*, ε_D]`. -/
theorem mixedRational_continuousOn :
    ContinuousOn (fun e => mixedValue (mixedInverse e)) (Set.Icc epsilonStar epsilonD) := by
  have hc : ContinuousOn mixedValue (Set.Icc sigmaD sigmaZero) := by
    intro s hs
    have hd := mixedDenominator_pos (by linarith [sigmaD_spec.1.1, hs.1] : 0 ≤ s)
    unfold mixedDenominator at hd
    unfold mixedValue mixedDenominator
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  exact hc.comp mixedInverse_continuousOn (fun _ he => (mixedInverse_spec he).1)

/-- The two-head branch `e ↦ twoHeadValue (twoHeadInverse e)` is continuous on `[ε_C, 1/4]`. -/
theorem twoHeadRational_continuousOn :
    ContinuousOn (fun e => twoHeadValue (twoHeadInverse e)) (Set.Icc epsilonC (1 / 4)) := by
  have hc : ContinuousOn twoHeadValue (Set.Icc (2 / 3) zC) := by
    intro z hz
    have hd := twoHeadDenominator_pos hz.1
    unfold twoHeadDenominator at hd
    unfold twoHeadValue twoHeadDensity twoHeadDenominator
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  exact hc.comp twoHeadInverse_continuousOn (fun _ he => (twoHeadInverse_spec he).1)

/-- The curve `W` is continuous on `[0, 1/4]`. -/
theorem mixedCurve_continuousOn : ContinuousOn mixedCurve (Set.Icc 0 (1 / 4)) := by
  have hfirst : ContinuousOn mixedCurve (Set.Icc 0 epsilonStar) := by
    apply (continuousOn_congr (fun e he => show mixedCurve e = splitValue (Real.sqrt (2 * e)) by
      exact ite_eq_left he.2)).mpr
    exact splitDensity_continuousOn.mono (fun e he =>
      ⟨he.1, he.2.trans (epsilonStar_lt_epsilonD.trans epsilonD_lt_quarter).le⟩)
  have hmiddle : ContinuousOn mixedCurve (Set.Icc epsilonStar epsilonD) := by
    apply (continuousOn_congr (fun e he => show mixedCurve e = mixedValue (mixedInverse e) by
      by_cases heq : e = epsilonStar
      · subst e
        rw [mixed_branch_match]
        exact ite_eq_left le_rfl
      · have hlt : epsilonStar < e := lt_of_le_of_ne he.1 (Ne.symm heq)
        simp only [mixedCurve, not_le.mpr hlt, ite_false, he.2, ite_true])).mpr
    exact mixedRational_continuousOn
  have hlast : ContinuousOn mixedCurve (Set.Icc epsilonD (1 / 4)) := by
    apply (continuousOn_congr (fun e he => show mixedCurve e = e by
      by_cases heq : e = epsilonD
      · simpa only [heq] using mixedCurve_epsilonD
      · have hlt : epsilonD < e := lt_of_le_of_ne he.1 (Ne.symm heq)
        simp only [mixedCurve, not_le.mpr (epsilonStar_lt_epsilonD.trans hlt), ite_false,
          not_le.mpr hlt])).mpr
    exact continuousOn_id
  have hjoin := (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc).mpr ⟨hfirst, hmiddle⟩
  rw [Set.Icc_union_Icc_eq_Icc epsilonStar_pos.le epsilonStar_lt_epsilonD.le] at hjoin
  have hfull := (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc).mpr ⟨hjoin, hlast⟩
  rwa [Set.Icc_union_Icc_eq_Icc (epsilonStar_pos.trans epsilonStar_lt_epsilonD).le
    epsilonD_lt_quarter.le] at hfull

/-- The curve `E₂` is continuous on `[0, 1/4]`. -/
theorem twoHeadCurve_continuousOn : ContinuousOn twoHeadCurve (Set.Icc 0 (1 / 4)) := by
  have heC : 0 < epsilonC := by linarith [epsilonC_bounds.1]
  have hfirst : ContinuousOn twoHeadCurve (Set.Icc 0 epsilonC) := by
    apply (continuousOn_congr (fun e he => show twoHeadCurve e = splitValue (Real.sqrt (2 * e)) by
      by_cases he0 : e = 0
      · simp [he0, twoHeadCurve, splitValue]
      · simp only [twoHeadCurve, he0, ite_false, he.2, ite_true])).mpr
    exact splitDensity_continuousOn.mono (fun e he => ⟨he.1, he.2.trans epsilonC_lt_quarter.le⟩)
  have hsecond : ContinuousOn twoHeadCurve (Set.Icc epsilonC (1 / 4)) := by
    apply (continuousOn_congr (fun e he => show twoHeadCurve e = twoHeadValue (twoHeadInverse e) by
      have he0 : e ≠ 0 := ne_of_gt (heC.trans_le he.1)
      by_cases heq : e = epsilonC
      · subst e
        rw [twoHead_branch_match]
        simp only [twoHeadCurve, he0, ite_false, le_refl, ite_true]
      · have hlt : epsilonC < e := lt_of_le_of_ne he.1 (Ne.symm heq)
        simp only [twoHeadCurve, he0, ite_false, not_le.mpr hlt])).mpr
    exact twoHeadRational_continuousOn
  have hfull := (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc).mpr ⟨hfirst, hsecond⟩
  rwa [Set.Icc_union_Icc_eq_Icc heC.le epsilonC_lt_quarter.le] at hfull

/-- The curve `W` satisfies `W(0) = 0`. -/
@[simp] theorem mixedCurve_zero : mixedCurve 0 = 0 := by
  simp [mixedCurve, epsilonStar_pos.le, splitValue]

/-- The curve `E₂` satisfies `E₂(0) = 0`. -/
@[simp] theorem twoHeadCurve_zero : twoHeadCurve 0 = 0 := by
  simp [twoHeadCurve]

/-- The curve `W` satisfies `W(1/4) = 1/4`. -/
@[simp] theorem mixedCurve_quarter : mixedCurve (1 / 4) = 1 / 4 := by
  simp only [mixedCurve, not_le.mpr (epsilonStar_lt_epsilonD.trans epsilonD_lt_quarter),
    ite_false, not_le.mpr epsilonD_lt_quarter]

end Erdos1017.Benchmark

namespace Erdos1017

/-- The explicit benchmark is continuous on its full density domain. -/
theorem benchmark_continuousOn : ContinuousOn benchmark (Set.Icc (0 : ℝ) (1 / 2)) := by
  have hfirst : ContinuousOn benchmark (Set.Icc (0 : ℝ) (1 / 4)) := by
    apply (continuousOn_congr (fun _ hd => benchmark_of_le_quarter hd.2)).mpr
    exact continuousOn_id
  have hsecond : ContinuousOn benchmark (Set.Icc (1 / 4 : ℝ) (1 / 2)) := by
    have hc := (Benchmark.mixedCurve_continuousOn.sup Benchmark.twoHeadCurve_continuousOn).comp
      (show ContinuousOn (fun d : ℝ => 1 / 2 - d) (Set.Icc (1 / 4) (1 / 2)) by fun_prop)
      (show Set.MapsTo (fun d : ℝ => 1 / 2 - d) (Set.Icc (1 / 4) (1 / 2)) (Set.Icc 0 (1 / 4)) by
        intro d hd
        constructor <;> linarith [hd.1, hd.2])
    apply (continuousOn_congr (fun d hd => show benchmark d =
      max (Benchmark.mixedCurve (1 / 2 - d)) (Benchmark.twoHeadCurve (1 / 2 - d)) by
      by_cases hq : d = 1 / 4
      · subst d
        rw [benchmark_of_le_quarter le_rfl]
        norm_num only [show (1 / 2 - 1 / 4 : ℝ) = 1 / 4 by norm_num,
          Benchmark.mixedCurve_quarter, Benchmark.twoHeadCurve_quarter, max_self]
      · by_cases hh : d = 1 / 2
        · subst d
          rw [benchmark_half]
          simp
        · have hq' : 1 / 4 < d := lt_of_le_of_ne hd.1 (Ne.symm hq)
          have hh' : d < 1 / 2 := lt_of_le_of_ne hd.2 hh
          simp only [benchmark, not_le.mpr hq', ite_false, hh', ite_true])).mpr
    exact hc
  have hfull := (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc).mpr ⟨hfirst, hsecond⟩
  rwa [Set.Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at hfull

end Erdos1017
