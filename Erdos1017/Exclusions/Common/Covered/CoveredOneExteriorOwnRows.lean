module

public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorRepeatObstruction
public import Erdos1017.Exclusions.Common.Covered.FullCoveredCopyVariation

/-!
# Own rows of the one-exterior model

From the model's own stationary event, the finite shifted rows, the
`A`-minus-`C` row difference, the strict penalty ceiling, the copy penalty bound
and the `E` charge row are derived, so that all coordinates are positive, `t<1`,
and the full-repeat obstruction holds (`own_row_parameters`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredOneExterior

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem integral_labels (label : Ω → Fin 4) (hlabel : Measurable label)
    (f : Fin 4 → ℝ) :
    (∫ z, f (label z) ∂μ) = ∑ i, μ.real (label ⁻¹' {i}) * f i := by
  have he : (fun z => f (label z)) =
      fun z => ∑ i, (label ⁻¹' {i}).indicator (fun _ => f i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hlabel (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hlabel (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

private theorem block_property_of_ae (label : Ω → Fin 4)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (P : Fin 4 → Fin 4 → Prop)
    (hP : ∀ᵐ p ∂μ.prod μ, P (label p.1) (label p.2)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨x, hx, hpx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hP))
  obtain ⟨z, hz, hpz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive j).ne' (ae_restrict_of_ae hpx)
  exact hx ▸ hz ▸ hpz

/-- Every finite shifted row comes from the own actual stationary event
on its positive original fiber. -/
theorem finite_rows_of_fullStationaryClass {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    ∀ i, (∑ j, μ.real (label ⁻¹' {j}) *
      (blockCharge y i j - m * (if blockAdjacency i j = true then 1 else 0))) =
        2 * (c - m * d) := by
  intro i
  obtain ⟨z, hz, hstat⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae hW.stationary)
  have hlabelz : label z = i := hz
  have heq : (∫ w, shiftedKernel W m z w ∂μ) =
      ∫ w, blockCharge y i (label w) - m *
        (if blockAdjacency i (label w) = true then 1 else 0) ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun w => by
      rw [shiftedKernel, shiftedMoment_eq, (hmom (z, w)).1, (hmom (z, w)).2, hlabelz])
  rw [heq, integral_labels label hlabel (fun j => blockCharge y i j - m *
    (if blockAdjacency i j = true then 1 else 0))] at hstat
  exact hstat

/-- The actual A-minus-C stationary equation retains the own multiplier
and the literal original B and E masses. -/
theorem stationary_row_difference {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    μ.real (label ⁻¹' {1}) * (1 - y 0) =
      μ.real (label ⁻¹' {3}) * (-m - y 2) := by
  have hrows := finite_rows_of_fullStationaryClass hW label hlabel hpositive y hmom
  have hA := hrows 0
  have hC := hrows 2
  norm_num [blockCharge, blockAdjacency, Fin.sum_univ_succ] at hA hC
  nlinarith only [hA, hC]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Own strict support on the positive original C-E rectangle gives its
strict present-block penalty ceiling, without an original multiplier transfer. -/
theorem penalty_lt_own_multiplier {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    y 2 < -m := by
  have hfinite := block_property_of_ae label hpositive
    (fun i j => blockAdjacency i j = true → 0 < blockCharge y i j - m) (by
      filter_upwards [(hW.strict_gap_structure hd hgap).strict_support] with p hp hG
      have hpos : 0 < shiftedMoment W m p := by
        by_contra h
        simp only [(hmom p).1, hG, ite_true, h, ite_false] at hp
        norm_num at hp
      rw [shiftedMoment_eq, (hmom p).1, (hmom p).2, hG] at hpos
      simpa only [ite_true, mul_one] using hpos)
  have h := hfinite 2 3 rfl
  norm_num [blockCharge] at h
  linarith

/-- Genuine covered C/E copying derives the strengthened penalty bound
from the actual own optimum. The body sign, finite rows and common-good
sections are constructed from the literal sign-feasible matrix. -/
theorem copy_penalty_mass_bound {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients) (hy : y ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    2 * (c - m * d) + m - m * μ.real (label ⁻¹' {0}) ≤
      y 2 * (μ.real (label ⁻¹' {1}) - μ.real (label ⁻¹' {2})) := by
  let G := blockAdjacency
  let C := blockCharge y
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := label ⁻¹' {1}
  let mass (i : Fin 4) := μ.real (label ⁻¹' {i})
  let nu := 2 * (c - m * d)
  let rY (i j k : Fin 4) : ℝ :=
    if (G i k && G j k) = true then C i k + C j k + C i j * (if k = 1 then 1 else 0)
    else 0
  let rA (i j k : Fin 4) : ℝ := if (G i k && G j k) = true then 1 else 0
  have hI : MeasurableSet I := hlabel (measurableSet_singleton 1)
  have hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I →
      adjacencyKernel W p.1 p.2 = 0 := by
    exact Eventually.of_forall (fun p hi hj => by
      change label p.1 = 1 at hi
      change label p.2 = 1 at hj
      change W.moment CappedColor.adjacency p = 0
      simp [hmom p, hi, hj, blockAdjacency])
  have hbody : ∀ᵐ p ∂μ.prod μ,
      p.1 ∉ I → p.2 ∉ I → chargeKernel W p.1 p.2 ≤ 0 := by
    apply Eventually.of_forall
    intro p hi hj
    change label p.1 ≠ 1 at hi
    change label p.2 ≠ 1 at hj
    change W.moment CappedColor.charge p ≤ 0
    rw [(hmom p).2]
    generalize label p.1 = i at hi ⊢
    generalize label p.2 = j at hj ⊢
    fin_cases i <;> fin_cases j <;> simp_all [blockCharge, hy.1 2, hy.1 3]
  have hcopy := hW.ae_covered_copy_shifted_row_le_stationary hd hgap I hI hind hbody
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hrep : ∀ᵐ p ∂μ.prod μ,
      A p.1 p.2 = G (label p.1) (label p.2) ∧
        Y p.1 p.2 = C (label p.1) (label p.2) := by
    filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hs,
      PhysicalRepresentative.charge_ae_eq W m hs] with p ha hy
    have he := ha.symm.trans (hmom p).1
    change (if A p.1 p.2 = true then (1 : ℝ) else 0) =
      (if G (label p.1) (label p.2) = true then 1 else 0) at he
    constructor
    · cases hA : A p.1 p.2 <;> cases hG : G (label p.1) (label p.2) <;> simp_all
    · exact hy.trans (hmom p).2
  have hsections := Measure.ae_ae_of_ae_prod hrep
  have hpair : ∀ᵐ p ∂μ.prod μ,
      label p.1 ≠ 1 → label p.2 ≠ 1 → G (label p.1) (label p.2) = true →
      (∑ k, mass k * rY (label p.1) (label p.2) k) -
        m * (∑ k, mass k * rA (label p.1) (label p.2) k) ≤ nu := by
    filter_upwards [hcopy, hrep, Measure.quasiMeasurePreserving_fst.ae hsections,
      Measure.quasiMeasurePreserving_snd.ae hsections] with p hp he hx hy hpx hpy hG
    have h := hp hpx hpy (he.1.trans hG)
    have hrowY : IndependentAtomCopy.rowCharge A Y I p.1 p.2 =ᵐ[μ]
        fun z => rY (label p.1) (label p.2) (label z) := by
      filter_upwards [hx, hy] with z hx hy
      change (if (A p.1 z && A p.2 z) = true then
        Y p.1 z + Y p.2 z + Y p.1 p.2 * I.indicator (fun _ => 1) z else 0) = _
      rw [hx.1, hy.1, hx.2, hy.2, he.2]
      by_cases hz : label z = 1 <;> simp [rY, I, hz]
    have hrowA : IndependentAtomCopy.rowAdjacency A p.1 p.2 =ᵐ[μ]
        fun z => rA (label p.1) (label p.2) (label z) := by
      filter_upwards [hx, hy] with z hx hy
      change (if (A p.1 z && A p.2 z) = true then (1 : ℝ) else 0) = _
      rw [hx.1, hy.1]
    change (∫ z, IndependentAtomCopy.rowCharge A Y I p.1 p.2 z ∂μ) -
      m * (∫ z, IndependentAtomCopy.rowAdjacency A p.1 p.2 z ∂μ) ≤ nu at h
    rw [integral_congr_ae hrowY, integral_congr_ae hrowA,
      integral_labels label hlabel (rY (label p.1) (label p.2)),
      integral_labels label hlabel (rA (label p.1) (label p.2))] at h
    exact h
  have hblocks := block_property_of_ae label hpositive
    (fun i j => i ≠ 1 → j ≠ 1 → G i j = true →
      (∑ k, mass k * rY i j k) - m * (∑ k, mass k * rA i j k) ≤ nu) hpair
  have hCE := hblocks 2 3 (by decide) (by decide) rfl
  have hrows := finite_rows_of_fullStationaryClass hW label hlabel hpositive y hmom
  have hC := hrows 2
  have hE := hrows 3
  have hmass : mass 0 + mass 1 + mass 2 + mass 3 = 1 := by
    have h := integral_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, mass, add_assoc] using h.symm
  have hMmass := congrArg (fun v : ℝ => m * v) hmass
  simp [rY, rA, G, C, blockAdjacency, blockCharge, Fin.sum_univ_succ] at hCE
  simp [blockAdjacency, blockCharge, Fin.sum_univ_succ] at hC hE
  dsimp only [mass, nu] at hCE hMmass
  nlinarith only [hCE, hC, hE, hMmass]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The literal E charge row has the positive own gamma intercept and
retains the original A mass. -/
theorem own_E_charge {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    2 * (c - m * d) + m - m * μ.real (label ⁻¹' {0}) =
      μ.real (label ⁻¹' {1}) * y 1 - μ.real (label ⁻¹' {2}) * y 2 -
        μ.real (label ⁻¹' {3}) * y 3 := by
  have hE := finite_rows_of_fullStationaryClass hW label hlabel hpositive y hmom 3
  have hmass : μ.real (label ⁻¹' {0}) + μ.real (label ⁻¹' {1}) +
      μ.real (label ⁻¹' {2}) + μ.real (label ⁻¹' {3}) = 1 := by
    have h := integral_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, add_assoc] using h.symm
  have hm := congrArg (fun v : ℝ => m * v) hmass
  norm_num [blockCharge, blockAdjacency, Fin.sum_univ_succ] at hE
  nlinarith only [hE, hm]

/-- Own rows, strict support, actual covered copying and all E-axis tests
make both penalties and the E star strictly positive, and give t<1. -/
theorem positive_parameters_and_star_upper {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients) (hy : y ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    0 < y 1 ∧ 0 < y 2 ∧ 0 < y 3 ∧ y 0 < 1 := by
  have hs := hW.strict_gap_structure hd hgap
  have hE := own_E_charge hW label hlabel hpositive y hmom
  have hleft : 0 < 2 * (c - m * d) + m - m * μ.real (label ⁻¹' {0}) := by
    have hprod := mul_nonpos_of_nonpos_of_nonneg hs.multiplier_neg.le
      (show 0 ≤ μ.real (label ⁻¹' {0}) from measureReal_nonneg)
    linarith only [hs.gamma_pos, hprod]
  have hcopy := copy_penalty_mass_bound hW hd hgap label hlabel hpositive y hy hmom
  have hdpos : 0 < y 2 := by
    by_contra h
    have hz : y 2 = 0 := le_antisymm (le_of_not_gt h) (hy.1 2)
    rw [hz, zero_mul] at hcopy
    linarith only [hleft, hcopy]
  have hvpos : 0 < y 1 := by
    by_contra h
    have hB := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ μ.real (label ⁻¹' {1}) from measureReal_nonneg) (le_of_not_gt h)
    have hC := mul_nonneg (show 0 ≤ μ.real (label ⁻¹' {2}) from measureReal_nonneg) (hy.1 2)
    have hQ := mul_nonneg (show 0 ≤ μ.real (label ⁻¹' {3}) from measureReal_nonneg) (hy.1 3)
    linarith only [hE, hleft, hB, hC, hQ]
  have hqpos : 0 < y 3 := by
    by_contra h
    have hqzero : y 3 = 0 := le_antisymm (le_of_not_gt h) (hy.1 3)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / y 1)
    have hlarge := (div_lt_iff₀ hvpos).mp hn
    have htest := hy.2 false n
    simp [test_eq_value, constant, slope, TightCounts.value, hqzero] at htest
    nlinarith only [hlarge, htest]
  have hrow := stationary_row_difference hW label hlabel hpositive y hmom
  have hpen := penalty_lt_own_multiplier hW hd hgap label hpositive y hmom
  have hepos : 0 < μ.real (label ⁻¹' {3}) :=
    ENNReal.toReal_pos (hpositive 3).ne' (measure_ne_top _ _)
  have hright := mul_pos hepos (sub_pos.mpr hpen)
  have ht : y 0 < 1 := by
    by_contra h
    have hbad := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ μ.real (label ⁻¹' {1}) from measureReal_nonneg)
      (sub_nonpos.mpr (le_of_not_gt h))
    linarith only [hrow, hright, hbad]
  exact ⟨hvpos, hdpos, hqpos, ht⟩

/-- The actual own model supplies all positive coordinates, t<1, its
stationary row and every full-repeat obstruction. The sign-feasible system
remains explicit; strict positivity, rows, copying and completion are derived. -/
theorem own_row_parameters {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients) (hy : y ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    (∀ i, 0 < y i) ∧ y 0 < 1 ∧
      μ.real (label ⁻¹' {1}) * (1 - y 0) = μ.real (label ⁻¹' {3}) * (-m - y 2) ∧
      ∀ D : ℝ, (∀ r n, repeatCharge (y 0) (y 1) (y 2) (y 3) D r n ≤ 1) → -m < D := by
  obtain ⟨hv, hdpos, hq, ht⟩ :=
    positive_parameters_and_star_upper hW hd hgap label hlabel hpositive y hy hmom
  have hstar := star_gt_own_multiplier hW hd hgap label hlabel (hpositive 2) y hy hmom
  have htpos : 0 < y 0 :=
    (neg_pos.mpr (hW.strict_gap_structure hd hgap).multiplier_neg).trans hstar
  refine ⟨?_, ht, stationary_row_difference hW label hlabel hpositive y hmom,
    repeat_penalty_gt_own_multiplier hW hd hgap label hlabel (hpositive 2) y hy hmom⟩
  intro i
  fin_cases i
  · exact htpos
  · exact hv
  · exact hdpos
  · exact hq

end Erdos1017.CoveredOneExterior
