module

public import Erdos1017.Exclusions.Common.Covered.CoveredTwoNeighborOwnRows
public import Erdos1017.Exclusions.Common.Covered.CoveredTwoNeighborRepeatObstruction
public import Erdos1017.Exclusions.Common.Covered.FullCoveredCopyVariation

/-!
# Copy bounds for the two-neighbor model

Covered `Ci`/`R` and `R`/`R` copying gives three penalty budgets on the same
original law and own optimum, and together with positive own gamma, default
repeats and the rooted triangle test makes all seven coefficients positive
(`own_coefficients_pos`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredTwoExteriorNeighbor

open CappedModel VertexClassification

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem integral_labels (label : Ω → Fin 5) (hlabel : Measurable label)
    (f : Fin 5 → ℝ) :
    (∫ z, f (label z) ∂μ) = ∑ i, μ.real (label ⁻¹' {i}) * f i := by
  have he : (fun z => f (label z)) =
      fun z => ∑ i, (label ⁻¹' {i}).indicator (fun _ => f i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hlabel (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hlabel (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

private theorem block_property_of_ae (label : Ω → Fin 5)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (P : Fin 5 → Fin 5 → Prop)
    (hP : ∀ᵐ p ∂μ.prod μ, P (label p.1) (label p.2)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨x, hx, hpx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hP))
  obtain ⟨z, hz, hpz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive j).ne' (ae_restrict_of_ae hpx)
  exact hx ▸ hz ▸ hpz

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual covered Ci/R and R/R copying gives the three penalty budgets
on the same original law and own optimum. -/
theorem copy_penalty_mass_bounds {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    2 * (c - m * d) + m ≤ μ.real (label ⁻¹' {1}) * x 6 ∧
    2 * (c - m * d) + m + μ.real (label ⁻¹' {0}) * x 2 ≤
      (μ.real (label ⁻¹' {1}) - μ.real (label ⁻¹' {2})) * x 4 ∧
    2 * (c - m * d) + m + μ.real (label ⁻¹' {0}) * x 2 ≤
      (μ.real (label ⁻¹' {1}) - μ.real (label ⁻¹' {3})) * x 5 := by
  let G := blockAdjacency
  let C := blockCharge x
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := label ⁻¹' {1}
  let mass (i : Fin 5) := μ.real (label ⁻¹' {i})
  let nu := 2 * (c - m * d)
  let rY (i j k : Fin 5) : ℝ :=
    if (G i k && G j k) = true then C i k + C j k + C i j * (if k = 1 then 1 else 0)
    else 0
  let rA (i j k : Fin 5) : ℝ := if (G i k && G j k) = true then 1 else 0
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
    fin_cases i <;> fin_cases j <;>
      simp_all [blockCharge, hx.1 2, hx.1 3, hx.1 4, hx.1 5, hx.1 6]
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
  have hC1R := hblocks 2 4 (by decide) (by decide) rfl
  have hC2R := hblocks 3 4 (by decide) (by decide) rfl
  have hRR := hblocks 4 4 (by decide) (by decide) rfl
  have hrows := finite_rows_of_fullStationaryClass hW label hlabel hpositive x hmom
  have hC1 := hrows 2
  have hC2 := hrows 3
  have hR := hrows 4
  have hmass : mass 0 + mass 1 + mass 2 + mass 3 + mass 4 = 1 := by
    have h := integral_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, mass, add_assoc] using h.symm
  have hMmass := congrArg (fun v : ℝ => m * v) hmass
  simp [rY, rA, G, C, blockAdjacency, blockCharge, Fin.sum_univ_succ] at hC1R hC2R hRR
  simp [blockAdjacency, blockCharge, Fin.sum_univ_succ] at hC1 hC2 hR
  dsimp only [mass, nu] at hC1R hC2R hRR hMmass
  constructor
  · nlinarith only [hRR, hR, hMmass]
  constructor
  · nlinarith only [hC1R, hC1, hR, hMmass]
  · nlinarith only [hC2R, hC2, hR, hMmass]

/-- Positive own gamma, the actual copying budgets, default repeats and
the genuine rooted triangle test make all seven coefficients positive.
No clipping, compact-face selection or transferred multiplier is assumed. -/
theorem own_coefficients_pos {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : x ∈ feasible)
    (hell : (1 / 2 : ℝ) < -m)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    ∀ i, 0 < x i := by
  have hgamma := (hW.strict_gap_structure hd hgap).gamma_pos
  have hrow := own_R_row hW label hlabel hpositive x hmom
  have hab := a_lt_b_of_fullStationaryClass hW hd hgap label hlabel hpositive x hx hmom
  have hz1 := mul_nonneg (show 0 ≤ μ.real (label ⁻¹' {2}) from measureReal_nonneg) (hx.1 4)
  have hz2 := mul_nonneg (show 0 ≤ μ.real (label ⁻¹' {3}) from measureReal_nonneg) (hx.1 5)
  have hp := mul_nonneg (show 0 ≤ μ.real (label ⁻¹' {4}) from measureReal_nonneg) (hx.1 6)
  have hh : 0 < x 2 := by
    by_contra h
    have hbad := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab.le) (le_of_not_gt h)
    linarith only [hrow, hgamma, hz1, hz2, hp, hbad]
  obtain ⟨hcopyP, hcopy1, hcopy2⟩ :=
    copy_penalty_mass_bounds hW hd hgap label hlabel hpositive x hx hmom
  have hleft : 0 < 2 * (c - m * d) + m + μ.real (label ⁻¹' {0}) * x 2 :=
    add_pos_of_pos_of_nonneg hgamma (mul_nonneg measureReal_nonneg hh.le)
  have h4 : 0 < x 4 := by
    by_contra h
    have hz : x 4 = 0 := le_antisymm (le_of_not_gt h) (hx.1 4)
    rw [hz, mul_zero] at hcopy1
    linarith only [hleft, hcopy1]
  have h5 : 0 < x 5 := by
    by_contra h
    have hz : x 5 = 0 := le_antisymm (le_of_not_gt h) (hx.1 5)
    rw [hz, mul_zero] at hcopy2
    linarith only [hleft, hcopy2]
  have h6 : 0 < x 6 := by
    by_contra h
    have hz : x 6 = 0 := le_antisymm (le_of_not_gt h) (hx.1 6)
    rw [hz, mul_zero] at hcopyP
    linarith only [hgamma, hcopyP]
  obtain ⟨ht1, ht2⟩ := stars_gt_own_multiplier hW hd hgap label hlabel hpositive x hx hmom
  have htriangle := hx.2 ((true, true), 0)
  norm_num [VertexClassification.test, VertexClassification.constant,
    VertexClassification.slope] at htriangle
  have h3 : 0 < x 3 := by linarith only [ht1, ht2, hell, htriangle]
  intro i
  fin_cases i
  · change 0 < x 0
    linarith only [ht1, hell]
  · change 0 < x 1
    linarith only [ht2, hell]
  · exact hh
  · exact h3
  · exact h4
  · exact h5
  · exact h6

end Erdos1017.CoveredTwoExteriorNeighbor
