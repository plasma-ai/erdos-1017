module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeEndpointBounds
public import Erdos1017.Exclusions.Cusp.SelectedCuspFourSourceGuards
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourcePeakGuards

/-!
# Scalar guards for the third-cusp high-slope source

The third-cusp height rules out an independent entire source, the same common
peak pays the head ordering, independent union and strict reserve of the child
payment, and original source geometry with the reverse endpoint gives the
normalized domain without dividing by the own penalty minus one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- The actual third-cusp height rules out an independent entire source,
including own penalty exactly one. -/
theorem cusp_three_source_edge_integral_pos (R : S.ReverseRecovery)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (hell : 1 ≤ -m) :
    0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  obtain ⟨r, hr⟩ := R.cusp_three_plateau_singleton hdk hW hgap hell
  by_contra hn
  have hzero : (∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ) = 0 :=
    le_antisymm (le_of_not_gt hn) (integral_nonneg (fun p => (adjacency_moment_mem W p).1))
  let P := {x | S.ρ x = r.val}
  let C := S.reverseCompulsorySource R.plateau
  have hP : MeasurableSet P := (S.hfibers r.val r.property).1
  have hC : MeasurableSet C := R.measurableSet_source
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hSource : C = S.reverseCompulsorySource {r} := by dsimp [C]; rw [hr]
  rw [← hSource] at hg
  have hi : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using KernelOperator.integrable_kernel_bilinear
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hCC : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ C → adjacencyKernel W p.1 p.2 = 0 := by
    have he := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun p : Ω × Ω => (adjacency_moment_mem W p).1))
      hi.integrableOn).mp hzero
    exact ((ae_restrict_iff' (hC.prod hC)).mp he).mono (fun _ hp hx hy => hp ⟨hx, hy⟩)
  have hind : ∀ᵐ p ∂(μ.restrict (P ∪ C)).prod (μ.restrict (P ∪ C)),
      adjacencyKernel W p.1 p.2 = 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' ((hP.union hC).prod (hP.union hC))).mpr
    filter_upwards [hg.zero_II, hg.zero_IC, hCC,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.zero_IC,
      adjacencyKernel_symm W] with p hPP hPC hCC hCP hs hp
    rcases hp.1 with hx | hx <;> rcases hp.2 with hy | hy
    · exact hPP hx hy
    · exact hPC hx hy
    · exact hs.trans (hCP hy hx)
    · exact hCC hx hy
  have hsquare := independent_set_mass_sq_le_missing_density W (P ∪ C) (hP.union hC) hind
  rw [measureReal_union hg.disjoint_IC hC, hW.density_eq] at hsquare
  have hheight := R.singleton_height_eq_mass_add_source r hr
  rw [← hSource] at hheight
  change R.height = μ.real P + μ.real C at hheight
  rw [← hheight] at hsquare
  rw [hdk] at hsquare
  have hheightLower := R.cusp_three_height_gt_third hdk hW hgap hglobal hell
  nlinarith only [hsquare, hheightLower]

/-- The same original common peak pays the head ordering, independent union
and strict reserve used by the cusp child payment. No endpoint atom is used. -/
theorem cusp_three_source_peak_guards (R : S.ReverseRecovery) (r i : S.I)
    (hdk : d = 4 / 9)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) :
    S.originalAtomMass r < S.originalAtomMass i ∧
      (S.originalAtomMass r + S.originalAtomMass i) ^ 2 ≤ 1 / 9 ∧
      (4 / 3 + m) / 9 <
        (2 + m) * (S.originalAtomMass i) ^ 2 := by
  obtain ⟨hd, _, hell, _, hmargin⟩ :=
    hW.cusp_contact_parameters 3 (by norm_num)
      (show d = (1 - 1 / (3 : ℝ) ^ 2) / 2 by norm_num [hdk]) hgap hglobal
  norm_num only [Nat.cast_ofNat] at hmargin
  have hri : r ≠ i := by
    intro heq
    subst i
    obtain ⟨x, hx, hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers r.val r.property).2.1.ne' hinside
    have hdis : Disjoint {x | S.ρ x = r.val} R.cuspSource := by
      rw [cuspSource, hr]
      exact S.disjoint_singleton_fiber_source r
    exact Set.disjoint_left.mp hdis hx hs
  obtain ⟨hDelta, j, _, _, hj, hlargest, hreserve, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  have hQi : (S.originalAtomMass i) ^ 2 ≤ ∑' j, (S.originalAtomMass j) ^ 2 := by
    simpa only [Finset.sum_singleton] using Summable.sum_le_tsum (s := {i})
      (fun j _ => sq_nonneg (S.originalAtomMass j)) S.originalAtomMass_sq_summable
  have hweighted := mul_le_mul_of_nonneg_left hQi (show 0 ≤ -m by linarith [hell.1])
  have hmass := R.cusp_source_peak_mass_sq_le_missing r i hW hd hgap hr hinside
  rw [hdk] at hmass
  exact ⟨hlargest r hri, by linarith only [hmass],
    by nlinarith only [hmargin, hreserve, hweighted]⟩


/-- Original source geometry and the actual reverse endpoint give the
third-cusp normalized domain without dividing by the own penalty minus one. -/
theorem cusp_three_high_source_normalized_guards (R : S.ReverseRecovery) (r i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) (hell : 1 ≤ -m)
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) :
    let X := S.originalAtomMass i / R.height
    let t := μ.real (R.cuspSourceRemainder i) / R.height
    let y := (1 / 9 : ℝ) / R.height ^ 2
    let q := R.cuspOutsideSquares r i / R.height ^ 2
    0 < X ∧ 0 < t ∧ X + t < 1 ∧ (1 - t) / 2 < X ∧
      y ∈ Ioo (16 / 25 : ℝ) 1 ∧ -m ∈ Ico (1 : ℝ) (4 / 3) ∧ 0 ≤ q ∧
      q < (25 / 16) * y - 1 ∧
      (4 / 3 + m) * y < (2 + m) * X ^ 2 ∧ 1 - t ^ 2 - 2 * X * t ≤ y := by
  let T := R.height
  let A := S.originalAtomMass i
  let b := S.originalAtomMass r
  let z := μ.real (R.cuspSourceRemainder i)
  let Q := R.cuspOutsideSquares r i
  let ell := -m
  let δ := 4 / 3 - ell
  have hdk' : d = (1 - 1 / (3 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  have hp := hW.cusp_contact_parameters 3 (by norm_num) hdk' hgap hglobal
  have hd := hp.1
  have hellUpper : ell < 4 / 3 := by
    have h := hp.2.1
    norm_num only [Nat.cast_ofNat] at h
    exact h.2
  have hE := R.cusp_three_source_edge_integral_pos hdk hW hgap hglobal hell
  have hz : 0 < z := R.cuspSourceRemainder_mass_pos i hE
  have hA : 0 < A := ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne'
    (measure_ne_top μ _)
  have hb : 0 < b := ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne'
    (measure_ne_top μ _)
  have hs : A + z = μ.real R.cuspSource := by
    have h := R.cuspSource_mass_decomposition i
    rwa [R.cuspSourcePeak_mass_original i hinside] at h
  have hT : T = b + A + z := by
    have h := R.singleton_height_eq_mass_add_source r hr
    change R.height = b + μ.real (S.reverseCompulsorySource {r}) at h
    have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
    rw [← hc, ← hs] at h
    exact h.trans (by ring)
  have hT0 : 0 < T := R.height_pos
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT0
  have hQ : 0 ≤ Q := tsum_nonneg (fun _ => sq_nonneg _)
  obtain ⟨hcut, hTlo, _⟩ := R.cusp_three_endpoint_bounds hdk hW hgap hglobal hell
  have hH := R.cuspEndpoint_missing_eq_whole r hW hd hgap hr
  rw [← R.cuspOutsideSquares_eq_whole r i] at hH
  have hcut' : T ^ 2 + Q < 25 / 144 := by linarith only [hcut, hH]
  obtain ⟨hba, _, hreserve⟩ :=
    R.cusp_three_source_peak_guards r i hdk hW hgap hglobal hr hinside hpeak
  change b < A at hba
  have hreserve' : δ / 9 < (2 - ell) * A ^ 2 := by
    convert hreserve using 1 <;> dsimp [δ, ell, A] <;> norm_num
  have hhole := R.cusp_source_original_hole_lower r i hW hd hgap hr hinside
  rw [hdk, ← hs] at hhole
  change b ^ 2 + 2 * b * (A + z) + A ^ 2 ≤ 1 - 2 * (4 / 9 : ℝ) at hhole
  have hhole' : T ^ 2 - z ^ 2 - 2 * A * z ≤ 1 / 9 := by
    rw [hT]
    nlinarith only [hhole]
  change 0 < A / T ∧ 0 < z / T ∧ A / T + z / T < 1 ∧ (1 - z / T) / 2 < A / T ∧
    (1 / 9 : ℝ) / T ^ 2 ∈ Ioo (16 / 25 : ℝ) 1 ∧
    ell ∈ Ico (1 : ℝ) (4 / 3) ∧ 0 ≤ Q / T ^ 2 ∧
    Q / T ^ 2 < (25 / 16) * ((1 / 9 : ℝ) / T ^ 2) - 1 ∧
    (4 / 3 + m) * ((1 / 9 : ℝ) / T ^ 2) < (2 + m) * (A / T) ^ 2 ∧
    1 - (z / T) ^ 2 - 2 * (A / T) * (z / T) ≤ (1 / 9 : ℝ) / T ^ 2
  refine ⟨div_pos hA hT0, div_pos hz hT0, ?_, ?_, ⟨?_, ?_⟩,
    ⟨hell, hellUpper⟩, div_nonneg hQ hT2.le, ?_, ?_, ?_⟩
  · rw [← add_div]
    exact (div_lt_one hT0).mpr (by linarith only [hT, hb])
  · have hx : A / T * T = A := div_mul_cancel₀ _ hT0.ne'
    have ht : z / T * T = z := div_mul_cancel₀ _ hT0.ne'
    apply (mul_lt_mul_iff_left₀ hT0).mp
    nlinarith only [hx, ht, hT, hba]
  · apply (lt_div_iff₀ hT2).mpr
    nlinarith only [hcut', hQ]
  · apply (div_lt_one hT2).mpr
    change 1 / 3 < T at hTlo
    nlinarith only [hTlo, hT0]
  · have he : (25 / 16 : ℝ) * ((1 / 9 : ℝ) / T ^ 2) - 1 =
        (25 / 144 - T ^ 2) / T ^ 2 := by field_simp; ring
    rw [he]
    exact (div_lt_div_iff_of_pos_right hT2).mpr (by linarith only [hcut'])
  · have hl : (4 / 3 + m) * ((1 / 9 : ℝ) / T ^ 2) = (δ / 9) / T ^ 2 := by
      dsimp [δ, ell]
      ring
    have hr : (2 + m) * (A / T) ^ 2 = ((2 - ell) * A ^ 2) / T ^ 2 := by
      dsimp [ell]
      ring
    rw [hl, hr]
    exact (div_lt_div_iff_of_pos_right hT2).mpr hreserve'
  · have he : 1 - (z / T) ^ 2 - 2 * (A / T) * (z / T) =
        (T ^ 2 - z ^ 2 - 2 * A * z) / T ^ 2 := by field_simp
    rw [he]
    exact (div_le_div_iff_of_pos_right hT2).mpr hhole'

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
