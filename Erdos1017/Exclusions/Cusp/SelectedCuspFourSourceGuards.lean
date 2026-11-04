module

public import Erdos1017.Exclusions.Cusp.SelectedCuspFourBounds
public import Erdos1017.Exclusions.Cusp.SelectedCuspSourcePeakGuards

/-!
# Scalar guards for the fourth-cusp source payment

The original missing inventory keeps the head and source-peak squares and both
orientations from the head to the entire source, and every scalar premise of the
fourth-cusp source payment is derived from the same original peak, source and
reverse endpoint.
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

/-- The original missing inventory retains the head square, source-peak
square, and both orientations from the original head to the entire source. -/
theorem cusp_source_original_hole_lower (R : S.ReverseRecovery) (r i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    (S.originalAtomMass r) ^ 2 + 2 * S.originalAtomMass r * μ.real R.cuspSource +
      (S.originalAtomMass i) ^ 2 ≤ 1 - 2 * d := by
  let P := {x | S.ρ x = r.val}
  let I := R.cuspSourcePeak i
  let J := R.cuspSourceRemainder i
  let B := P ∪ I
  let Z := (B ×ˢ B ∪ P ×ˢ J) ∪ J ×ˢ P
  have hP : MeasurableSet P := (S.hfibers r.val r.property).1
  have hI : MeasurableSet I := R.measurableSet_cuspSourcePeak i
  have hJ : MeasurableSet J := R.measurableSet_cuspSourceRemainder i
  have hB : MeasurableSet B := hP.union hI
  have hZ : MeasurableSet Z := ((hB.prod hB).union (hP.prod hJ)).union (hJ.prod hP)
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hc : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hc] at hg
  have hPI : Disjoint P I := hg.disjoint_IC.mono_right inter_subset_left
  have hPJ : Disjoint P J := hg.disjoint_IC.mono_right sdiff_subset
  have hIJ : Disjoint I J := R.cuspSource_disjoint_peak_remainder i
  have hBJ : Disjoint B J := hPJ.union_left hIJ
  have hdis₁ : Disjoint (B ×ˢ B) (P ×ˢ J) := Set.disjoint_left.mpr
    (fun _ hp hq => disjoint_left.mp hBJ hp.2 hq.2)
  have hdis₂ : Disjoint (B ×ˢ B ∪ P ×ˢ J) (J ×ˢ P) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hp.elim (fun h => disjoint_left.mp hBJ h.1 hq.1)
      (fun h => disjoint_left.mp hPJ h.1 hq.1)
  have hz : ∀ᵐ p ∂μ.prod μ, p ∈ Z → adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [hg.zero_II, hg.zero_IC, singleton_zero_II (S := S) i,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.zero_IC,
      adjacencyKernel_symm W] with p hpp hps hii hsp hsym hp
    rcases hp with (hp | hp) | hp
    · rcases hp.1 with hx | hx <;> rcases hp.2 with hy | hy
      · exact hpp hx hy
      · exact hps hx hy.1
      · exact hsym.trans (hsp hy hx.1)
      · exact hii hx.2 hy.2
    · exact hps hp.1 hp.2.1
    · exact hsym.trans (hsp hp.2 hp.1.1)
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using KernelOperator.integrable_kernel_bilinear
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hle : (μ.prod μ).real Z ≤ ∫ p, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
    calc
      _ = ∫ p, Z.indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ := by
        rw [integral_indicator hZ, setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ _ := integral_mono_ae ((integrable_const 1).indicator hZ)
        ((integrable_const 1).sub hG) (hz.mono (fun p hp => by
          change Z.indicator (fun _ => (1 : ℝ)) p ≤ 1 - adjacencyKernel W p.1 p.2
          by_cases hm : p ∈ Z
          · rw [indicator_of_mem hm, hp hm]
            norm_num
          · rw [indicator_of_notMem hm]
            exact sub_nonneg.mpr (adjacency_moment_mem W p).2))
  have hmass : (μ.prod μ).real Z =
      (S.originalAtomMass r + S.originalAtomMass i) ^ 2 +
        2 * S.originalAtomMass r * μ.real J := by
    rw [measureReal_union hdis₂ (hJ.prod hP), measureReal_union hdis₁ (hP.prod hJ),
      measureReal_prod_prod, measureReal_prod_prod, measureReal_prod_prod,
      measureReal_union hPI hI, R.cuspSourcePeak_mass_original i hinside]
    change (S.originalAtomMass r + S.originalAtomMass i) *
      (S.originalAtomMass r + S.originalAtomMass i) + S.originalAtomMass r * μ.real J +
      μ.real J * S.originalAtomMass r = _
    ring
  rw [hmass, integral_sub (integrable_const 1) hG] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  have hdensity := hW.density_eq
  change (∫ p, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 = d at hdensity
  have hs := R.cuspSource_mass_decomposition i
  rw [R.cuspSourcePeak_mass_original i hinside] at hs
  change S.originalAtomMass i + μ.real J = μ.real R.cuspSource at hs
  rw [← hs]
  nlinarith only [hle, hdensity]

/-- Every scalar premise of the fourth-cusp source payment is derived
from the same original peak, source, and actual reverse endpoint. -/
theorem cusp_four_source_normalized_guards (R : S.ReverseRecovery) (r i : S.I)
    (hdk : d = 15 / 32) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) :
    let X := S.originalAtomMass i / R.height
    let t := μ.real (R.cuspSourceRemainder i) / R.height
    let y := (1 / 16 : ℝ) / R.height ^ 2
    let ρ := (3 / 2 + m) / (-m - 1)
    let q := R.cuspOutsideSquares r i / R.height ^ 2
    0 < X ∧ 0 < t ∧ X + t < 1 ∧ (1 - t) / 2 < X ∧
      y ∈ Ioo (2 / 5 : ℝ) 1 ∧ ρ ∈ Ioo (0 : ℝ) 4 ∧ 0 ≤ q ∧
      q < ρ * (1 - y) ∧ q < (5 / 2) * y - 1 ∧
      ρ * y < (1 + 2 * ρ) * X ^ 2 ∧ 1 - t ^ 2 - 2 * X * t ≤ y := by
  let T := R.height
  let A := S.originalAtomMass i
  let b := S.originalAtomMass r
  let z := μ.real (R.cuspSourceRemainder i)
  let Q := R.cuspOutsideSquares r i
  let ell := -m
  let δ := 3 / 2 - ell
  have hdk' : d = (1 - 1 / (4 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  have hp := hW.cusp_contact_parameters 4 (by norm_num) hdk' hgap hglobal
  have hd := hp.1
  have hell : ell ∈ Ioo (11 / 10 : ℝ) (3 / 2) := by
    have h := hp.2.1
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hE := R.cusp_source_edge_integral_pos 4 (by norm_num) hdk' hW hgap hglobal
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
  obtain ⟨hcut, hTlo, _⟩ := R.cusp_four_endpoint_bounds hdk hW hgap hglobal
  have hH := R.cuspEndpoint_missing_eq_whole r hW hd hgap hr
  rw [← R.cuspOutsideSquares_eq_whole r i] at hH
  have hcut' : T ^ 2 + Q < 5 / 32 := by linarith only [hcut, hH]
  obtain ⟨hba, _, hreserve⟩ :=
    R.cusp_source_peak_guards r i 4 (by norm_num) hdk' hW hgap hglobal hr hinside hpeak
  change b < A at hba
  have hreserve' : δ / 16 < (2 - ell) * A ^ 2 := by
    convert hreserve using 1 <;> dsimp [δ, ell, A] <;> norm_num
  have hhole := R.cusp_source_original_hole_lower r i hW hd hgap hr hinside
  rw [hdk, ← hs] at hhole
  change b ^ 2 + 2 * b * (A + z) + A ^ 2 ≤ 1 - 2 * (15 / 32 : ℝ) at hhole
  have hhole' : T ^ 2 - z ^ 2 - 2 * A * z ≤ 1 / 16 := by
    rw [hT]
    nlinarith only [hhole]
  have hbudget := R.cusp_source_budget_lt r i 4 (by norm_num) hdk' hW hgap hglobal hr hinside
  have hcI := R.cuspPeakCredit_nonnegative hW hd hgap r i hr hinside
  have hCJ := R.cuspRemainderCredit_nonnegative hW hd hgap r i hr
  have hPhi := R.cuspCrossEnergy_nonnegative hW i
  have hF := R.cuspRemainderEnergy_nonnegative hW i
  have hbudget' : (ell - 1) * Q < δ * (T ^ 2 - 1 / 16) := by
    norm_num only [Nat.cast_ofNat] at hbudget
    change A * R.cuspPeakCredit r i + R.cuspRemainderCredit r i +
      A * R.cuspCrossEnergy i + R.cuspRemainderEnergy i / 2 <
      (3 / 2 + m) * (T ^ 2 - 1 / 16) / 2 - (-m - 1) * Q / 2 at hbudget
    dsimp [δ, ell]
    nlinarith only [hbudget, hCJ, hF, mul_nonneg hA.le hcI, mul_nonneg hA.le hPhi]
  have hden : 0 < ell - 1 := by linarith only [hell.1]
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hell.2]
  have hδeq : δ = 3 / 2 + m := by dsimp [δ, ell]; ring
  dsimp only
  rw [← hδeq]
  change 0 < A / T ∧ 0 < z / T ∧ A / T + z / T < 1 ∧ (1 - z / T) / 2 < A / T ∧
    (1 / 16 : ℝ) / T ^ 2 ∈ Ioo (2 / 5 : ℝ) 1 ∧
    δ / (ell - 1) ∈ Ioo (0 : ℝ) 4 ∧ 0 ≤ Q / T ^ 2 ∧
    Q / T ^ 2 < δ / (ell - 1) * (1 - (1 / 16 : ℝ) / T ^ 2) ∧
    Q / T ^ 2 < (5 / 2) * ((1 / 16 : ℝ) / T ^ 2) - 1 ∧
    δ / (ell - 1) * ((1 / 16 : ℝ) / T ^ 2) <
      (1 + 2 * (δ / (ell - 1))) * (A / T) ^ 2 ∧
    1 - (z / T) ^ 2 - 2 * (A / T) * (z / T) ≤ (1 / 16 : ℝ) / T ^ 2
  refine ⟨div_pos hA hT0, div_pos hz hT0, ?_, ?_, ⟨?_, ?_⟩,
    ⟨div_pos hδ hden, ?_⟩, div_nonneg hQ hT2.le, ?_, ?_, ?_, ?_⟩
  · rw [← add_div]
    exact (div_lt_one hT0).mpr (by linarith only [hT, hb])
  · have hx : A / T * T = A := div_mul_cancel₀ _ hT0.ne'
    have ht : z / T * T = z := div_mul_cancel₀ _ hT0.ne'
    apply (mul_lt_mul_iff_left₀ hT0).mp
    nlinarith only [hx, ht, hT, hba]
  · apply (lt_div_iff₀ hT2).mpr
    nlinarith only [hcut', hQ]
  · apply (div_lt_one hT2).mpr
    change 1 / 4 < T at hTlo
    nlinarith only [hTlo, hT0]
  · apply (div_lt_iff₀ hden).mpr
    dsimp [δ]
    linarith only [hell.1]
  · have he : δ / (ell - 1) * (1 - (1 / 16 : ℝ) / T ^ 2) =
        (δ * (T ^ 2 - 1 / 16) / (ell - 1)) / T ^ 2 := by field_simp
    rw [he]
    apply (div_lt_div_iff_of_pos_right hT2).mpr
    exact (lt_div_iff₀ hden).mpr (by nlinarith only [hbudget'])
  · have he : (5 / 2 : ℝ) * ((1 / 16 : ℝ) / T ^ 2) - 1 =
        (5 / 32 - T ^ 2) / T ^ 2 := by field_simp; ring
    rw [he]
    exact (div_lt_div_iff_of_pos_right hT2).mpr (by linarith only [hcut'])
  · have hl : δ / (ell - 1) * ((1 / 16 : ℝ) / T ^ 2) =
        (δ / 16) / ((ell - 1) * T ^ 2) := by field_simp
    have hr : (1 + 2 * (δ / (ell - 1))) * (A / T) ^ 2 =
        ((2 - ell) * A ^ 2) / ((ell - 1) * T ^ 2) := by
      dsimp [δ]
      field_simp
      ring
    rw [hl, hr]
    exact (div_lt_div_iff_of_pos_right (mul_pos hden hT2)).mpr hreserve'
  · have he : 1 - (z / T) ^ 2 - 2 * (A / T) * (z / T) =
        (T ^ 2 - z ^ 2 - 2 * A * z) / T ^ 2 := by field_simp
    rw [he]
    exact (div_le_div_iff_of_pos_right hT2).mpr hhole'

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
