module

public import Erdos1017.Exclusions.Common.Covered.CoveredTwoExteriorBlockMoments
public import Erdos1017.Exclusions.Common.Covered.FullCoveredCopyVariation

/-!
# Own rows and copy margins of the two-exterior model

Every positive block of a `FullStationaryClass` model obeys its own stationary
row with a strictly positive adjusted intercept, and the `C1`-`E`, `C2`-`E` and
`E`-`E` pair copies obey the model's own margin, with the sign-feasible table
supplying the covered-copy hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical BigOperators

namespace Erdos1017.CoveredTwoExterior

private theorem integral_labels {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (label : Ω → Fin 5) (hlabel : Measurable label) (f : Fin 5 → ℝ) :
    (∫ z, f (label z) ∂μ) = ∑ i, μ.real (label ⁻¹' {i}) * f i := by
  have he : (fun z => f (label z)) =
      fun z => ∑ i, (label ⁻¹' {i}).indicator (fun _ => f i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hlabel (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hlabel (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

private theorem own_row_sum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : CappedModel.Model Ω μ}
    {d c m : ℝ} (hW : CappedModel.FullStationaryClass d c W m)
    (x : VertexClassification.Coefficients) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpos : ∀ i, 0 < μ (label ⁻¹' {i}))
    (hA : ∀ z w, CappedModel.adjacencyKernel W z w =
      if blockAdjacency (label z) (label w) = true then 1 else 0)
    (hY : ∀ z w, CappedModel.chargeKernel W z w = blockCharge x (label z) (label w))
    (i : Fin 5) :
    (∑ j, μ.real (label ⁻¹' {j}) *
      (blockCharge x i j - m * (if blockAdjacency i j = true then 1 else 0))) =
        2 * (c - m * d) := by
  obtain ⟨z, hz, hflat⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (hpos i).ne'
    (ae_restrict_of_ae hW.stationary)
  have he : (∫ w, CappedModel.shiftedKernel W m z w ∂μ) =
      ∫ w, blockCharge x i (label w) -
        m * (if blockAdjacency i (label w) = true then 1 else 0) ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun w => by
      change CappedModel.shiftedMoment W m (z, w) = _
      rw [CappedModel.shiftedMoment_eq]
      change CappedModel.chargeKernel W z w - m * CappedModel.adjacencyKernel W z w = _
      rw [hY, hA, show label z = i from hz])
  rw [he, integral_labels (μ := μ) label hlabel (fun j => blockCharge x i j -
    m * (if blockAdjacency i j = true then 1 else 0))] at hflat
  exact hflat

private theorem own_copy_row_bound {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    {W : CappedModel.Model Ω μ} {d c m : ℝ}
    (hW : CappedModel.FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (x : VertexClassification.Coefficients) (hx : x ∈ VertexClassification.feasible)
    (label : Ω → Fin 5) (hlabel : Measurable label) (hpos : ∀ i, 0 < μ (label ⁻¹' {i}))
    (hA : ∀ z w, CappedModel.adjacencyKernel W z w =
      if blockAdjacency (label z) (label w) = true then 1 else 0)
    (hY : ∀ z w, CappedModel.chargeKernel W z w = blockCharge x (label z) (label w))
    (i j : Fin 5) (hi : i ≠ 1) (hj : j ≠ 1) (hij : blockAdjacency i j = true) :
    (∫ z, IndependentAtomCopy.rowCharge blockAdjacency (blockCharge x) {1}
      i j (label z) ∂μ) -
        m * (∫ z, IndependentAtomCopy.rowAdjacency blockAdjacency i j (label z) ∂μ) ≤
          2 * (c - m * d) := by
  let I := label ⁻¹' {(1 : Fin 5)}
  let G := CappedModel.PhysicalRepresentative.adjacency W m
  let Y := CappedModel.PhysicalRepresentative.charge W m
  have hI : MeasurableSet I := hlabel (measurableSet_singleton 1)
  have hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I →
      CappedModel.adjacencyKernel W p.1 p.2 = 0 := by
    exact Eventually.of_forall (fun p hp hq => by
      rw [hA]
      simp [I] at hp hq
      simp [hp, hq, blockAdjacency])
  have hsign (a b : Fin 5) (ha : a ≠ 1) (hb : b ≠ 1) : blockCharge x a b ≤ 0 := by
    fin_cases a <;> fin_cases b <;> simp_all [blockCharge]
    all_goals linarith [hx.1 3, hx.1 4, hx.1 5, hx.1 6]
  have hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ I → p.2 ∉ I →
      CappedModel.chargeKernel W p.1 p.2 ≤ 0 := by
    exact Eventually.of_forall (fun p hp hq => by
      rw [hY]
      exact hsign _ _ hp hq)
  have hcopy := hW.ae_covered_copy_shifted_row_le_stationary hd hgap I hI hind hbody
  have hstructure := hW.strict_gap_structure hd hgap
  have hG : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = blockAdjacency (label p.1) (label p.2) := by
    filter_upwards [CappedModel.PhysicalRepresentative.adjacency_moment_ae_eq W m
      hstructure.strict_support] with p hp
    have he := hp.symm.trans (hA p.1 p.2)
    change (if G p.1 p.2 = true then (1 : ℝ) else 0) =
      (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) at he
    cases hg : G p.1 p.2 <;> cases hb : blockAdjacency (label p.1) (label p.2) <;> simp_all
  have hcharge : ∀ᵐ p ∂μ.prod μ, Y p.1 p.2 = blockCharge x (label p.1) (label p.2) := by
    filter_upwards [CappedModel.PhysicalRepresentative.charge_ae_eq W m
      hstructure.strict_support] with p hp
    exact hp.trans (hY p.1 p.2)
  have hrows := Measure.ae_ae_of_ae_prod (hG.and hcharge)
  have hall : ∀ᵐ p ∂μ.prod μ, label p.1 = i → label p.2 = j →
      (∫ z, IndependentAtomCopy.rowCharge blockAdjacency (blockCharge x) {1}
        i j (label z) ∂μ) -
          m * (∫ z, IndependentAtomCopy.rowAdjacency blockAdjacency i j (label z) ∂μ) ≤
            2 * (c - m * d) := by
    filter_upwards [hcopy, hG, hcharge, Measure.quasiMeasurePreserving_fst.ae hrows,
      Measure.quasiMeasurePreserving_snd.ae hrows] with p hp hg hy hpx hpy hpi hpj
    have htrue : G p.1 p.2 = true := by simpa [hpi, hpj, hij] using hg
    have hbound := hp (by simpa [I, hpi] using hi) (by simpa [I, hpj] using hj) htrue
    have hyrow : IndependentAtomCopy.rowCharge G Y I p.1 p.2 =ᵐ[μ]
        fun z => IndependentAtomCopy.rowCharge blockAdjacency (blockCharge x) {1}
          i j (label z) := by
      filter_upwards [hpx, hpy] with z hz hw
      simp only [IndependentAtomCopy.rowCharge, hz.1, hw.1, hz.2, hw.2, hy, hpi, hpj]
      simp [I, Set.indicator_apply]
    have harow : IndependentAtomCopy.rowAdjacency G p.1 p.2 =ᵐ[μ]
        fun z => IndependentAtomCopy.rowAdjacency blockAdjacency i j (label z) := by
      filter_upwards [hpx, hpy] with z hz hw
      simp only [IndependentAtomCopy.rowAdjacency, hz.1, hw.1, hpi, hpj]
    rw [integral_congr_ae hyrow, integral_congr_ae harow] at hbound
    exact hbound
  have hrect : 0 < (μ.prod μ) ((label ⁻¹' {i}) ×ˢ (label ⁻¹' {j})) := by
    rw [Measure.prod_prod]
    exact pos_iff_ne_zero.mpr (mul_ne_zero (hpos i).ne' (hpos j).ne')
  obtain ⟨p, hp, he⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hrect.ne'
    (ae_restrict_of_ae hall)
  exact he hp.1 hp.2

end Erdos1017.CoveredTwoExterior

namespace Erdos1017.CappedModel

open CoveredTwoExterior

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Every positive original block obeys the same supplied model's own
stationary row. The adjusted intercept is derived to be strictly positive. -/
theorem FullStationaryClass.coveredTwoExterior_own_rows
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (x : VertexClassification.Coefficients) (label : Ω → Fin 5) (hlabel : Measurable label)
    (hpos : ∀ i, 0 < μ (label ⁻¹' {i}))
    (hA : ∀ z w, adjacencyKernel W z w =
      if blockAdjacency (label z) (label w) = true then 1 else 0)
    (hY : ∀ z w, chargeKernel W z w = blockCharge x (label z) (label w)) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let c1 := μ.real (label ⁻¹' {2})
    let c2 := μ.real (label ⁻¹' {3})
    let e := μ.real (label ⁻¹' {4})
    let ν := 2 * (c - m * d)
    let γ := ν + m - m * a
    ν = (1 - m) * b ∧
      ν = a + c1 * x 0 + c2 * x 1 + e * x 2 - m * (1 - b) ∧
      ν = b * x 0 - c2 * x 3 - e * x 4 - m * (1 - a - c1) ∧
      ν = b * x 1 - c1 * x 3 - e * x 5 - m * (1 - a - c2) ∧
      γ = b * x 2 - c1 * x 4 - c2 * x 5 - e * x 6 ∧ 0 < γ := by
  have hrows := CoveredTwoExterior.own_row_sum hW x label hlabel hpos hA hY
  have hmass : μ.real (label ⁻¹' {0}) + μ.real (label ⁻¹' {1}) +
      μ.real (label ⁻¹' {2}) + μ.real (label ⁻¹' {3}) + μ.real (label ⁻¹' {4}) = 1 := by
    have h := CoveredTwoExterior.integral_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, add_assoc] using h.symm
  have hmassm := congrArg (fun z : ℝ => m * z) hmass
  have h0 := hrows 0
  have h1 := hrows 1
  have h2 := hrows 2
  have h3 := hrows 3
  have h4 := hrows 4
  simp [blockCharge, blockAdjacency, Fin.sum_univ_succ] at h0 h1 h2 h3 h4
  have hs := hW.strict_gap_structure hd hgap
  have hγ : 0 < 2 * (c - m * d) + m - m * μ.real (label ⁻¹' {0}) := by
    have hm := mul_nonpos_of_nonpos_of_nonneg hs.multiplier_neg.le
      (measureReal_nonneg (μ := μ) (s := label ⁻¹' {0}))
    linarith [hs.gamma_pos]
  exact ⟨by nlinarith only [h0], by nlinarith only [h1, hmassm],
    by nlinarith only [h2, hmassm], by nlinarith only [h3, hmassm],
    by nlinarith only [h4, hmassm], hγ⟩

/-- Actual C1–E, C2–E and E–E pair copies obey the original model's own
margin. The sign-feasible table supplies the covered-copy hypotheses. -/
theorem FullStationaryClass.coveredTwoExterior_copy_margins
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (x : VertexClassification.Coefficients) (hx : x ∈ VertexClassification.feasible)
    (label : Ω → Fin 5) (hlabel : Measurable label) (hpos : ∀ i, 0 < μ (label ⁻¹' {i}))
    (hA : ∀ z w, adjacencyKernel W z w =
      if blockAdjacency (label z) (label w) = true then 1 else 0)
    (hY : ∀ z w, chargeKernel W z w = blockCharge x (label z) (label w)) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let c1 := μ.real (label ⁻¹' {2})
    let c2 := μ.real (label ⁻¹' {3})
    let γ := 2 * (c - m * d) + m - m * a
    0 < γ ∧ γ ≤ (b - c1) * x 4 ∧ γ ≤ (b - c2) * x 5 ∧ γ ≤ b * x 6 := by
  obtain ⟨_, _, hC1, hC2, hE, hγ⟩ :=
    hW.coveredTwoExterior_own_rows hd hgap x label hlabel hpos hA hY
  have hfirst := CoveredTwoExterior.own_copy_row_bound hW hd hgap x hx label hlabel hpos
    hA hY 2 4 (by decide) (by decide) (by rfl)
  have hsecond := CoveredTwoExterior.own_copy_row_bound hW hd hgap x hx label hlabel hpos
    hA hY 3 4 (by decide) (by decide) (by rfl)
  have hthird := CoveredTwoExterior.own_copy_row_bound hW hd hgap x hx label hlabel hpos
    hA hY 4 4 (by decide) (by decide) (by rfl)
  rw [CoveredTwoExterior.integral_labels (μ := μ) label hlabel
    (IndependentAtomCopy.rowCharge blockAdjacency (blockCharge x) {1} 2 4),
    CoveredTwoExterior.integral_labels (μ := μ) label hlabel
      (IndependentAtomCopy.rowAdjacency blockAdjacency 2 4)] at hfirst
  rw [CoveredTwoExterior.integral_labels (μ := μ) label hlabel
    (IndependentAtomCopy.rowCharge blockAdjacency (blockCharge x) {1} 3 4),
    CoveredTwoExterior.integral_labels (μ := μ) label hlabel
      (IndependentAtomCopy.rowAdjacency blockAdjacency 3 4)] at hsecond
  rw [CoveredTwoExterior.integral_labels (μ := μ) label hlabel
    (IndependentAtomCopy.rowCharge blockAdjacency (blockCharge x) {1} 4 4),
    CoveredTwoExterior.integral_labels (μ := μ) label hlabel
      (IndependentAtomCopy.rowAdjacency blockAdjacency 4 4)] at hthird
  simp [IndependentAtomCopy.rowCharge, IndependentAtomCopy.rowAdjacency,
    blockCharge, blockAdjacency, Fin.sum_univ_succ] at hfirst hsecond hthird
  have hmass : μ.real (label ⁻¹' {0}) + μ.real (label ⁻¹' {1}) +
      μ.real (label ⁻¹' {2}) + μ.real (label ⁻¹' {3}) + μ.real (label ⁻¹' {4}) = 1 := by
    have h := CoveredTwoExterior.integral_labels (μ := μ) label hlabel (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, add_assoc] using h.symm
  have hmassm := congrArg (fun z : ℝ => m * z) hmass
  exact ⟨hγ, by nlinarith only [hfirst, hC1, hE, hmassm],
    by nlinarith only [hsecond, hC2, hE, hmassm],
    by nlinarith only [hthird, hE, hmassm]⟩

end Erdos1017.CappedModel
