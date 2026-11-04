module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceChild
public import Erdos1017.Exclusions.Cusp.CuspWholeSourceChildAccounting

/-!
# Adjacency rows of the partial cusp endpoint

Exact current adjacency masses of the partial endpoint: the cross-block masses
of the remainder against the peak and against itself (with deficit `qJ`), and
the rows of the retained head, the original peak and the remainder.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open WholeSourceChild KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

private theorem row_of_missing_block {ν : Measure Ω} [IsProbabilityMeasure ν]
    (G : Ω → Ω → ℝ) (hG : AEStronglyMeasurable (Function.uncurry G) (ν.prod ν))
    (hbound : ∀ᵐ p ∂ν.prod ν, ‖G p.1 p.2‖ ≤ 1)
    (C P D : Set Ω) (hC : MeasurableSet C) (hP : MeasurableSet P) (hD : MeasurableSet D)
    (he : ∀ᵐ p ∂ν.prod ν, p.1 ∈ C → G p.1 p.2 =
      1 - P.indicator (fun _ => 1) p.2 - D.indicator (fun _ => 1) p.2 * (1 - G p.1 p.2)) :
    rowIntegral ν G C = ν.real C * (1 - ν.real P) -
      crossIntegral ν (fun x y => 1 - G x y) C D := by
  let f := C.indicator (fun _ => (1 : ℝ))
  let g := P.indicator (fun _ => (1 : ℝ))
  let h := D.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f ν := (integrable_const 1).indicator hC
  have hg : Integrable g ν := (integrable_const 1).indicator hP
  have hh : Integrable h ν := (integrable_const 1).indicator hD
  have hb : ∀ᵐ p ∂ν.prod ν, ‖1 - G p.1 p.2‖ ≤ 2 := by
    filter_upwards [hbound] with p hp
    calc
      ‖1 - G p.1 p.2‖ ≤ ‖(1 : ℝ)‖ + ‖G p.1 p.2‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num at *; linarith
  have heq : (fun p : Ω × Ω => G p.1 p.2 * 1 * f p.1) =ᵐ[ν.prod ν]
      fun p => f p.1 * 1 - f p.1 * g p.2 - (1 - G p.1 p.2) * h p.2 * f p.1 := by
    filter_upwards [he] with p hp
    by_cases hc : p.1 ∈ C
    · have hv := hp hc
      dsimp [f, g, h]
      rw [indicator_of_mem hc]
      linear_combination hv
    · simp only [f, indicator_of_notMem hc, mul_zero, zero_mul, sub_self]
  have hi : Integrable (fun p : Ω × Ω => (1 - G p.1 p.2) * h p.2 * f p.1) (ν.prod ν) :=
    integrable_kernel_bilinear (K := fun x y => 1 - G x y)
      (aestronglyMeasurable_const.sub hG) hb hh hf
  have hs₁ : (∫ p : Ω × Ω, f p.1 * 1 - f p.1 * g p.2 -
      (1 - G p.1 p.2) * h p.2 * f p.1 ∂ν.prod ν) =
      (∫ p : Ω × Ω, f p.1 * 1 - f p.1 * g p.2 ∂ν.prod ν) -
        ∫ p : Ω × Ω, (1 - G p.1 p.2) * h p.2 * f p.1 ∂ν.prod ν :=
    integral_sub ((hf.mul_prod (integrable_const 1)).sub (hf.mul_prod hg)) hi
  have hs₂ : (∫ p : Ω × Ω, f p.1 * 1 - f p.1 * g p.2 ∂ν.prod ν) =
      (∫ p : Ω × Ω, f p.1 * 1 ∂ν.prod ν) - ∫ p : Ω × Ω, f p.1 * g p.2 ∂ν.prod ν :=
    integral_sub (hf.mul_prod (integrable_const 1)) (hf.mul_prod hg)
  have hs₃ : (∫ p : Ω × Ω, f p.1 * 1 ∂ν.prod ν) =
      (∫ x, f x ∂ν) * ∫ _ : Ω, (1 : ℝ) ∂ν := integral_prod_mul f (fun _ : Ω => (1 : ℝ))
  rw [← pairing_one_indicator G hG hbound C hC, kernelPairing,
    integral_congr_ae heq, hs₁, hs₂, hs₃, integral_prod_mul]
  have hint (T : Set Ω) (hT : MeasurableSet T) :
      (∫ x, T.indicator (fun _ => (1 : ℝ)) x ∂ν) = ν.real T := by
    rw [integral_indicator hT, setIntegral_const, smul_eq_mul, mul_one]
  change (∫ x, f x ∂ν) * (∫ _ : Ω, (1 : ℝ) ∂ν) - (∫ x, f x ∂ν) * (∫ x, g x ∂ν) -
    kernelPairing (μ := ν) (fun x y => 1 - G x y) h f = _
  rw [show (∫ x, f x ∂ν) = ν.real C from hint C hC,
    show (∫ x, g x ∂ν) = ν.real P from hint P hP,
    pairing_indicator _ C D hC hD]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

private theorem row_of_missing_set {ν : Measure Ω} [IsProbabilityMeasure ν]
    (G : Ω → Ω → ℝ) (hG : AEStronglyMeasurable (Function.uncurry G) (ν.prod ν))
    (hbound : ∀ᵐ p ∂ν.prod ν, ‖G p.1 p.2‖ ≤ 1)
    (C P : Set Ω) (hC : MeasurableSet C) (hP : MeasurableSet P)
    (he : ∀ᵐ p ∂ν.prod ν, p.1 ∈ C → G p.1 p.2 = 1 - P.indicator (fun _ => 1) p.2) :
    rowIntegral ν G C = ν.real C * (1 - ν.real P) := by
  have h := row_of_missing_block G hG hbound C P ∅ hC hP MeasurableSet.empty
    (he.mono (fun p hp hx => by simpa only [indicator_empty, Pi.zero_apply, zero_mul, sub_zero] using hp hx))
  simpa only [crossIntegral, prod_empty, Measure.restrict_empty, integral_zero_measure, sub_zero] using h

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

private theorem adjacency_rows_event (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    ∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      (S.ρ p.1 = r.val → adjacencyKernel W p.1 p.2 =
        1 - ({x | S.ρ x = r.val} ∪ R.cuspSource).indicator (fun _ => 1) p.2) ∧
      (p.1 ∈ R.cuspSourcePeak i → adjacencyKernel W p.1 p.2 =
        1 - ({x | S.ρ x = r.val} ∪ R.cuspSourcePeak i).indicator (fun _ => 1) p.2) ∧
      (p.1 ∈ R.cuspSourceRemainder i → adjacencyKernel W p.1 p.2 =
        1 - {x | S.ρ x = r.val}.indicator (fun _ => 1) p.2 -
          (R.cuspSourceRemainder i).indicator (fun _ => 1) p.2 * (1 - adjacencyKernel W p.1 p.2)) := by
  let := R.cuspPartialLaw_probability
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  have hg := R.cuspPartialLaw_child_graph r i hW hd hgap hr
  have ho := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hSource : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  rw [← hSource] at ho
  filter_upwards [hg.1, hg.2.1, hg.2.2.1, hac.ae_le ho.zero_II,
    hac.ae_le ho.zero_IC, hac.ae_le ho.joined_IO,
    hac.ae_le (Measure.measurePreserving_swap.quasiMeasurePreserving.ae ho.zero_IC),
    hac.ae_le (adjacencyKernel_symm W),
    Measure.quasiMeasurePreserving_snd.ae (R.cuspPartialLaw_ae_partition r hr)]
    with p hb hj hblock hPP hPS hPO hSP hsym hpart
  have hPnotS (x : Ω) (hx : S.ρ x = r.val) : x ∉ R.cuspSource :=
    fun hs => disjoint_left.mp ho.disjoint_IC hx hs
  have hSnotP (x : Ω) (hx : x ∈ R.cuspSource) : S.ρ x ≠ r.val :=
    fun hp => hPnotS x hp hx
  have hvalue (v : Bool) (hv : PhysicalRepresentative.adjacency W m p.1 p.2 = v) :
      adjacencyKernel W p.1 p.2 = if v = true then 1 else 0 := by
    change adjacencyKernel W p.1 p.2 = _ at hb
    rw [hv] at hb
    exact hb
  refine ⟨?_, ?_, ?_⟩
  · intro hx
    by_cases hy : p.2 ∈ {x | S.ρ x = r.val} ∪ R.cuspSource
    · rw [indicator_of_mem hy]
      rcases hy with hy | hy
      · rw [hPP hx hy]; norm_num
      · rw [hPS hx hy]; norm_num
    · rw [indicator_of_notMem hy]
      have hO : p.2 ∈ singletonOther (S := S) r := hpart.elim (fun h => False.elim (hy h)) id
      rw [hPO hx hO]; norm_num
  · intro hx
    by_cases hyP : S.ρ p.2 = r.val
    · rw [indicator_of_mem (show p.2 ∈ {x | S.ρ x = r.val} ∪ R.cuspSourcePeak i from Or.inl hyP)]
      rw [hsym.trans (hSP hyP hx.1)]; norm_num
    · have hnJ : p.1 ∉ R.cuspSourceRemainder i :=
        fun h => disjoint_left.mp (R.cuspSource_disjoint_peak_remainder i) hx h
      have hA := hblock (hSnotP _ hx.1) hyP (Or.inl hnJ)
      by_cases hyI : p.2 ∈ R.cuspSourcePeak i
      · have hv : PhysicalRepresentative.adjacency W m p.1 p.2 = false := by
          simpa only [WholeSourceChild.outsideAdjacency, hx, hyI, and_self, ↓reduceIte] using hA
        rw [hvalue false hv, indicator_of_mem (show p.2 ∈ {x | S.ρ x = r.val} ∪ R.cuspSourcePeak i from Or.inr hyI)]
        norm_num
      · have hv : PhysicalRepresentative.adjacency W m p.1 p.2 = true := by
          simpa only [WholeSourceChild.outsideAdjacency, hx, hyI, and_false, ↓reduceIte, true_or] using hA
        rw [hvalue true hv, indicator_of_notMem (show p.2 ∉ {x | S.ρ x = r.val} ∪ R.cuspSourcePeak i from
          fun h => h.elim hyP hyI)]
        norm_num
  · intro hx
    by_cases hyP : S.ρ p.2 = r.val
    · have hnJ : p.2 ∉ R.cuspSourceRemainder i := fun h => hSnotP _ h.1 hyP
      have hz : adjacencyKernel W p.1 p.2 = 0 := hsym.trans (hSP hyP hx.1)
      rw [indicator_of_mem (show p.2 ∈ {x | S.ρ x = r.val} from hyP), indicator_of_notMem hnJ, hz]
      norm_num
    · rw [indicator_of_notMem (show p.2 ∉ {x | S.ρ x = r.val} from hyP)]
      by_cases hyJ : p.2 ∈ R.cuspSourceRemainder i
      · rw [indicator_of_mem hyJ]
        ring
      · rw [indicator_of_notMem hyJ, hvalue true (hj hx hyJ hyP).1]
        norm_num

/-- The unchanged source restrictions and genuine J–I join give its exact
current cross-block adjacency mass. -/
theorem cuspPartial_adjacency_cross_remainder_peak (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    crossIntegral R.cuspPartialLaw (adjacencyKernel W)
      (R.cuspSourceRemainder i) (R.cuspSourcePeak i) =
        S.originalAtomMass i * μ.real (R.cuspSourceRemainder i) := by
  let := R.cuspPartialLaw_probability
  have hg := R.cuspPartialLaw_child_graph r i hW hd hgap hr
  have hgeom := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hj : ∀ᵐ p ∂R.cuspPartialLaw.prod R.cuspPartialLaw,
      p.1 ∈ R.cuspSourceRemainder i → p.2 ∈ R.cuspSourcePeak i → adjacencyKernel W p.1 p.2 = 1 := by
    filter_upwards [hg.1, hg.2.1] with p hb hp hx hy
    have hnJ : p.2 ∉ R.cuspSourceRemainder i :=
      fun h => disjoint_left.mp (R.cuspSource_disjoint_peak_remainder i) hy h
    have hnP : S.ρ p.2 ≠ r.val := by
      intro he
      apply disjoint_left.mp hgeom.disjoint_IC he
      simpa only [cuspSource, hr] using hy.1
    have he := (hp hx hnJ hnP).1
    rw [ite_eq_left he] at hb
    exact hb
  rw [crossIntegral]
  have he : (∫ p in (R.cuspSourceRemainder i) ×ˢ (R.cuspSourcePeak i),
      adjacencyKernel W p.1 p.2 ∂R.cuspPartialLaw.prod R.cuspPartialLaw) =
      ∫ _p in (R.cuspSourceRemainder i) ×ˢ (R.cuspSourcePeak i), (1 : ℝ)
        ∂R.cuspPartialLaw.prod R.cuspPartialLaw := by
    apply integral_congr_ae
    apply (ae_restrict_iff' ((R.measurableSet_cuspSourceRemainder i).prod
      (R.measurableSet_cuspSourcePeak i))).mpr
    exact hj.mono (fun _ hp hx => hp hx.1 hx.2)
  rw [he, setIntegral_const, smul_eq_mul, mul_one, measureReal_prod_prod,
    R.cuspPartialLaw_mass_remainder i, R.cuspPartialLaw_mass_peak i hinside]
  ring

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The literal qJ is the missing mass of the actual current J-square. -/
theorem cuspPartial_adjacency_cross_remainder_remainder (R : S.ReverseRecovery) (i : S.I) :
    crossIntegral R.cuspPartialLaw (adjacencyKernel W)
      (R.cuspSourceRemainder i) (R.cuspSourceRemainder i) =
        (μ.real (R.cuspSourceRemainder i)) ^ 2 - R.cuspRemainderMissing i := by
  let := R.cuspPartialLaw_probability
  let J := R.cuspSourceRemainder i
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2)
      (R.cuspPartialLaw.prod R.cuspPartialLaw) := by
    simpa only [mul_one] using integrable_kernel_bilinear
      ((adjacencyKernel_measurable W).mono_ac hac) (hac.ae_le (adjacencyKernel_bound W))
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hq : R.cuspRemainderMissing i = ∫ p in J ×ˢ J, 1 - adjacencyKernel W p.1 p.2
      ∂R.cuspPartialLaw.prod R.cuspPartialLaw := by
    rw [← Measure.prod_restrict, R.cuspPartialLaw_restrict_remainder i, Measure.prod_restrict]
    rfl
  rw [hq, integral_sub (integrable_const 1).integrableOn hG.integrableOn,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_prod_prod,
    R.cuspPartialLaw_mass_remainder i]
  unfold crossIntegral
  dsimp only [J]
  ring

/-- The retained head misses precisely itself and the entire source. -/
theorem cuspPartial_adjacency_row_head (R : S.ReverseRecovery) (r : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    rowIntegral R.cuspPartialLaw (adjacencyKernel W) {x | S.ρ x = r.val} =
      S.originalAtomMass r * (1 - (S.originalAtomMass r + μ.real R.cuspSource)) := by
  let := R.cuspPartialLaw_probability
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  have he := R.adjacency_rows_event r r hW hd hgap hr
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hdis : Disjoint {x | S.ρ x = r.val} R.cuspSource := by
    simpa only [cuspSource, hr] using hg.disjoint_IC
  rw [row_of_missing_set (adjacencyKernel W) ((adjacencyKernel_measurable W).mono_ac hac)
    (hac.ae_le (adjacencyKernel_bound W)) _ _ (S.hfibers r.val r.property).1
    ((S.hfibers r.val r.property).1.union R.measurableSet_source)
    (he.mono (fun _ hp => hp.1))]
  change R.cuspPartialLaw.real {x | S.ρ x = r.val} *
    (1 - R.cuspPartialLaw.real ({x | S.ρ x = r.val} ∪ R.cuspSource)) = _
  rw [measureReal_union hdis R.measurableSet_source,
    R.cuspPartialLaw_mass_head r hW hr, R.cuspPartialLaw_mass_source]

/-- The retained original peak misses precisely itself and the old head. -/
theorem cuspPartial_adjacency_row_peak (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    rowIntegral R.cuspPartialLaw (adjacencyKernel W) (R.cuspSourcePeak i) =
      S.originalAtomMass i * (1 - S.originalAtomMass r - S.originalAtomMass i) := by
  let := R.cuspPartialLaw_probability
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  have he := R.adjacency_rows_event r i hW hd hgap hr
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hdis : Disjoint {x | S.ρ x = r.val} (R.cuspSourcePeak i) := by
    have hPS : Disjoint {x | S.ρ x = r.val} R.cuspSource := by
      simpa only [cuspSource, hr] using hg.disjoint_IC
    exact hPS.mono_right inter_subset_left
  rw [row_of_missing_set (adjacencyKernel W) ((adjacencyKernel_measurable W).mono_ac hac)
    (hac.ae_le (adjacencyKernel_bound W)) _ _ (R.measurableSet_cuspSourcePeak i)
    ((S.hfibers r.val r.property).1.union (R.measurableSet_cuspSourcePeak i))
    (he.mono (fun _ hp => hp.2.1)), measureReal_union hdis (R.measurableSet_cuspSourcePeak i),
    R.cuspPartialLaw_mass_head r hW hr, R.cuspPartialLaw_mass_peak i hinside]
  ring

/-- The source remainder joins every retained point outside its own
square and the old head. Its only internal deficit is the literal qJ. -/
theorem cuspPartial_adjacency_row_remainder (R : S.ReverseRecovery) (r i : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r}) :
    rowIntegral R.cuspPartialLaw (adjacencyKernel W) (R.cuspSourceRemainder i) =
      μ.real (R.cuspSourceRemainder i) * (1 - S.originalAtomMass r) - R.cuspRemainderMissing i := by
  let := R.cuspPartialLaw_probability
  have hac := R.cuspPartialLaw_ac.prod R.cuspPartialLaw_ac
  have he := R.adjacency_rows_event r i hW hd hgap hr
  have hq : crossIntegral R.cuspPartialLaw (fun x y => 1 - adjacencyKernel W x y)
      (R.cuspSourceRemainder i) (R.cuspSourceRemainder i) = R.cuspRemainderMissing i := by
    rw [crossIntegral, ← Measure.prod_restrict, R.cuspPartialLaw_restrict_remainder i,
      Measure.prod_restrict]
    rfl
  rw [row_of_missing_block (adjacencyKernel W) ((adjacencyKernel_measurable W).mono_ac hac)
    (hac.ae_le (adjacencyKernel_bound W)) _ _ _ (R.measurableSet_cuspSourceRemainder i)
    (S.hfibers r.val r.property).1 (R.measurableSet_cuspSourceRemainder i)
    (he.mono (fun _ hp => hp.2.2)), hq, R.cuspPartialLaw_mass_head r hW hr,
    R.cuspPartialLaw_mass_remainder i]

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
