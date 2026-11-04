module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeLowSlopeGeometry
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Edge charge cap on the third-cusp missing region

At the low-slope third cusp every physical edge of the entire original missing
region carries charge below `4/21`, and the missing square pays at most `8/21`
of its unhalved edge mass `z = G(J,J)/2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

private theorem tupleCharge_three {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z : Ω) (hsym : ∀ a b, Y a b = Y b a) :
    FiniteArity.tupleCharge Y ![x, y, z] = Y x y + Y x z + Y y z := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
    FiniteArity.crossSum, Fin.sum_univ_succ, hsym y x, hsym z x, hsym z y]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- A measurable symmetric order-three clique test, sectioned at almost
every ordered pair: almost every third vertex of a triangle obeys the
triangle cap. The root section is swapped by product Fubini on one
measurable set, not by choosing pointwise representatives. -/
private theorem ae_pair_triangle (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hAm : Measurable (Function.uncurry A)) (hAs : ∀ x y, A x y = A y x)
    (hYm : Measurable (Function.uncurry Y)) (hYs : ∀ x y, Y x y = Y y x)
    (htest : FiniteArity.FeasibleOrder μ A Y 3) :
    ∀ᵐ q ∂μ.prod μ, ∀ᵐ z ∂μ, A q.1 q.2 = true → A q.1 z = true → A q.2 z = true →
      Y q.1 q.2 + Y q.1 z + Y q.2 z ≤ 1 := by
  have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
    (measurePreserving_finTwoArrow μ)
  have hvec (z : Ω) (q : Ω × Ω) :
      Fin.cons z ((MeasurableEquiv.finTwoArrow (α := Ω)).symm q) = ![z, q.1, q.2] := by
    ext k
    fin_cases k <;> rfl
  have hrooted : ∀ᵐ z ∂μ, ∀ᵐ q ∂μ.prod μ, A q.1 q.2 = true → A q.1 z = true →
      A q.2 z = true → Y q.1 q.2 + Y q.1 z + Y q.2 z ≤ 1 := by
    filter_upwards [FiniteArity.ae_root_sections μ 2 _ htest] with z hz
    filter_upwards [hmp.quasiMeasurePreserving.ae hz] with q hq hxy hxz hyz
    rw [hvec] at hq
    have hyx : A q.2 q.1 = true := (hAs q.2 q.1).trans hxy
    have hzx : A z q.1 = true := (hAs z q.1).trans hxz
    have hzy : A z q.2 = true := (hAs z q.2).trans hyz
    have hclique : FiniteArity.TupleClique A ![z, q.1, q.2] := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · exact hzx
      · exact hzy
      · exact hxz
      · exact absurd rfl hab
      · exact hxy
      · exact hyz
      · exact hyx
      · exact absurd rfl hab
    have hbound := hq hclique
    rw [tupleCharge_three Y z q.1 q.2 hYs, hYs z q.1, hYs z q.2] at hbound
    linarith only [hbound]
  have hpairA (f g : Ω × (Ω × Ω) → Ω) (hf : Measurable f) (hg : Measurable g) :
      MeasurableSet {w | A (f w) (g w) = true} :=
    (hAm.comp (hf.prodMk hg)) (measurableSet_singleton true)
  have hpairY (f g : Ω × (Ω × Ω) → Ω) (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun w => Y (f w) (g w)) :=
    hYm.comp (hf.prodMk hg)
  have h0 : Measurable (fun w : Ω × (Ω × Ω) => w.1) := measurable_fst
  have h1 : Measurable (fun w : Ω × (Ω × Ω) => w.2.1) := measurable_snd.fst
  have h2 : Measurable (fun w : Ω × (Ω × Ω) => w.2.2) := measurable_snd.snd
  have hmeas : MeasurableSet {w : Ω × (Ω × Ω) | A w.2.1 w.2.2 = true →
      A w.2.1 w.1 = true → A w.2.2 w.1 = true →
        Y w.2.1 w.2.2 + Y w.2.1 w.1 + Y w.2.2 w.1 ≤ 1} :=
    (hpairA _ _ h1 h2).imp ((hpairA _ _ h1 h0).imp ((hpairA _ _ h2 h0).imp
      (measurableSet_le (((hpairY _ _ h1 h2).add (hpairY _ _ h1 h0)).add
        (hpairY _ _ h2 h0)) measurable_const)))
  exact (Measure.ae_ae_comm (p := fun (z : Ω) (q : Ω × Ω) => A q.1 q.2 = true →
    A q.1 z = true → A q.2 z = true → Y q.1 q.2 + Y q.1 z + Y q.2 z ≤ 1) hmeas).mp hrooted

/-- Every fixed original shifted-kernel row is integrable on the original
probability law, without selecting an almost-everywhere representative. -/
private theorem integrable_shifted_row (x : Ω) :
    Integrable (shiftedKernel W m x) μ := by
  have hmeas : StronglyMeasurable (shiftedKernel W m x) := by
    exact (W.stronglyMeasurable_moment
      (continuous_shiftedColor m).measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound hmeas.aestronglyMeasurable (3 + ‖m‖)
  exact Eventually.of_forall (fun z => by
    have h := norm_integral_le_of_norm_le_const (μ := W.kernel (x, z))
      (Filter.Eventually.of_forall (shiftedColor_norm_le m))
    simpa only [shiftedKernel, shiftedMoment, DecoratedKernel.moment,
      probReal_univ, mul_one] using h)

omit [IsProbabilityMeasure μ] in
/-- On a pair where the physical representative agrees with the original
adjacency and charge moments, the original shifted kernel is the physical
charge plus the own multiplier on a physical edge and zero off it. -/
private theorem shiftedKernel_eq_physical (x z : Ω)
    (hG : adjacencyKernel W x z =
      if PhysicalRepresentative.adjacency W m x z = true then 1 else 0)
    (hY : PhysicalRepresentative.charge W m x z = chargeKernel W x z) :
    shiftedKernel W m x z = if PhysicalRepresentative.adjacency W m x z = true then
      PhysicalRepresentative.charge W m x z - m else 0 := by
  have hs := shiftedMoment_eq W m (x, z)
  change shiftedKernel W m x z = chargeKernel W x z - m * adjacencyKernel W x z at hs
  rw [hs, hG, ← hY]
  cases ha : PhysicalRepresentative.adjacency W m x z
  · simp [PhysicalRepresentative.charge_zero_of_nonedge W m x z ha]
  · simp

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {d c : ℝ}

/-- At the low-slope third cusp, every actual physical edge of the entire
original missing region carries physical charge below 4/21. Both endpoints
miss the whole original peak. On a common physical neighbor the triangle
test caps their shifted row sum by 2*ell+1-q; on a private neighbor the
K2 cap gives 1+ell; absent pairs contribute zero. If q>=4/21 both caps are
at most 2*ell+17/21, and the two flat original rows contradict A>11/39.
No nonuniversality hypothesis is needed: a null region is vacuous. -/
theorem cusp_three_missing_edge_charge_lt (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.cuspThreeMissingRegion i → p.2 ∈ S.cuspThreeMissingRegion i →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
        PhysicalRepresentative.charge W m p.1 p.2 < 4 / 21 := by
  let I := {x | S.ρ x = i.val}
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  obtain ⟨hslope, hfloor, _⟩ :=
    S.cusp_three_low_slope_peak_bounds i hdk hW hgap hglobal hell hpeak
  change 11 / 39 < μ.real I at hfloor
  have hdk' : d = (1 - 1 / (3 : ℝ) ^ 2) / 2 := by norm_num [hdk]
  obtain ⟨_, _, _, _, hmargin⟩ := hW.cusp_contact_parameters 3 (by norm_num) hdk' hgap hglobal
  have hrow : 4 / 27 - 8 * m / 9 < 2 * (c - m * d) := by
    rw [hdk] at hmargin ⊢
    norm_num at hmargin
    linarith only [hmargin]
  have hs := hW.strict_gap_structure hd hgap
  have hcol : ∀ᵐ p ∂μ.prod μ, S.ρ p.2 = i.val → p.1 ∉ S.rootNeighborhood i →
      adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [adjacencyKernel_symm W,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae
        (S.ae_original_root_adjacency i hW hd hgap)] with p hsym hp hz hx
    simpa [hx] using hsym.trans (hp hz)
  have hpair : ∀ᵐ p ∂μ.prod μ,
      (adjacencyKernel W p.1 p.2 = if A p.1 p.2 = true then 1 else 0) ∧
        Y p.1 p.2 = chargeKernel W p.1 p.2 ∧
        (S.ρ p.2 = i.val → p.1 ∉ S.rootNeighborhood i → adjacencyKernel W p.1 p.2 = 0) := by
    filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support, hcol] with p hG hY hz
    exact ⟨hG, hY, hz⟩
  have hsec := Measure.ae_ae_of_ae_prod hpair
  have htest := PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
    hW.deterministic 3
  filter_upwards [ae_pair_triangle A Y (PhysicalRepresentative.measurable_adjacency W m)
      (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.measurable_charge W m)
      (PhysicalRepresentative.charge_symm W m) htest,
    Measure.quasiMeasurePreserving_fst.ae hsec, Measure.quasiMeasurePreserving_snd.ae hsec,
    Measure.quasiMeasurePreserving_fst.ae hW.stationary,
    Measure.quasiMeasurePreserving_snd.ae hW.stationary]
    with p htri hxsec hysec hxflat hyflat hxJ hyJ hxy
  by_contra hq
  have hq' : 4 / 21 ≤ Y p.1 p.2 := le_of_not_gt hq
  have hbound : ∀ᵐ z ∂μ, shiftedKernel W m p.1 z + shiftedKernel W m p.2 z ≤
      (-2 * m + 17 / 21) * (1 - I.indicator (fun _ => (1 : ℝ)) z) := by
    filter_upwards [htri, hxsec, hysec] with z hz hxz hyz
    rw [shiftedKernel_eq_physical p.1 z hxz.1 hxz.2.1,
      shiftedKernel_eq_physical p.2 z hyz.1 hyz.2.1]
    by_cases hzI : S.ρ z = i.val
    · have hxfalse : A p.1 z = false := by
        have hG := hxz.1
        rw [hxz.2.2 hzI hxJ.2] at hG
        cases ha : A p.1 z
        · rfl
        · change (0 : ℝ) = if A p.1 z = true then 1 else 0 at hG
          rw [ha] at hG
          norm_num at hG
      have hyfalse : A p.2 z = false := by
        have hG := hyz.1
        rw [hyz.2.2 hzI hyJ.2] at hG
        cases ha : A p.2 z
        · rfl
        · change (0 : ℝ) = if A p.2 z = true then 1 else 0 at hG
          rw [ha] at hG
          norm_num at hG
      have hzmem : z ∈ I := hzI
      change (if A p.1 z = true then Y p.1 z - m else 0) +
        (if A p.2 z = true then Y p.2 z - m else 0) ≤ _
      rw [hxfalse, hyfalse, indicator_of_mem hzmem]
      norm_num
    · have hznot : z ∉ I := hzI
      change (if A p.1 z = true then Y p.1 z - m else 0) +
        (if A p.2 z = true then Y p.2 z - m else 0) ≤ _
      rw [indicator_of_notMem hznot]
      have hYx := (PhysicalRepresentative.charge_mem_Icc W m p.1 z).2
      have hYy := (PhysicalRepresentative.charge_mem_Icc W m p.2 z).2
      change Y p.1 z ≤ 1 at hYx
      change Y p.2 z ≤ 1 at hYy
      have hlow := hslope.1
      cases ha : A p.1 z <;> cases hb : A p.2 z
      · norm_num
        linarith only [hlow]
      · norm_num
        linarith only [hlow, hYy]
      · norm_num
        linarith only [hlow, hYx]
      · have htriangle := hz hxy ha hb
        norm_num
        linarith only [htriangle, hq']
  have hMx := integrable_shifted_row (W := W) (m := m) p.1
  have hMy := integrable_shifted_row (W := W) (m := m) p.2
  have hcap : Integrable (fun z => (-2 * m + 17 / 21) *
      (1 - I.indicator (fun _ => (1 : ℝ)) z)) μ :=
    ((integrable_const 1).sub ((integrable_const 1).indicator hI)).const_mul _
  have hle := integral_mono_ae (hMx.add hMy) hcap hbound
  rw [integral_add' hMx hMy, integral_const_mul,
    integral_sub (integrable_const 1) ((integrable_const 1).indicator hI),
    integral_const, integral_indicator hI, setIntegral_const] at hle
  simp only [probReal_univ, smul_eq_mul, mul_one] at hle
  change (∫ y, shiftedKernel W m p.1 y ∂μ) = 2 * (c - m * d) at hxflat
  change (∫ y, shiftedKernel W m p.2 y ∂μ) = 2 * (c - m * d) at hyflat
  rw [hxflat, hyflat] at hle
  have hlow := hslope.1
  have hprod := mul_pos (by linarith only [hlow] : 0 < -2 * m + 17 / 21)
    (by linarith only [hfloor] : 0 < μ.real I - 11 / 39)
  nlinarith only [hle, hprod, hrow, hlow]

/-- The entire original missing square pays at most 8/21 of its unhalved
edge mass z=G(J,J)/2. The pointwise physical edge cap is proved above from
the actual triangle and K2 tests; it is not an input. Off physical edges the
original charge vanishes almost everywhere. -/
theorem cusp_three_missing_charge_le_edge_mass (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i) :
    (∫ p in S.cuspThreeMissingRegion i ×ˢ S.cuspThreeMissingRegion i,
      chargeKernel W p.1 p.2 ∂μ.prod μ) ≤
      8 / 21 * ((∫ p in S.cuspThreeMissingRegion i ×ˢ S.cuspThreeMissingRegion i,
        adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2) := by
  let J := S.cuspThreeMissingRegion i
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  have hJ : MeasurableSet J := S.measurableSet_cuspThreeMissingRegion i
  have hs := hW.strict_gap_structure hd hgap
  have hedge := S.cusp_three_missing_edge_charge_lt i hdk hW hgap hglobal hell hpeak
  have hpoint : ∀ᵐ p ∂(μ.prod μ).restrict (J ×ˢ J),
      chargeKernel W p.1 p.2 ≤ 4 / 21 * adjacencyKernel W p.1 p.2 := by
    filter_upwards [ae_restrict_of_ae hedge,
      ae_restrict_of_ae (PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support),
      ae_restrict_of_ae (PhysicalRepresentative.charge_ae_eq W m hs.strict_support),
      ae_restrict_mem (hJ.prod hJ)] with p hp hG hY hpJ
    change adjacencyKernel W p.1 p.2 = _ at hG
    rw [← hY, hG]
    cases ha : PhysicalRepresentative.adjacency W m p.1 p.2
    · simp [PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 ha]
    · have hlt := hp hpJ.1 hpJ.2 ha
      norm_num
      exact hlt.le
  have hY : Integrable (fun p : Ω × Ω => chargeKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (chargeKernel_measurable W)
      (chargeKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hmono := integral_mono_ae hY.integrableOn (hG.integrableOn.const_mul (4 / 21)) hpoint
  rw [integral_const_mul] at hmono
  change (∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂μ.prod μ) ≤
    8 / 21 * ((∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2)
  linarith only [hmono]

end Erdos1017.CappedModel.SelectedHighLowStructure
