module

public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedSources
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedScoreFloor

/-!
# Score budget of the saturated sources

The two saturated heads, their entire singleton compulsory sources and the
residual carrier together exhaust the shifted-row score budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The averaged physical charge row agrees almost everywhere with the
original homogeneous shifted row plus its adjacency charge. -/
private theorem ae_rootChargeRow_eq_shifted_row_plus
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ, S.rootChargeRow r y = r.val y + m * (if 0 < r.val y then 1 else 0) := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hrows : ∀ᵐ x ∂μ.restrict Ir,
      chargeKernel W x =ᵐ[μ]
        fun y => r.val y + m * (if 0 < r.val y then 1 else 0) :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hs := hW.strict_gap_structure hd hgap
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir →
      PhysicalRepresentative.charge W m p.1 p.2 = S.rootChargeRow r p.2 ∧
      PhysicalRepresentative.charge W m p.1 p.2 = chargeKernel W p.1 p.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hroot hp hIr
    exact ⟨hroot hIr, hp⟩
  have hsections := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨x, hxIr, hxrows, hxsection⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIrpos.ne'
      (hrows.and (ae_restrict_of_ae hsections))
  filter_upwards [hxrows, hxsection] with y hy hp
  exact (hp hxIr).1.symm.trans ((hp hxIr).2.trans hy)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual original physical root-charge average is integrable on
the probability carrier. -/
private theorem integrable_rootChargeRow (S : SelectedHighLowStructure W m)
    (r : S.I) : Integrable (S.rootChargeRow r) μ := by
  apply Integrable.of_bound (S.measurable_rootChargeRow r).aestronglyMeasurable 3
  filter_upwards [] with x
  have hx := S.rootChargeRow_mem_Icc r x
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hx.1, hx.2.trans (by norm_num)⟩

/-- On the entire original source compelled only to the first head,
the shifted-score deficit is exactly the other head's original
physical charge deficit. -/
private theorem ae_compulsorySource_deficit_eq_other_charge
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.reverseCompulsorySource {r}),
      1 - m - r.val x - u.val x = 1 - S.rootChargeRow u x := by
  have hnothead : ∀ᵐ x ∂μ, x ∈ S.H → S.ρ x ≠ u.val := by
    filter_upwards [compl_mem_ae_iff.mpr
      (hpair.symm.high_head_null hW hd hgap hell)] with x hx hH hu
    exact hx ⟨hu, hH⟩
  filter_upwards [ae_restrict_of_ae (S.ae_whole_row_nonneg r hW),
    ae_restrict_of_ae (S.ae_rootChargeRow_eq_shifted_row_plus u hW hd hgap),
    ae_restrict_of_ae hnothead,
    ae_restrict_mem (S.measurableSet_reverseCompulsorySource {r})]
    with x hrnonneg hcharge hnot hx
  have hNr : x ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val := by
    obtain ⟨v, hv, hxv⟩ := hx.2.2.1
    have hvr : v = r := Finset.mem_singleton.mp (hx.2.2.2 v hv hxv)
    simpa only [hvr] using hxv
  have hrzero : r.val x = 0 := le_antisymm hNr.2 hrnonneg
  have hnotNu : x ∉ KernelOperator.wholeFiberMissingSet S.ρ u.val := by
    intro hu
    have hmem := hx.2.2.2 u (hpair.symm.head_eligibleReverseAtom hW hd hgap hell) hu
    exact hpair.1 (Finset.mem_singleton.mp hmem).symm
  have huPos : 0 < u.val x := by
    have huNotOwn : S.ρ x ≠ u.val := hnot hx.1
    exact lt_of_not_ge (fun h => hnotNu ⟨huNotOwn, h⟩)
  rw [hrzero, hcharge]
  simp only [ite_eq_left huPos]
  ring

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual saturated row score equals its global cap on each
original head fiber, so the deficit there is zero. -/
private theorem ae_head_deficit_eq_zero
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val},
      1 - m - r.val x - u.val x = 0 := by
  filter_upwards [S.root_row_zero_on_fiber r, hpair.symm.row_on_other] with x hr hu
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Both original whole-row means determine the global shifted-score
deficit exactly. -/
private theorem integral_shifted_score_deficit
    (S : SelectedHighLowStructure W m) (r u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    (∫ x, 1 - m - r.val x - u.val x ∂μ) =
      1 - m - 2 * (2 * (c - m * d)) := by
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  have hfirst := integral_sub ((integrable_const (1 - m)).sub hr) hu
  have hsecond := integral_sub (integrable_const (1 - m)) hr
  simp only [Pi.sub_apply] at hfirst hsecond
  rw [hfirst, hsecond,
    S.row_integral_of_stationary r hW, S.row_integral_of_stationary u hW]
  simp
  ring

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem entire_source_integral_budget
    (Ir Iu SA SB : Set Ω) (hIr : MeasurableSet Ir) (hIu : MeasurableSet Iu)
    (hSA : MeasurableSet SA) (hSB : MeasurableSet SB)
    (f fA fB : Ω → ℝ) (δ : ℝ) (hf : Integrable f μ)
    (hfA : IntegrableOn fA SA μ) (hfB : IntegrableOn fB SB μ)
    (hdisjoint : ∀ᵐ x ∂μ, ¬(x ∈ SA ∧ x ∈ SB))
    (hheads : ∀ᵐ x ∂μ, x ∈ Ir ∪ Iu → f x = 0)
    (hA : ∀ᵐ x ∂μ.restrict SA, f x = fA x)
    (hB : ∀ᵐ x ∂μ.restrict SB, f x = fB x)
    (hfloor : ∀ᵐ x ∂μ.restrict (Ir ∪ Iu ∪ SA ∪ SB)ᶜ, δ ≤ f x) :
    (∫ x in SA, fA x ∂μ) + (∫ x in SB, fB x ∂μ) +
      δ * μ.real (Ir ∪ Iu ∪ SA ∪ SB)ᶜ ≤ ∫ x, f x ∂μ := by
  classical
  let R := (Ir ∪ Iu ∪ SA ∪ SB)ᶜ
  have hR : MeasurableSet R := (((hIr.union hIu).union hSA).union hSB).compl
  have hIA : Integrable (SA.indicator fA) μ := (integrable_indicator_iff hSA).mpr hfA
  have hIB : Integrable (SB.indicator fB) μ := (integrable_indicator_iff hSB).mpr hfB
  have hIC : Integrable (R.indicator (fun _ => δ)) μ :=
    (integrable_const δ).indicator hR
  have hA' := (ae_restrict_iff' hSA).mp hA
  have hB' := (ae_restrict_iff' hSB).mp hB
  have hfloor' := (ae_restrict_iff' hR).mp hfloor
  have hpoint : ∀ᵐ x ∂μ,
      SA.indicator fA x + SB.indicator fB x + R.indicator (fun _ => δ) x ≤ f x := by
    filter_upwards [hdisjoint, hheads, hA', hB', hfloor'] with x hdis hxhead hxA hxB hxR
    by_cases ha : x ∈ SA
    · have hb : x ∉ SB := fun hb => hdis ⟨ha, hb⟩
      have hr : x ∉ R := fun hx => hx (Or.inl (Or.inr ha))
      simpa only [indicator_of_mem ha, indicator_of_notMem hb,
        indicator_of_notMem hr, add_zero] using (hxA ha).symm.le
    · by_cases hb : x ∈ SB
      · have hr : x ∉ R := fun hx => hx (Or.inr hb)
        simpa only [indicator_of_notMem ha, indicator_of_mem hb,
          indicator_of_notMem hr, zero_add, add_zero] using (hxB hb).symm.le
      · by_cases hr : x ∈ R
        · simpa only [indicator_of_notMem ha, indicator_of_notMem hb,
            indicator_of_mem hr, zero_add] using hxR hr
        · have hhead : x ∈ Ir ∪ Iu := by
            simpa only [R, mem_compl_iff, not_not, mem_union, ha, hb, or_false] using hr
          simp only [indicator_of_notMem ha, indicator_of_notMem hb,
            indicator_of_notMem hr, zero_add, hxhead hhead, le_refl]
  have hbound := integral_mono_ae ((hIA.add hIB).add hIC) hf hpoint
  rw [integral_add' (hIA.add hIB) hIC, integral_add' hIA hIB,
    integral_indicator hSA, integral_indicator hSB, integral_indicator_const δ hR] at hbound
  simpa only [smul_eq_mul, mul_comm] using hbound

/-- The original two saturated heads, their entire singleton compulsory
sources, and the residual carrier exhaust the actual shifted-row score
budget. The two source terms use original physical charge rows. -/
theorem IsSaturatedAtomPair.entire_source_score_budget
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    (∫ x in S.reverseCompulsorySource {r}, 1 - S.rootChargeRow u x ∂μ) +
      (∫ x in S.reverseCompulsorySource {u}, 1 - S.rootChargeRow r x ∂μ) +
      (1 + m) * μ.real
        ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val} ∪
          S.reverseCompulsorySource {r} ∪ S.reverseCompulsorySource {u})ᶜ ≤
      1 - m - 2 * (2 * (c - m * d)) := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  let Iu : Set Ω := {x | S.ρ x = u.val}
  let SA := S.reverseCompulsorySource {r}
  let SB := S.reverseCompulsorySource {u}
  let f : Ω → ℝ := fun x => 1 - m - r.val x - u.val x
  let fA : Ω → ℝ := fun x => 1 - S.rootChargeRow u x
  let fB : Ω → ℝ := fun x => 1 - S.rootChargeRow r x
  have hIr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hIu : MeasurableSet Iu := (S.hfibers u.val u.property).1
  have hSA : MeasurableSet SA := S.measurableSet_reverseCompulsorySource {r}
  have hSB : MeasurableSet SB := S.measurableSet_reverseCompulsorySource {u}
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  have hf : Integrable f μ := ((integrable_const (1 - m)).sub hr).sub hu
  have hfA : IntegrableOn fA SA μ :=
    ((integrable_const (1 : ℝ)).sub (integrable_rootChargeRow S u)).integrableOn
  have hfB : IntegrableOn fB SB μ :=
    ((integrable_const (1 : ℝ)).sub (integrable_rootChargeRow S r)).integrableOn
  have hdisjoint : ∀ᵐ x ∂μ, ¬(x ∈ SA ∧ x ∈ SB) :=
    Eventually.of_forall (fun x hx =>
      Set.disjoint_left.mp (S.disjoint_singleton_compulsorySources r u hpair.1) hx.1 hx.2)
  have hheads : ∀ᵐ x ∂μ, x ∈ Ir ∪ Iu → f x = 0 := by
    have hfirst := (ae_restrict_iff' hIr).mp (ae_head_deficit_eq_zero hpair)
    have hsecond := (ae_restrict_iff' hIu).mp (ae_head_deficit_eq_zero hpair.symm)
    filter_upwards [hfirst, hsecond] with x hx hy hmem
    rcases hmem with h | h
    · exact hx h
    · have hz := hy h
      dsimp only [f] at hz ⊢
      linarith
  have hA : ∀ᵐ x ∂μ.restrict SA, f x = fA x :=
    ae_compulsorySource_deficit_eq_other_charge hpair hW hd hgap hell
  have hB : ∀ᵐ x ∂μ.restrict SB, f x = fB x := by
    filter_upwards [ae_compulsorySource_deficit_eq_other_charge
      hpair.symm hW hd hgap hell] with x hx
    dsimp only [f, fB] at hx ⊢
    linarith
  have hfloor : ∀ᵐ x ∂μ.restrict (Ir ∪ Iu ∪ SA ∪ SB)ᶜ,
      1 + m ≤ f x :=
    hpair.ae_entire_source_score_floor hW hd hgap hell
  have hbound := entire_source_integral_budget Ir Iu SA SB hIr hIu hSA hSB
    f fA fB (1 + m) hf hfA hfB hdisjoint hheads hA hB hfloor
  rw [S.integral_shifted_score_deficit r u hW] at hbound
  exact hbound

end Erdos1017.CappedModel.SelectedHighLowStructure
