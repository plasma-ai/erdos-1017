module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateSoleSource
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSaturatedPrivateStars
public import Erdos1017.Exclusions.Common.SelectedAtomicChargeBlocks
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateFailedInsertionDiffuse

/-!
# Hole exposure of the sole-source private peak

On the no-saturation branch, every positive high-hole atom has positive
first-root charge, every high dust missing row is bounded by a quarter, and the
private common peak has strictly more shifted exposure on its positive hole than
`ell` times the hole mass (`middle_private_sole_source_exposure`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c q : ℝ}

private theorem sole_source_surplus_lt {q : ℝ}
    (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5)) :
    (1 - LowerE2Scalar.missingMass q) / 2 -
      3 * Benchmark.twoHeadValue ((q + 2) / 3) < 7 / 1000 := by
  have hq0 : 0 ≤ q := by linarith only [hq.1]
  have hR := LowerE2Scalar.denominator_pos hq0
  let u := 1 / 5 - q
  have hu : u ∈ Icc (0 : ℝ) (1 / 50) := by dsimp only [u]; constructor <;> linarith [hq.1, hq.2]
  have h2 := pow_le_pow_left₀ hu.1 hu.2 2
  have h3 := pow_le_pow_left₀ hu.1 hu.2 3
  have h4 := pow_le_pow_left₀ hu.1 hu.2 4
  have hid : 56 * LowerE2Scalar.denominator q ^ 2 +
      1000 * LowerE2Scalar.pairNumerator q =
      8376 / 625 + 2877216 / 125 * u - 81504 / 25 * u ^ 2 -
        264144 / 5 * u ^ 3 - 4944 * u ^ 4 := by
    dsimp only [u, LowerE2Scalar.denominator, LowerE2Scalar.pairNumerator]
    ring
  have hpoly : 0 < 56 * LowerE2Scalar.denominator q ^ 2 +
      1000 * LowerE2Scalar.pairNumerator q := by nlinarith only [hid, h2, h3, h4, hu.1]
  have hfloor : -(2 * LowerE2Scalar.pairFloor q) < 7 / 1000 := by
    unfold LowerE2Scalar.pairFloor
    rw [neg_lt, mul_div_assoc', lt_div_iff₀ (by positivity)]
    linarith only [hpoly]
  linarith only [hfloor, LowerE2Scalar.pairFloor_eq_twoHeadValue hq0]

/-- The actual no-saturation parent laws supply the small nonnegative excess
and exact first-root count used in both atom and genuine-dust insertion. -/
theorem PrivatePhysicalPrimal.middle_sole_source_count_data
    {S : SelectedHighLowStructure W m} {i p : S.I} (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0) :
    0 ≤ P.positiveRootExcess ∧ P.positiveRootExcess < 7 / 3000 ∧
      2 * (S.originalAtomMass i ^ 2 -
        ∑ n ∈ Finset.range (P.orderCap + 1),
          (P.laws n).real (PrivatePhysicalPrimal.firstRootEvent S i n)) =
        S.originalAtomMass i * (3 * S.originalAtomMass i + S.originalAtomMass p - 1) +
          P.positiveRootExcess := by
  have hL : P.positiveRootExcess = P.rootExcess := by
    rw [P.positiveRootExcess_eq, P.laws_two_eq_zero hnull]
    simp only [measureReal_def, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, add_zero]
  rw [hL]
  have hbound := P.rootExcess_le hW hd hgap hnull
  have hsurplus := sole_source_surplus_lt hq
  rw [← hdq, ← hvalue] at hsurplus
  refine ⟨hbound.1, by linarith only [hbound.2, hsurplus, hgap], ?_⟩
  have hcount := P.first_root_count
  rw [P.rootExcess_eq_sum]
  have heq : (∑ n ∈ Finset.range (P.orderCap + 1),
      ((n : ℝ) - 1) * (P.laws n).real (PrivatePhysicalPrimal.firstRootEvent S i n)) =
      (∑ n ∈ Finset.range (P.orderCap + 1),
        ((n : ℝ) - 3) * (P.laws n).real (PrivatePhysicalPrimal.firstRootEvent S i n)) +
      2 * ∑ n ∈ Finset.range (P.orderCap + 1),
        (P.laws n).real (PrivatePhysicalPrimal.firstRootEvent S i n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  dsimp only [originalAtomMass]
  linarith only [hcount, heq]

/-- Every actual positive HIGH-hole atom has positive first-root charge.
The scalar insertion margin uses the full closed missing region of this atom. -/
theorem PrivatePhysicalPrimal.middle_sole_source_atom_charge_pos
    {S : SelectedHighLowStructure W m} {i p : S.I} (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hm : m = -LowerE2Scalar.multiplier q)
    (hgamma : LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m)
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hA : S.originalAtomMass i ∈ Icc (61 / 200 : ℝ) (1 / 3))
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (j : S.I) (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, 0 < S.rootChargeRow i x := by
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hell9 : 9 / 11 ≤ -m := by rw [hneg]; exact MiddlePrivateSoleSourceScalar.multiplier_ge hq
  have hell83 : -m < 83 / 100 := by rw [hneg]; exact MiddlePrivateUnsaturatedScalar.multiplier_lt hq
  have hnonlow := hhigh.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
  obtain ⟨hji, hjp, _, _⟩ := S.middleSaturatedPrivateHighRegion_atom i p j hW hpos
  have hfailed := P.failed_insertion_atom_normalized hW hd hgap (by linarith) hprivate j hji hjp
    (S.ae_middleSaturatedPrivateHighRegion_atom_off_head i p j hW hpos)
  have hrow := S.middleSaturatedPrivateHighRegion_atomRow_normalized i p j hW hd hgap hpos
  have hbudget := S.middleSaturatedPrivateHighRegion_atom_sharp_budget i p j hW hd hgap
    hpeak hnonlow ⟨by linarith only [hA.1], hA.2⟩ (by linarith) hpos
  have hsmall : S.originalAtomMass j +
      μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) < 13 / 100 := by
    apply MiddleUnsaturatedJoinedScalar.sharp_radius_lt hq
      ⟨by linarith only [hA.1], hA.2⟩ hgamma
    rw [← hneg]
    linarith only [hbudget]
  rw [S.middleSaturatedPrivateHighRegion_missing_mass_eq i p j hW hpos] at hsmall
  let beta := S.coveredCountableBoundaryCoefficient (Sum.inl i) (Sum.inl j)
  have hconst : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, S.rootChargeRow i x = beta :=
    S.ae_atomic_rootChargeRow i j hW hd hgap
  have ha : 0 < S.originalAtomMass j :=
    ENNReal.toReal_pos (S.hfibers j.val j.property).2.1.ne' (measure_ne_top μ _)
  have havg : (∫ x in {x | S.ρ x = j.val}, S.rootChargeRow i x ∂μ) /
      S.originalAtomMass j = beta := by
    rw [integral_congr_ae hconst, setIntegral_const, smul_eq_mul]
    change S.originalAtomMass j * beta / S.originalAtomMass j = beta
    exact mul_div_cancel_left₀ _ ha.ne'
  have hbeta : m ≤ beta := by
    obtain ⟨x, _, hx, hb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers j.val j.property).2.1.ne'
      (hconst.and (ae_restrict_of_ae (S.ae_rootChargeRow_ge i hW hd hgap
        (by linarith))))
    rwa [hx] at hb
  have hbetapos : 0 < beta := by
    by_contra hn
    obtain ⟨hL0, hL, hcount⟩ := P.middle_sole_source_count_data hW hd hgap hq hdq hvalue hnull
    have hmargin := MiddlePrivateSoleSourceScalar.failed_insertion_margin hA.1 hA.2
      ((MiddlePrivateUnsaturatedScalar.gapFloor_gt hq).trans hgamma) hell9 hell83
      ha.le (show 0 ≤ S.originalAtomMass p from measureReal_nonneg)
      (show 0 ≤ μ.real (S.atomExtraHole j p) from measureReal_nonneg)
      (show S.originalAtomMass j + S.originalAtomMass p + μ.real (S.atomExtraHole j p) ≤ 1 / 4
        by linarith only [hsmall]) hL0 hL hcount (by simpa using hbeta) (le_of_not_gt hn)
    change (S.originalAtomMass i - S.originalAtomMass j) * _ -
      S.originalAtomMass i * μ.real (S.atomExtraHole j p) - P.positiveRootExcess ≤ _ at hfailed
    dsimp only [originalAtomMass] at hfailed hrow havg hmargin
    rw [hrow, havg] at hfailed
    linarith only [hfailed, hmargin]
  exact hconst.mono (fun _ hx => hx.symm ▸ hbetapos)

/-- The sharp selector bounds every genuine HIGH dust missing row by a
quarter on the same original model; no limiting source-tail argument is used. -/
theorem middle_sole_source_diffuse_missing_le_quarter
    (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hm : m = -LowerE2Scalar.multiplier q)
    (hgamma : LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hA : S.originalAtomMass i ∈ Icc (61 / 200 : ℝ) (1 / 3)) :
    ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H → (∫ y, 1 - adjacencyKernel W x y ∂μ) ≤ 1 / 4 := by
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hell : 2 / 3 ≤ -m := by
    rw [hneg]
    linarith only [MiddlePrivateSoleSourceScalar.multiplier_ge hq]
  have hnonlow := hhigh.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
  have hmargin : (-1 + 8 * S.originalAtomMass i -
      (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 <
      2 * (c - m * d) + m + (-m - 2 / 3) * (1 / 4) ^ 2 := by
    by_contra hn
    have hsmall := MiddleUnsaturatedJoinedScalar.sharp_radius_lt (T := 1 / 4) hq
      ⟨by linarith only [hA.1], hA.2⟩ hgamma (by
        rw [← hneg]
        linarith only [le_of_not_gt hn])
    norm_num at hsmall
  have hcap := S.ae_middle_diffuse_high_outside_le i hW hd hgap hpeak hnonlow
    ⟨by linarith only [hA.1], hA.2⟩ hell (by norm_num : (0 : ℝ) < 1 / 4)
    (by linarith only [hA.1]) hmargin
  filter_upwards [hcap, S.ae_diffuse_missing_row_le_outside hW hd hgap] with x hc hr hxD hxH
  exact (hr hxD).trans (hc hxD hxH)

private theorem sole_source_root_charge_shifted
    (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, S.rootChargeRow i x =
      i.val x + m * (if 0 < i.val x then 1 else 0) := by
  have hrows : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      chargeKernel W x =ᵐ[μ]
        fun y => i.val y + m * (if 0 < i.val y then 1 else 0) :=
    (S.hfibers i.val i.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hpair : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      PhysicalRepresentative.charge W m z.1 z.2 = S.rootChargeRow i z.2 ∧
      PhysicalRepresentative.charge W m z.1 z.2 = chargeKernel W z.1 z.2 := by
    filter_upwards [S.ae_root_charge i hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support]
      with z hr hy hi
    exact ⟨hr hi, hy⟩
  obtain ⟨x, hx, hrow, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers i.val i.property).2.1.ne'
    (hrows.and (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair)))
  filter_upwards [hrow, hsection] with y hy hp
  exact (hp hx).1.symm.trans ((hp hx).2.trans hy)

private theorem sole_source_exposure_of_positive_charge
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (hcharge : ∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p), 0 < S.rootChargeRow i x) :
    (-m) * μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p) <
      ∫ x in (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
        S.rootNeighborhood p), (i.val : Ω → ℝ) x ∂μ := by
  let K := ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p
  have hK : MeasurableSet K := ((S.hfibers i.val i.property).1.union
    (S.hfibers p.val p.property).1).compl.diff (S.measurableSet_rootNeighborhood p)
  have hk : 0 < μ K := S.private_hole_measure_pos i p hip hW hd hgap hprivate
  have hgt : ∀ᵐ x ∂μ.restrict K, -m < i.val x := by
    filter_upwards [hcharge, ae_restrict_mem hK,
      ae_restrict_of_ae (S.sole_source_root_charge_shifted i hW hd hgap),
      ae_restrict_of_ae (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate),
      ae_restrict_of_ae (S.ae_rootNeighborhood_iff i)] with x hc hx hr hN hpos
    have hni : S.ρ x ≠ i.val := fun he => hx.1 (Or.inl he)
    have hnp : S.ρ x ≠ p.val := fun he => hx.1 (Or.inr he)
    have hi : 0 < i.val x := hpos.mp (hN.mpr ⟨hni, hnp⟩)
    rw [ite_eq_left hi, mul_one] at hr
    linarith only [hc, hr]
  have hi : Integrable (fun x => (i.val : Ω → ℝ) x) (μ.restrict K) :=
    ((Lp.memLp i.val).integrable (by norm_num)).restrict
  have hpositive : 0 < ∫ x in K, (i.val x - (-m)) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (hgt.mono (fun _ hx => sub_nonneg.mpr hx.le)) (hi.sub (integrable_const _))]
    have hs : Function.support (fun x => i.val x - (-m)) =ᵐ[μ.restrict K] Set.univ := by
      filter_upwards [hgt] with x hx
      apply propext
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (sub_pos.mpr hx).ne'
    rw [measure_congr hs]
    simpa only [Measure.restrict_apply_univ] using hk
  rw [integral_sub hi (integrable_const _), integral_const, measureReal_restrict_apply_univ,
    smul_eq_mul] at hpositive
  change (-m) * μ.real K < ∫ x in K, (i.val : Ω → ℝ) x ∂μ
  linarith only [hpositive]

private theorem sole_source_charge_pos_of_dust
    {S : SelectedHighLowStructure W m} {i p : S.I} (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hm : m = -LowerE2Scalar.multiplier q)
    (hgamma : LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m)
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hA : S.originalAtomMass i ∈ Icc (61 / 200 : ℝ) (1 / 3))
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (hdust : ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.middleSaturatedPrivateHighRegion i p →
      0 < S.rootChargeRow i x) :
    ∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p), 0 < S.rootChargeRow i x := by
  let _ : Countable S.I := S.hI.to_subtype
  let K := ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p
  have hatoms : ∀ᵐ x ∂μ, ∀ j : S.I, x ∈ S.middleSaturatedPrivateHighRegion i p →
      S.ρ x = j.val → 0 < S.rootChargeRow i x := by
    rw [ae_all_iff]
    intro j
    by_cases hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩ {x | S.ρ x = j.val})
    · have hj := (ae_restrict_iff' (S.hfibers j.val j.property).1).mp
        (P.middle_sole_source_atom_charge_pos hW hd hgap hq hdq hvalue hm hgamma hnull
          hpeak hhigh hA hprivate j hpos)
      exact hj.mono (fun _ hx _ he => hx he)
    · have hz : μ (S.middleSaturatedPrivateHighRegion i p ∩ {x | S.ρ x = j.val}) = 0 :=
        le_antisymm (le_of_not_gt hpos) zero_le
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx hK hj
      exact False.elim (hx ⟨hK, hj⟩)
  have hK : MeasurableSet K := ((S.hfibers i.val i.property).1.union
    (S.hfibers p.val p.property).1).compl.diff (S.measurableSet_rootNeighborhood p)
  filter_upwards [S.ae_private_hole_high i p P.distinct_roots hW hd hgap hhigh hprivate,
    ae_restrict_mem hK, ae_restrict_of_ae hatoms, ae_restrict_of_ae hdust] with x hxH hxK hx hd
  have hxRegion : x ∈ S.middleSaturatedPrivateHighRegion i p := ⟨hxH, hxK⟩
  by_cases hxD : x ∈ S.D
  · exact hd hxD hxRegion
  · have hx' : x ∈ ⋃ r ∈ S.I, {y | S.ρ y = r} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hxD
    obtain ⟨r, hr⟩ := mem_iUnion.mp hx'
    obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
    exact hx ⟨r, hrI⟩ hxRegion hxr

private theorem sole_source_diffuse_charge_pos
    {S : SelectedHighLowStructure W m} {i p : S.I} (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hm : m = -LowerE2Scalar.multiplier q)
    (hgamma : LowerE2Scalar.gapFloor q < 2 * (c - m * d) + m)
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hA : S.originalAtomMass i ∈ Icc (61 / 200 : ℝ) (1 / 3))
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.middleSaturatedPrivateHighRegion i p →
      0 < S.rootChargeRow i x := by
  have hneg : -m = LowerE2Scalar.multiplier q := by rw [hm]; ring
  have hell9 : 9 / 11 ≤ -m := by rw [hneg]; exact MiddlePrivateSoleSourceScalar.multiplier_ge hq
  have hell83 : -m < 83 / 100 := by rw [hneg]; exact MiddlePrivateUnsaturatedScalar.multiplier_lt hq
  obtain ⟨hL0, hL, hcount⟩ := P.middle_sole_source_count_data hW hd hgap hq hdq hvalue hnull
  filter_upwards [P.failed_insertion_diffuse hW hd hgap (by linarith) hprivate,
    S.ae_missing_row_eq_second_add_diffuseExtraHole p hW hd hgap,
    S.middle_sole_source_diffuse_missing_le_quarter i hW hd hgap hq hm hgamma hpeak hhigh hA,
    S.ae_rootChargeRow_ge i hW hd hgap (by linarith)] with x hf he hc hb hxD hxK
  have hxi : S.ρ x ≠ i.val := fun hi => hxK.2.1 (Or.inl hi)
  have hxp : S.ρ x ≠ p.val := fun hp => hxK.2.1 (Or.inr hp)
  have hw : S.originalAtomMass p + μ.real (S.diffuseExtraHole p x) ≤ 1 / 4 := by
    change μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) ≤ 1 / 4
    rw [← he hxK.2.2]
    exact hc hxD hxK.1
  have hfailed := hf hxi hxp hxK.2.2
  by_contra hn
  have hmargin := MiddlePrivateSoleSourceScalar.failed_insertion_margin (a := 0) hA.1 hA.2
    ((MiddlePrivateUnsaturatedScalar.gapFloor_gt hq).trans hgamma) hell9 hell83
    le_rfl (show 0 ≤ S.originalAtomMass p from measureReal_nonneg)
    (show 0 ≤ μ.real (S.diffuseExtraHole p x) from measureReal_nonneg)
    (by simpa only [zero_add] using hw) hL0 hL hcount (by simpa using hb) (le_of_not_gt hn)
  dsimp only [originalAtomMass] at hmargin
  simp only [sub_zero, zero_add] at hmargin
  linarith only [hfailed, hmargin]

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual no-saturation private common peak has strictly more shifted
exposure on its positive original hole than `ell` times the hole mass.
Atomic and genuine diffuse charge positivity use the same original primal. -/
theorem middle_private_sole_source_exposure (S : SelectedHighLowStructure W m)
    (i p : S.I) (hip : i ≠ p) (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hnull : (μ.prod μ) {z | chargeKernel W z.1 z.2 = 1} = 0)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hsrc : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.reverseCompulsorySource {p})
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    (-m) * μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p) <
      ∫ x in (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
        S.rootNeighborhood p), (i.val : Ω → ℝ) x ∂μ := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, _, hgamma⟩ := hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  obtain ⟨hcut, hA, hthird, _⟩ := S.middle_private_peak_bounds hW hq hdq hvalue hderiv
    hgap hglobal hnull i p hip hpeak hprivate
  have hqclosed : q ∈ Icc (187 / 1000 : ℝ) (1 / 5) := ⟨hcut.le, hq.2.le⟩
  have hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H :=
    hsrc.mono (fun _ hx => hx.1)
  obtain ⟨P⟩ := S.exists_private_physical_primal i p hip hW hd hgap hprivate
  have hdust := sole_source_diffuse_charge_pos P hW hd hgap hqclosed hdq hvalue hm hgamma
    hnull hpeak hhigh ⟨hA.le, hthird.le⟩ hprivate
  have hcharge := sole_source_charge_pos_of_dust P hW hd hgap hqclosed hdq hvalue hm hgamma
    hnull hpeak hhigh ⟨hA.le, hthird.le⟩ hprivate hdust
  exact S.sole_source_exposure_of_positive_charge i p hip hW hd hgap hprivate hcharge

end Erdos1017.CappedModel.SelectedHighLowStructure
