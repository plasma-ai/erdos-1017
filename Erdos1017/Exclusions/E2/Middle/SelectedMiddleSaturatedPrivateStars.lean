module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSaturatedPrivateCount
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleOffPairCompulsory
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSharpMissingCap
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleSimultaneousSquareReserve
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateFailedInsertion
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateFailedInsertionDiffuse
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedSourcePeak
public import Erdos1017.Exclusions.Common.SelectedAtomicChargeBlocks

/-!
# Forbidden radius on the high hole of a saturated private peak

The high region `middleSaturatedPrivateHighRegion` lies outside the saturated
missing head's neighborhood, and one sharp radius bounds the forbidden mass at
every point of the complete high hole, whole atoms and diffuse points alike
(`ae_middleSaturatedPrivate_forbidden_radius`), through the failed-insertion
inequality on each positive atom.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- Every HIGH point outside the saturated missing head's neighborhood,
with the original peak and head fibers removed. The head removal changes
the intended HIGH region only on a null set. -/
def middleSaturatedPrivateHighRegion (S : SelectedHighLowStructure W m)
    (i p : S.I) : Set Ω :=
  S.H ∩ (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
    S.rootNeighborhood p)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_middleSaturatedPrivateHighRegion
    (S : SelectedHighLowStructure W m) (i p : S.I) :
    MeasurableSet (S.middleSaturatedPrivateHighRegion i p) :=
  S.hpartition.1.inter (((S.hfibers i.val i.property).1.union
    (S.hfibers p.val p.property).1).compl.diff (S.measurableSet_rootNeighborhood p))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem middleSaturatedPrivateHighRegion_subset_exterior
    (S : SelectedHighLowStructure W m) (i p : S.I) :
    S.middleSaturatedPrivateHighRegion i p ⊆
      (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
        S.rootNeighborhood p) :=
  Set.inter_subset_right

/-- Removing the saturated head from the literal region loses only a
null HIGH set. Thus the region covers the entire intended HIGH hole. -/
theorem ae_middleSaturatedPrivateHighRegion_iff
    (S : SelectedHighLowStructure W m) (i p u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hpair : S.IsSaturatedAtomPair p u) :
    ∀ᵐ x ∂μ, x ∈ S.middleSaturatedPrivateHighRegion i p ↔
      x ∈ S.H ∧ x ∉ S.rootNeighborhood p ∧ S.ρ x ≠ i.val := by
  have hnull := hpair.high_head_null hW hd hgap hell
  have hae : ∀ᵐ x ∂μ, x ∉ {x | S.ρ x = p.val} ∩ S.H :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with x hx
  simp only [middleSaturatedPrivateHighRegion, Set.mem_inter_iff,
    Set.mem_sdiff, Set.mem_compl_iff, Set.mem_union,
    Set.mem_ofPred_eq, not_or, not_and] at hx ⊢
  tauto

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The literal private peak joins every recipient in the complete HIGH
hole region, including points with other LOW missing neighbors. -/
theorem ae_private_peak_joins_middleSaturatedHighRegion
    (S : SelectedHighLowStructure W m) (i p : S.I)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      z.2 ∈ S.middleSaturatedPrivateHighRegion i p →
        adjacencyKernel W z.1 z.2 = 1 := by
  filter_upwards [hprivate] with z hz hi hK
  have hnot : ¬(S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val) := by
    simpa only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq] using hK.2.1
  rw [hz hi, ite_eq_right hnot]

/-- The same joined peak-to-HIGH-hole pairs are present in the actual
physical representative. -/
theorem ae_private_peak_physical_join_middleSaturatedHighRegion
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      z.2 ∈ S.middleSaturatedPrivateHighRegion i p →
        PhysicalRepresentative.adjacency W m z.1 z.2 = true := by
  have hstrict := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [S.ae_private_peak_joins_middleSaturatedHighRegion i p hprivate,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hstrict]
    with z hj hp hi hK
  have h := hj hi hK
  change W.moment CappedColor.adjacency z = 1 at h
  rw [hp] at h
  cases hb : PhysicalRepresentative.adjacency W m z.1 z.2 <;> simp [hb] at h ⊢

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A positive original atom in the complete HIGH hole is wholly HIGH and
wholly missing from the saturated head, modulo its original fiber law. -/
theorem middleSaturatedPrivateHighRegion_atom
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    j ≠ i ∧ j ≠ p ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ S.H) ∧
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
        x ∈ KernelOperator.wholeFiberMissingSet S.ρ p.val) := by
  let K := S.middleSaturatedPrivateHighRegion i p
  let J := {x | S.ρ x = j.val}
  have hJ : MeasurableSet J := (S.hfibers j.val j.property).1
  have hji : j ≠ i := by
    intro he
    have hempty : K ∩ J = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hx.1.2.1 (Or.inl (hx.2.trans (congrArg Subtype.val he)))
    rw [hempty, measure_empty] at hpos
    exact (lt_irrefl 0) hpos
  have hjp : j ≠ p := by
    intro he
    have hempty : K ∩ J = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hx.1.2.1 (Or.inr (hx.2.trans (congrArg Subtype.val he)))
    rw [hempty, measure_empty] at hpos
    exact (lt_irrefl 0) hpos
  have hhigh : ∀ᵐ x ∂μ.restrict J, x ∈ S.H :=
    S.high_fiber_of_positive_high_subset j (K ∩ J) hpos
      (fun _ hx => hx.1.1) (fun _ hx => hx.2)
  rcases S.ae_fiber_missing_or_not j p hW with hmissing | hjoined
  · exact ⟨hji, hjp, hhigh, hmissing⟩
  · have hjoined' := (ae_restrict_iff' hJ).mp hjoined
    obtain ⟨x, hx, hnot⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hpos.ne' (ae_restrict_of_ae hjoined')
    have hxK : x ∈ K := hx.1
    have hxJ : x ∈ J := hx.2
    have hxp : S.ρ x ≠ p.val := by
      intro he
      exact hjp (Subtype.ext (hxJ.symm.trans he))
    have hrow : p.val x ≤ 0 := not_lt.mp (fun h => hxK.2.2 ⟨hxp, h⟩)
    exact False.elim (hnot hxJ ⟨hxp, hrow⟩)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A positive HIGH-hole atom forces the whole saturated head fiber into
its closed original missing region on the original law. -/
private theorem ae_middleSaturatedPrivateHighRegion_partner_fiber_missing
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    ∀ᵐ x ∂μ, S.ρ x = p.val →
      x ∈ KernelOperator.wholeFiberMissingSet S.ρ j.val := by
  let J := {x | S.ρ x = j.val}
  obtain ⟨_, hjp, _, hmissing⟩ :=
    S.middleSaturatedPrivateHighRegion_atom i p j hW hpos
  have hJ : MeasurableSet J := (S.hfibers j.val j.property).1
  have hpositive : 0 < μ (J ∩ {x | p.val x ≤ 0}) := by
    have hsub : ∀ᵐ x ∂μ, x ∈ S.middleSaturatedPrivateHighRegion i p ∩ J →
        x ∈ J ∩ {x | p.val x ≤ 0} := by
      have h := (ae_restrict_iff' hJ).mp hmissing
      filter_upwards [h] with x hx hK
      exact ⟨hK.2, (hx hK.2).2⟩
    exact lt_of_lt_of_le hpos (measure_mono_ae hsub)
  have hcross := KernelOperator.whole_row_cross_block_zero_of_positive_nonpositive
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ
    p.val j.val
    (S.hfibers p.val p.property).2.1 (S.hfibers j.val j.property).2.1
    (S.hfibers p.val p.property).2.2.2 (S.hfibers j.val j.property).2.2.2
    (shiftedKernel_measurable W m) (adjacencyKernel_measurable W)
    (chargeKernel_measurable W)
    ((shiftedMoment_symm W m).mono (fun q hq => hq.symm)) hW.moment_mem
    hJ hpositive
  have h := (ae_restrict_iff' (S.hfibers p.val p.property).1).mp hcross.2.1
  filter_upwards [h] with x hx hxp
  have hxzero : j.val x = 0 := hx hxp
  refine ⟨?_, by simp [hxzero]⟩
  intro hsame
  exact hjp (Subtype.ext (hsame.symm.trans hxp))

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The saturated partner's entire original mass is part of the
positive HIGH-hole atom's closed missing tail. -/
theorem middleSaturatedPrivateHighRegion_partner_mass_le_missing
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    S.originalAtomMass p ≤
      μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
  let P := {x | S.ρ x = p.val}
  have hsub := S.ae_middleSaturatedPrivateHighRegion_partner_fiber_missing
    i p j hW hpos
  change μ.real P ≤ μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The closed missing tail of an actual K-atom is exactly the head mass
plus the extra missing region used by the all-order insertion theorem. -/
theorem middleSaturatedPrivateHighRegion_missing_mass_eq
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) =
      S.originalAtomMass p + μ.real (S.atomExtraHole j p) := by
  let M := KernelOperator.wholeFiberMissingSet S.ρ j.val
  let P := {x | S.ρ x = p.val}
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hsub := S.ae_middleSaturatedPrivateHighRegion_partner_fiber_missing
    i p j hW hpos
  have hMP : μ.real (M ∩ P) = μ.real P := by
    apply measureReal_congr
    filter_upwards [hsub] with x hx
    exact propext ⟨fun h => h.2, fun h => ⟨hx h, h⟩⟩
  have hdiff : M \ P = S.atomExtraHole j p := by
    ext x
    change (S.ρ x ≠ j.val ∧ j.val x ≤ 0) ∧ S.ρ x ≠ p.val ↔
      x ∉ S.rootNeighborhood j ∧ x ∉
        ({x | S.ρ x = j.val} ∪ {x | S.ρ x = p.val})
    constructor
    · rintro ⟨⟨hj, hzero⟩, hp⟩
      exact ⟨fun h => not_lt_of_ge hzero h.2, fun h => h.elim hj hp⟩
    · rintro ⟨hN, hJP⟩
      have hj : S.ρ x ≠ j.val := fun h => hJP (Or.inl h)
      have hp : S.ρ x ≠ p.val := fun h => hJP (Or.inr h)
      exact ⟨⟨hj, le_of_not_gt (fun h => hN ⟨hj, h⟩)⟩, hp⟩
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := M) hP
  rw [hMP, hdiff] at hsplit
  change μ.real P + μ.real (S.atomExtraHole j p) = μ.real M at hsplit
  simpa only [originalAtomMass] using hsplit.symm

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The actual K-atom meets the exact outside-neighborhood premise of
the all-order failed-insertion theorem. -/
theorem ae_middleSaturatedPrivateHighRegion_atom_off_head
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∉ S.rootNeighborhood p := by
  have hmissing := (S.middleSaturatedPrivateHighRegion_atom i p j hW hpos).2.2.2
  filter_upwards [hmissing] with x hx hN
  exact not_lt_of_ge hx.2 hN.2

/-- The actual peak's sharp selector pays the full closed missing tail of
every positive HIGH-hole atom, including the saturated partner head. -/
theorem middleSaturatedPrivateHighRegion_atom_sharp_budget
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hell : 2 / 3 ≤ -m)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    2 * (c - m * d) + m + (-m - 2 / 3) *
      (S.originalAtomMass j +
        μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)) ^ 2 ≤
      (-1 + 8 * S.originalAtomMass i -
        (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  obtain ⟨hji, _, hhigh, _⟩ := S.middleSaturatedPrivateHighRegion_atom i p j hW hpos
  exact S.middle_high_atom_closed_missing_sq_bound i j hji hW hd hgap hpeak
    hnonlow hhigh hA hell

/-- The same selector bound in the insertion variables `a + b + f`. -/
theorem middleSaturatedPrivateHighRegion_atom_insertion_sq_cap
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hell : 2 / 3 ≤ -m)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    2 * (c - m * d) + m + (-m - 2 / 3) *
      (S.originalAtomMass j + S.originalAtomMass p +
        μ.real (S.atomExtraHole j p)) ^ 2 ≤
      (-1 + 8 * S.originalAtomMass i -
        (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  have h := S.middleSaturatedPrivateHighRegion_atom_sharp_budget i p j
    hW hd hgap hpeak hnonlow hA hell hpos
  rw [S.middleSaturatedPrivateHighRegion_missing_mass_eq i p j hW hpos] at h
  convert h using 1; ring

/-- The two actual saturated heads use one original sharp selector reserve.
Their square costs are not added from separate peak-avoiding flows. -/
theorem middleSaturatedPrivate_pair_square_sharp_budget
    (S : SelectedHighLowStructure W m) (i p u : S.I)
    (hip : i ≠ p) (hiu : i ≠ u) (hpair : S.IsSaturatedAtomPair p u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hell : 2 / 3 ≤ -m) :
    2 * (c - m * d) + m + (-m - 2 / 3) *
      ((S.originalAtomMass p) ^ 2 + (S.originalAtomMass u) ^ 2) ≤
      (-1 + 8 * S.originalAtomMass i -
        (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 := by
  let _ : Countable S.I := S.hI.to_subtype
  have hfinite := Summable.sum_le_tsum (s := {i, p, u})
    (fun k _ => sq_nonneg (S.originalAtomMass k)) S.originalAtomMass_sq_summable
  have hnot : i ∉ ({p, u} : Finset S.I) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ⟨hip, hiu⟩
  have hQ : (S.originalAtomMass i) ^ 2 + (S.originalAtomMass p) ^ 2 +
      (S.originalAtomMass u) ^ 2 ≤ ∑' k, (S.originalAtomMass k) ^ 2 := by
    simpa only [Finset.sum_insert hnot, Finset.sum_pair hpair.1, add_assoc] using hfinite
  have hcoef : 0 ≤ -m - 2 / 3 := sub_nonneg.mpr hell
  have hQscaled := mul_le_mul_of_nonneg_left hQ hcoef
  have hjoint := S.middle_original_total_square_sharp_gap_bound i hW hd hgap
    hpeak hnonlow hA hell
  nlinarith only [hQscaled, hjoint]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- An original whole atom, its closed missing set, and its actual
neighborhood partition the entire original carrier. -/
private theorem rootNeighborhood_atom_missing_partition
    (S : SelectedHighLowStructure W m) (j : S.I) :
    μ.real (S.rootNeighborhood j) + S.originalAtomMass j +
      μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) = 1 := by
  let N := S.rootNeighborhood j
  let J := {x | S.ρ x = j.val}
  have hJ : MeasurableSet J := (S.hfibers j.val j.property).1
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood j
  have hNJ : Nᶜ ∩ J = J := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    exact ⟨fun h => h.2, fun h => ⟨fun hn => hn.1 h, h⟩⟩
  have hmissing : Nᶜ \ J = KernelOperator.wholeFiberMissingSet S.ρ j.val := by
    ext x
    change (¬(S.ρ x ≠ j.val ∧ 0 < j.val x) ∧ S.ρ x ≠ j.val) ↔
      (S.ρ x ≠ j.val ∧ j.val x ≤ 0)
    constructor
    · rintro ⟨hn, hj⟩
      exact ⟨hj, le_of_not_gt (fun hp => hn ⟨hj, hp⟩)⟩
    · rintro ⟨hj, hp⟩
      exact ⟨fun hn => not_lt_of_ge hp hn.2, hj⟩
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := Nᶜ) hJ
  rw [hNJ, hmissing, measureReal_compl hN, probReal_univ] at hsplit
  change μ.real J + μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) =
    1 - μ.real N at hsplit
  dsimp only [originalAtomMass]
  linarith

/-- The original stationary whole row gives the exact mean physical
charge of an atom through its actual closed missing mass. -/
private theorem atom_rootChargeRow_integral_eq
    (S : SelectedHighLowStructure W m) (j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    (∫ y, S.rootChargeRow j y ∂μ) =
      2 * (c - m * d) + m * μ.real (S.rootNeighborhood j) := by
  let J : Set Ω := {x | S.ρ x = j.val}
  have hJpos : 0 < μ J := (S.hfibers j.val j.property).2.1
  have hrows : ∀ᵐ x ∂μ.restrict J,
      chargeKernel W x =ᵐ[μ]
        fun y => j.val y + m * (if 0 < j.val y then 1 else 0) :=
    (S.hfibers j.val j.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hs := hW.strict_gap_structure hd hgap
  have hpair : ∀ᵐ z ∂μ.prod μ, z.1 ∈ J →
      PhysicalRepresentative.charge W m z.1 z.2 = S.rootChargeRow j z.2 ∧
      PhysicalRepresentative.charge W m z.1 z.2 = chargeKernel W z.1 z.2 := by
    filter_upwards [S.ae_root_charge j hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with z hz hc hJz
    exact ⟨hz hJz, hc⟩
  obtain ⟨x, hxJ, hxrows, hxsection⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hJpos.ne'
      (hrows.and (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair)))
  have hrow : ∀ᵐ y ∂μ, S.rootChargeRow j y =
      j.val y + m * (if 0 < j.val y then 1 else 0) := by
    filter_upwards [hxrows, hxsection] with y hy hp
    exact (hp hxJ).1.symm.trans ((hp hxJ).2.trans hy)
  have hN := S.measurableSet_rootNeighborhood j
  have hrow' : ∀ᵐ y ∂μ, S.rootChargeRow j y =
      j.val y + m * (S.rootNeighborhood j).indicator (fun _ => (1 : ℝ)) y := by
    filter_upwards [hrow, S.ae_rootNeighborhood_iff j] with y hy hiff
    rw [hy]
    by_cases h : y ∈ S.rootNeighborhood j
    · simp [h, hiff.mp h]
    · have hn : ¬0 < j.val y := fun hp => h (hiff.mpr hp)
      simp [h, hn]
  have hjint : Integrable (j.val : Ω → ℝ) μ :=
    (Lp.memLp j.val).integrable (by norm_num)
  rw [integral_congr_ae hrow', integral_add hjint
    (((integrable_const (1 : ℝ)).indicator hN).const_mul m),
    integral_const_mul, integral_indicator hN, setIntegral_const, smul_eq_mul,
    mul_one, S.row_integral_of_stationary j hW]

/-- The stationary mean row is the original gamma plus `ell` times the
entire closed missing mass, including the atom itself. -/
private theorem atom_rootChargeRow_integral_eq_closed_missing
    (S : SelectedHighLowStructure W m) (j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    (∫ y, S.rootChargeRow j y ∂μ) =
      2 * (c - m * d) + m + (-m) *
        (S.originalAtomMass j +
          μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)) := by
  have hrow := S.atom_rootChargeRow_integral_eq j hW hd hgap
  have hpartition := S.rootNeighborhood_atom_missing_partition j
  have hscaled := congrArg (fun t : ℝ => m * t) hpartition
  nlinarith only [hrow, hscaled]

/-- The averaged insertion row has the same exact original stationary
mean per unit atom mass. The normalization is paid by the positive fiber. -/
theorem middleSaturatedPrivate_atomRow_normalized
    (S : SelectedHighLowStructure W m) (j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    (∫ y, S.atomRow j y ∂μ) / S.originalAtomMass j =
      2 * (c - m * d) + m + (-m) *
        (S.originalAtomMass j +
          μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val)) := by
  let a := S.originalAtomMass j
  have ha : 0 < a :=
    ENNReal.toReal_pos (S.hfibers j.val j.property).2.1.ne' (measure_ne_top μ _)
  have ha' : 0 < (μ {x | S.ρ x = j.val}).toReal := by
    simpa only [a, originalAtomMass, measureReal_def] using ha
  have hrow (y : Ω) : S.atomRow j y = a * S.rootChargeRow j y := by
    simp only [atomRow, rootChargeRow, ProbabilityTheory.cond, integral_smul_measure,
      smul_eq_mul, ENNReal.toReal_inv, a, originalAtomMass, measureReal_def]
    rw [← mul_assoc, mul_inv_cancel₀ ha'.ne', one_mul]
  have hint : (∫ y, S.atomRow j y ∂μ) =
      a * (∫ y, S.rootChargeRow j y ∂μ) := by
    simp_rw [hrow]
    rw [integral_const_mul]
  apply (div_eq_iff ha.ne').mpr
  rw [hint, S.atom_rootChargeRow_integral_eq_closed_missing j hW hd hgap]
  ring

/-- The normalized insertion row is `γ + ell*w` for the exact atom,
saturated-head, and extra-hole masses in the all-order test. -/
theorem middleSaturatedPrivateHighRegion_atomRow_normalized
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    (∫ y, S.atomRow j y ∂μ) / S.originalAtomMass j =
      2 * (c - m * d) + m + (-m) *
        (S.originalAtomMass j + S.originalAtomMass p +
          μ.real (S.atomExtraHole j p)) := by
  rw [S.middleSaturatedPrivate_atomRow_normalized j hW hd hgap,
    S.middleSaturatedPrivateHighRegion_missing_mass_eq i p j hW hpos]
  ring

/-- HIGH peak slack removes every order-two first-root parent from the
same physical primal, so the insertion excess equals the counted excess. -/
theorem PrivatePhysicalPrimal.positiveRootExcess_eq_rootExcess
    {i p : S.I} {d c : ℝ} (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) :
    P.positiveRootExcess = P.rootExcess := by
  have htwo := P.orderRootLeaves_two_first_eq_zero hW hd hgap hell hhigh
  have hnull := PhysicalPrimal.order_two_root_event_null (P.laws 2)
    {x | S.ρ x = i.val} (S.hfibers i.val i.property).1 htwo
  have heq : {v : Fin 2 → Ω | ∃ j, S.ρ (v j) = i.val} =
      {v | ∃ j, v j ∈ {x | S.ρ x = i.val}} := by
    ext v
    simp
  rw [P.positiveRootExcess_eq, measureReal_def]
  change P.rootExcess +
    ((P.laws 2) {v : Fin 2 → Ω | ∃ j, S.ρ (v j) = i.val}).toReal = P.rootExcess
  rw [heq, hnull,
    ENNReal.toReal_zero, add_zero]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The exact same-law first-root count identifies the failed-insertion
coefficient with `R`, including the full order-two correction. -/
theorem PrivatePhysicalPrimal.rootDeficit_eq_saturated_formula
    {i p : S.I} {c : ℝ} (P : S.PrivatePhysicalPrimal i p c) :
    μ.real {x | S.ρ x = i.val} ^ 2 -
        (∑ n ∈ Finset.range (P.orderCap + 1),
          (P.laws n).real (firstRootEvent S i n)) =
      (μ.real {x | S.ρ x = i.val} *
        (3 * μ.real {x | S.ρ x = i.val} +
          μ.real {x | S.ρ x = p.val} - 1) + P.rootExcess) / 2 := by
  let M := ∑ n ∈ Finset.range (P.orderCap + 1),
    (P.laws n).real (firstRootEvent S i n)
  have hcount := P.first_root_count
  have hL := P.rootExcess_eq_sum
  have hML : (∑ n ∈ Finset.range (P.orderCap + 1),
      ((n : ℝ) - 1) * (P.laws n).real (firstRootEvent S i n)) =
      P.rootExcess + 2 * M := by
    rw [hL]
    simp only [M, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  nlinarith only [hcount, hML]

/-- The same actual physical primal gives the failed-insertion
inequality for every positive whole atom of the full HIGH hole. -/
theorem PrivatePhysicalPrimal.failed_insertion_highRegion_atom
    {i p : S.I} {d c : ℝ} (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (j : S.I)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    (μ.real {x | S.ρ x = i.val} - μ.real {x | S.ρ x = j.val}) *
        (2 * (c - m * d) + m + (-m) *
          (S.originalAtomMass j + S.originalAtomMass p +
            μ.real (S.atomExtraHole j p))) -
        μ.real {x | S.ρ x = i.val} * μ.real (S.atomExtraHole j p) - P.rootExcess ≤
      ((μ.real {x | S.ρ x = i.val} *
            (3 * μ.real {x | S.ρ x = i.val} +
              μ.real {x | S.ρ x = p.val} - 1) + P.rootExcess) / 2 +
          μ.real {x | S.ρ x = i.val} * μ.real (S.atomExtraHole j p)) *
        ((∫ x in {x | S.ρ x = j.val}, S.rootChargeRow i x ∂μ) /
          μ.real {x | S.ρ x = j.val}) := by
  obtain ⟨hji, hjp, _, _⟩ := S.middleSaturatedPrivateHighRegion_atom i p j hW hpos
  have hJP := S.ae_middleSaturatedPrivateHighRegion_atom_off_head i p j hW hpos
  have h := P.failed_insertion_atom_normalized hW hd hgap hell.le
    hprivate j hji hjp hJP
  have hZ : (∫ y, S.atomRow j y ∂μ) / μ.real {x | S.ρ x = j.val} =
      2 * (c - m * d) + m + (-m) *
        (S.originalAtomMass j + S.originalAtomMass p +
          μ.real (S.atomExtraHole j p)) := by
    simpa only [originalAtomMass] using
      (S.middleSaturatedPrivateHighRegion_atomRow_normalized i p j hW hd hgap hpos)
  rw [hZ, P.positiveRootExcess_eq_rootExcess hW hd hgap hell hhigh] at h
  rw [P.rootDeficit_eq_saturated_formula] at h
  exact h

/-- The scalar insertion star is exactly the constant original atomic
charge block, so a positive scalar star holds on the entire fiber AE. -/
theorem middleSaturatedPrivate_atomStar_eq_atomicCharge
    (S : SelectedHighLowStructure W m) (i j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    ((∫ x in {x | S.ρ x = j.val}, S.rootChargeRow i x ∂μ) /
        S.originalAtomMass j) =
      S.coveredCountableBoundaryCoefficient (Sum.inl i) (Sum.inl j) := by
  have hconst := S.ae_atomic_rootChargeRow i j hW hd hgap
  have ha : 0 < S.originalAtomMass j :=
    ENNReal.toReal_pos (S.hfibers j.val j.property).2.1.ne' (measure_ne_top μ _)
  have hint : (∫ x in {x | S.ρ x = j.val}, S.rootChargeRow i x ∂μ) =
      S.originalAtomMass j *
        S.coveredCountableBoundaryCoefficient (Sum.inl i) (Sum.inl j) := by
    rw [integral_congr_ae hconst, setIntegral_const, smul_eq_mul]
    rfl
  rw [hint, mul_div_cancel_left₀ _ ha.ne']

/-- On an original atom, the physical missing-row mass is the atom's
own mass plus its entire closed missing set. -/
theorem ae_middleSaturatedPrivate_atom_missing_mass
    (S : SelectedHighLowStructure W m) (j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      μ.real {y | PhysicalRepresentative.adjacency W m x y = false} =
        S.originalAtomMass j +
          μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
  let N := S.rootNeighborhood j
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood j
  have hrow := Measure.ae_ae_of_ae_prod (S.ae_root_adjacency j hW hd hgap)
  filter_upwards [ae_restrict_of_ae hrow,
    ae_restrict_mem (S.hfibers j.val j.property).1] with x hx hJ
  have heq : {y | PhysicalRepresentative.adjacency W m x y = false} =ᵐ[μ] Nᶜ := by
    filter_upwards [hx] with y hy
    have h := hy hJ
    cases hb : PhysicalRepresentative.adjacency W m x y <;>
      simp_all [N, Set.mem_compl_iff]
  rw [measureReal_congr heq, measureReal_compl hN, probReal_univ]
  have hpart := S.rootNeighborhood_atom_missing_partition j
  linarith

/-- The fresh-point forbidden mass on a HIGH atom is exactly the
redirected whole-atom square mass, including the atom's own fiber. -/
theorem ae_middleSaturatedPrivateHighRegion_atom_forbidden_mass
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) =
        S.originalAtomMass j +
          μ.real (KernelOperator.wholeFiberMissingSet S.ρ j.val) := by
  have hJP := S.ae_middleSaturatedPrivateHighRegion_atom_off_head i p j hW hpos
  have hmissing := ae_restrict_of_ae (s := {x | S.ρ x = j.val})
    (S.ae_missing_mass_eq_second_add_diffuseExtraHole p hW hd hgap)
  have hclosed := S.ae_middleSaturatedPrivate_atom_missing_mass j hW hd hgap
  filter_upwards [hJP, hmissing, hclosed] with x hxP hxM hxC
  exact (hxM hxP).symm.trans hxC

/-- The quantitative fresh-point insertion applies across the entire
HIGH hole. Its forbidden mass includes the point's own atom when present. -/
theorem PrivatePhysicalPrimal.ae_failed_insertion_highRegion
    {i p : S.I} {d c : ℝ} (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ, x ∈ S.middleSaturatedPrivateHighRegion i p →
      ((μ.real {y | S.ρ y = i.val} *
            (3 * μ.real {y | S.ρ y = i.val} +
              μ.real {y | S.ρ y = p.val} - 1) + P.rootExcess) / 2 +
          μ.real {y | S.ρ y = i.val} * μ.real (S.diffuseExtraHole p x)) *
          S.rootChargeRow i x ≥
        μ.real {y | S.ρ y = i.val} *
          (2 * (c - m * d) + m + (-m) *
            (μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x))) -
          μ.real {y | S.ρ y = i.val} * μ.real (S.diffuseExtraHole p x) -
          P.rootExcess := by
  have h := P.failed_insertion_diffuse hW hd hgap hell.le hprivate
  rw [P.positiveRootExcess_eq_rootExcess hW hd hgap hell hhigh,
    P.rootDeficit_eq_saturated_formula] at h
  filter_upwards [h] with x hx hK
  exact hx (fun hi => hK.2.1 (Or.inl hi))
    (fun hp => hK.2.1 (Or.inr hp)) hK.2.2

/-- A positive whole HIGH-hole atom obeys the same fresh-point radius
cap as the diffuse section, including its own missing fiber. -/
theorem ae_middleSaturatedPrivate_atom_forbidden_radius
    (S : SelectedHighLowStructure W m) (i p j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hell : 2 / 3 < -m) (T : ℝ) (hT : 0 ≤ T)
    (hTcap : (-m - 2 / 3) * T ^ 2 =
      (-1 + 8 * S.originalAtomMass i -
        (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 -
          (2 * (c - m * d) + m))
    (hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
      {x | S.ρ x = j.val})) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) ≤ T := by
  have hcap := S.middleSaturatedPrivateHighRegion_atom_sharp_budget i p j
    hW hd hgap hpeak hnonlow hA hell.le hpos
  have hforbid := S.ae_middleSaturatedPrivateHighRegion_atom_forbidden_mass
    i p j hW hd hgap hpos
  filter_upwards [hforbid] with x hx
  have hw : 0 ≤ μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) :=
    add_nonneg (measureReal_nonneg) (measureReal_nonneg)
  rw [← hx] at hcap
  by_contra hn
  have hsq : T ^ 2 <
      (μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x)) ^ 2 := by
    nlinarith only [hT, hw, lt_of_not_ge hn]
  have hcoef : 0 < -m - 2 / 3 := by linarith only [hell]
  have hmul := mul_lt_mul_of_pos_left hsq hcoef
  linarith only [hcap, hTcap, hmul]

/-- The sharp diffuse excess estimate gives the same forbidden-mass
radius on genuine diffuse points of the full HIGH hole. -/
theorem ae_middleSaturatedPrivate_dust_forbidden_radius
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hell : 2 / 3 < -m) (T : ℝ)
    (hT : 0 ≤ T) (hTA : T < S.originalAtomMass i)
    (hTcap : (-m - 2 / 3) * T ^ 2 =
      (-1 + 8 * S.originalAtomMass i -
        (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 -
          (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.middleSaturatedPrivateHighRegion i p →
      μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) ≤ T := by
  let A := S.originalAtomMass i
  let D := (-1 + 8 * A - (7 + 6 * (-m)) * A ^ 2) / 6
  let γ := 2 * (c - m * d) + m
  have hcoef : 0 < -m - 2 / 3 := by linarith only [hell]
  have hdust : ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.H → S.outsideSectionMass x ≤ T := by
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, x ∈ S.D → x ∈ S.H →
        S.outsideSectionMass x ≤ T + (A - T) / ((n : ℝ) + 2) := by
      rw [ae_all_iff]
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hstep : 0 < (A - T) / ((n : ℝ) + 2) :=
        div_pos (by linarith only [hTA]) hn
      have hstepA : (A - T) / ((n : ℝ) + 2) ≤ A - T := by
        rw [div_le_iff₀ hn]
        nlinarith only [hTA, hn, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hRpos : 0 < T + (A - T) / ((n : ℝ) + 2) := by
        linarith only [hT, hstep]
      have hmargin : D < γ + (-m - 2 / 3) *
          (T + (A - T) / ((n : ℝ) + 2)) ^ 2 := by
        have hsq : T ^ 2 < (T + (A - T) / ((n : ℝ) + 2)) ^ 2 := by
          nlinarith only [hT, hstep]
        have hmul := mul_lt_mul_of_pos_left hsq hcoef
        change (-m - 2 / 3) * T ^ 2 = D - γ at hTcap
        linarith only [hTcap, hmul]
      exact S.ae_middle_diffuse_high_outside_le i hW hd hgap hpeak hnonlow
        hA hell.le hRpos (by linarith only [hstepA]) hmargin
    filter_upwards [hall] with x hx hxD hxH
    by_contra hlt
    have hδ : 0 < S.outsideSectionMass x - T := by
      linarith only [lt_of_not_ge hlt]
    obtain ⟨n, hn⟩ := exists_nat_gt ((A - T) / (S.outsideSectionMass x - T))
    have hbound := hx n hxD hxH
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hlarge : A - T < (S.outsideSectionMass x - T) * ((n : ℝ) + 2) := by
      rw [div_lt_iff₀ hδ] at hn
      nlinarith only [hn, hδ]
    have hsmall : (A - T) / ((n : ℝ) + 2) < S.outsideSectionMass x - T := by
      rw [div_lt_iff₀ hn2]
      exact hlarge
    linarith only [hbound, hsmall]
  have hrows := S.ae_diffuse_missing_row_le_outside hW hd hgap
  have hmass := S.ae_missing_row_eq_second_add_diffuseExtraHole p hW hd hgap
  filter_upwards [hdust, hrows, hmass] with x hxD hxR hxM hxS hxK
  have hxH : x ∈ S.H := hxK.1
  have hxN : x ∉ S.rootNeighborhood p := hxK.2.2
  linarith only [hxD hxS hxH, hxR hxS, hxM hxN]

/-- One sharp radius bounds the actual forbidden mass on every point of
the complete HIGH hole, both whole atoms and genuine diffuse points. -/
theorem ae_middleSaturatedPrivate_forbidden_radius
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∉ S.L)
    (hA : S.originalAtomMass i ∈ Icc (1 / 4 : ℝ) (1 / 3))
    (hell : 2 / 3 < -m) (T : ℝ)
    (hT : 0 ≤ T) (hTA : T < S.originalAtomMass i)
    (hTcap : (-m - 2 / 3) * T ^ 2 =
      (-1 + 8 * S.originalAtomMass i -
        (7 + 6 * (-m)) * (S.originalAtomMass i) ^ 2) / 6 -
          (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ, x ∈ S.middleSaturatedPrivateHighRegion i p →
      μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) ≤ T := by
  let _ : Countable S.I := S.hI.to_subtype
  have hatoms : ∀ᵐ x ∂μ, ∀ j : S.I,
      x ∈ S.middleSaturatedPrivateHighRegion i p → S.ρ x = j.val →
        μ.real {y | S.ρ y = p.val} + μ.real (S.diffuseExtraHole p x) ≤ T := by
    rw [ae_all_iff]
    intro j
    by_cases hpos : 0 < μ (S.middleSaturatedPrivateHighRegion i p ∩
        {x | S.ρ x = j.val})
    · have hbound := (ae_restrict_iff' (S.hfibers j.val j.property).1).mp
        (S.ae_middleSaturatedPrivate_atom_forbidden_radius i p j hW hd hgap
          hpeak hnonlow hA hell T hT hTcap hpos)
      exact hbound.mono (fun _ hx _ hJ => hx hJ)
    · have hz : μ (S.middleSaturatedPrivateHighRegion i p ∩
          {x | S.ρ x = j.val}) = 0 :=
        le_antisymm (le_of_not_gt hpos) zero_le
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx hK hJ
      exact False.elim (hx ⟨hK, hJ⟩)
  have hdust := S.ae_middleSaturatedPrivate_dust_forbidden_radius i p hW hd hgap
    hpeak hnonlow hA hell T hT hTA hTcap
  filter_upwards [hatoms, hdust] with x hx hd hK
  by_cases hxD : x ∈ S.D
  · exact hd hxD hK
  · have hx' : x ∈ ⋃ r ∈ S.I, {y | S.ρ y = r} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hxD
    obtain ⟨r, hr⟩ := mem_iUnion.mp hx'
    obtain ⟨hrI, hxr⟩ := mem_iUnion.mp hr
    exact hx ⟨r, hrI⟩ hK hxr

end Erdos1017.CappedModel.SelectedHighLowStructure
