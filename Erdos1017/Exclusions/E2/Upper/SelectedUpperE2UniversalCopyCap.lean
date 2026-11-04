module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalGeometry
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPrice
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalBadTopology

/-!
# Copy caps for the universal root

Under the scalar price guard an original hole-to-bad charge is at most the
multiplier magnitude, saturation of the root-partner edge leaves nonpositive
charge from the partner to every good recipient, and the common-root copy
estimate bounds every positive body charge on the large-mass price branch.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem ae_prod_restrict_imp (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (P : Ω × Ω → Prop)
    (h : ∀ᵐ q ∂(μ.restrict A).prod (μ.restrict B), P q) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ A → q.2 ∈ B → P q := by
  rw [Measure.prod_restrict] at h
  exact ((ae_restrict_iff' (hA.prod hB)).mp h).mono
    (fun _ hq ha hb => hq ⟨ha, hb⟩)

private theorem missingSection_mass_eq_one_sub_degree (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G)) (x : Ω) :
    μ.real (missingSection G x) =
      1 - ∫ z, (if G x z = true then (1 : ℝ) else 0) ∂μ := by
  let E := {z | G x z = true}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun (hG.comp (measurable_const.prodMk measurable_id)) measurable_const
  have hM : missingSection G x = Eᶜ := by
    ext z
    cases h : G x z <;> simp [missingSection, E, h]
  rw [hM, measureReal_compl hE, probReal_univ]
  have he : E.indicator (fun _ => (1 : ℝ)) =
      fun z => if G x z = true then 1 else 0 := by
    funext z
    simp [Set.indicator, E]
  rw [← he, integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]

private theorem missing_row_le_mass (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (hbound : ∀ x y, ‖Y x y‖ ≤ 3)
    (P : Set Ω) (hP : MeasurableSet P) (x y : Ω) (v ell : ℝ)
    (hell : 0 ≤ ell)
    (hrow : ∀ᵐ z ∂μ, G x z = false →
      (z ∈ P → Y y z ≤ ell) ∧ (z ∉ P → Y y z ≤ v)) :
    (∫ z in missingSection G x, Y y z ∂μ) ≤
      v * μ.real (missingSection G x \ P) + ell * μ.real P := by
  let M := missingSection G x
  have hM : MeasurableSet M := measurableSet_missingSection G hG x
  have hMP : MeasurableSet (M \ P) := hM.diff hP
  have hYi : Integrable (Y y) μ := Integrable.of_bound
    (hY.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    (Eventually.of_forall (hbound y))
  have hIM : Integrable ((M \ P).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hMP
  have hIP : Integrable (P.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hP
  have hle : M.indicator (Y y) ≤ᵐ[μ]
      fun z => v * (M \ P).indicator (fun _ => (1 : ℝ)) z +
        ell * P.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [hrow] with z hz
    by_cases hm : z ∈ M
    · have hg : G x z = false := hm
      by_cases hp : z ∈ P
      · simpa [Set.indicator, hm, hp] using (hz hg).1 hp
      · simpa [Set.indicator, hm, hp] using (hz hg).2 hp
    · by_cases hp : z ∈ P <;> simp [Set.indicator, hm, hp, hell]
  have hi := integral_mono_ae (hYi.indicator hM)
    ((hIM.const_mul v).add (hIP.const_mul ell)) hle
  change (∫ z, M.indicator (Y y) z ∂μ) ≤
    ∫ z, v * (M \ P).indicator (fun _ => (1 : ℝ)) z +
      ell * P.indicator (fun _ => (1 : ℝ)) z ∂μ at hi
  rw [integral_add (hIM.const_mul v) (hIP.const_mul ell),
    integral_const_mul, integral_const_mul] at hi
  simp only [integral_indicator hM, integral_indicator hMP, integral_indicator hP,
    setIntegral_const, smul_eq_mul, mul_one] at hi
  exact hi

end Erdos1017.IndependentAtomCopy

namespace Erdos1017.CappedModel.SelectedHighLowStructure

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m c : ℝ}

private theorem ae_physical_missing_mass_le_of_original_degree_ge
    {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (B : Set Ω) (t : ℝ)
    (hdegree : ∀ᵐ x ∂μ.restrict B, t ≤ ∫ z, adjacencyKernel W x z ∂μ) :
    ∀ᵐ x ∂μ.restrict B,
      μ.real (IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) x) ≤ 1 - t := by
  have hsections := Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)
  filter_upwards [hdegree, ae_restrict_of_ae hsections] with x hx hsec
  have heq : (∫ z, (if PhysicalRepresentative.adjacency W m x z = true
      then (1 : ℝ) else 0) ∂μ) = ∫ z, adjacencyKernel W x z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hsec] with z hz
    exact hz.symm
  rw [IndependentAtomCopy.missingSection_mass_eq_one_sub_degree
    (PhysicalRepresentative.adjacency W m)
    (PhysicalRepresentative.measurable_adjacency W m) x, heq]
  linarith

private theorem ae_physical_missing_same_atom_or_relation
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ q ∂μ.prod μ,
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        q ∈ S.sameAtomRelation ∨ q ∈ actualZeroRelation W m S.ρ := by
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  filter_upwards [hW.moment_mem, hs,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs,
    S.ae_zero_iff_sameAtom_or_relation hW hd hgap]
    with q hmem hsupport hphysical hzero hG
  have hA : adjacencyKernel W q.1 q.2 = 0 := by
    change adjacencyKernel W q.1 q.2 = _ at hphysical
    rw [hphysical, hG]
    norm_num
  have hM : shiftedKernel W m q.1 q.2 = 0 := by
    change shiftedMoment W m q = 0
    change W.moment CappedColor.adjacency q =
      if 0 < shiftedMoment W m q then 1 else 0 at hsupport
    have hn : ¬0 < shiftedMoment W m q := by
      intro hpos
      rw [ite_eq_left hpos] at hsupport
      change W.moment CappedColor.adjacency q = 0 at hA
      linarith
    exact le_antisymm (le_of_not_gt hn) hmem.1
  exact (hzero.mp hM)

private theorem ae_partner_fiber_missing_on_universalHole
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      ∀ᵐ z ∂μ.restrict {z | S.ρ z = p.val},
        PhysicalRepresentative.adjacency W m x z = false := by
  let H := S.universalPartnerHoleRegion r p
  let P := {z | S.ρ z = p.val}
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hP := (S.hfibers p.val p.property).1
  have hprod : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict H),
      PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
    have hle : (μ.restrict P).prod (μ.restrict H) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [ae_mono hle (S.ae_root_adjacency p hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hH)]
      with q hrow hp hh
    by_cases hA : PhysicalRepresentative.adjacency W m q.1 q.2
    · exact False.elim (hh (Or.inr ((hrow hp).mp hA)))
    · exact Bool.eq_false_iff.mpr hA
  have hswap := (Measure.measurePreserving_swap
    (μ := μ.restrict H) (ν := μ.restrict P)).quasiMeasurePreserving.ae hprod
  have hprod' : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict P),
      PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
    filter_upwards [hswap] with q hq
    change PhysicalRepresentative.adjacency W m q.2 q.1 = false at hq
    simpa [PhysicalRepresentative.adjacency_symm W m q.1 q.2] using hq
  exact Measure.ae_ae_of_ae_prod hprod'

private theorem ae_universalHole_physical_missing_except_partner_le
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      μ.real (IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) x \ {z | S.ρ z = p.val}) ≤
          1 - 2 * S.originalAtomMass r - S.originalAtomMass p := by
  let H := S.universalPartnerHoleRegion r p
  let P := {z | S.ρ z = p.val}
  let G := PhysicalRepresentative.adjacency W m
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hP := (S.hfibers p.val p.property).1
  have hV := ((S.hfibers r.val r.property).1.union hP).compl
  have hdeg : ∀ᵐ x ∂μ.restrict H,
      2 * S.originalAtomMass r ≤ ∫ z, adjacencyKernel W x z ∂μ := by
    apply (ae_restrict_iff' hH).mpr
    filter_upwards [(ae_restrict_iff' hV).mp
      (S.ae_universalPartner_exterior_degree_ge_twice_mass r p hpair hW hd hgap hell hN)]
      with x hx hHx
    exact hx (fun hmem => hHx (Or.inl hmem))
  have hM := ae_physical_missing_mass_le_of_original_degree_ge hW hd hgap H
    (2 * S.originalAtomMass r) hdeg
  have hPM := S.ae_partner_fiber_missing_on_universalHole r p hW hd hgap
  filter_upwards [hM, hPM] with x hx hpx
  let M := IndependentAtomCopy.missingSection G x
  have hMset := IndependentAtomCopy.measurableSet_missingSection G
    (PhysicalRepresentative.measurable_adjacency W m) x
  have heq : μ.real (M ∩ P) = μ.real P := by
    have hAE : (M ∩ P) =ᵐ[μ] P := by
      apply ((ae_restrict_iff' hP).mp hpx).mono
      intro z hz
      apply propext
      exact ⟨fun h => h.2, fun hp => ⟨hz hp, hp⟩⟩
    exact congrArg ENNReal.toReal (measure_congr hAE)
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := M) hP
  rw [heq] at hsplit
  change μ.real M ≤ 1 - 2 * S.originalAtomMass r at hx
  change μ.real (M \ P) ≤ _
  have hPeq : μ.real P = S.originalAtomMass p := rfl
  rw [hPeq] at hsplit
  linarith

private theorem UniversalPhysicalPrimal.ae_universalBad_physical_missing_mass_le
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalUpperE2BadRegion r p d c),
      μ.real (IndependentAtomCopy.missingSection
        (PhysicalRepresentative.adjacency W m) x) ≤
          1 - 3 * S.originalAtomMass r + S.originalAtomMass p := by
  have hdegree := P.ae_universalUpperE2Bad_originalDegree_ge S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  filter_upwards [ae_physical_missing_mass_le_of_original_degree_ge hW hd hgap
    (S.universalUpperE2BadRegion r p d c)
    (3 * S.originalAtomMass r - S.originalAtomMass p) hdegree] with x hx
  linarith

private theorem universal_copy_cap_scalar {A b γ ell v : ℝ}
    (hA : 1 / 3 < A)
    (hcopy : (6 * A - 2) * v + γ ≤ b * ell)
    (hprice : b * ell - γ ≤ ell * (6 * A - 2)) : v ≤ ell := by
  have hcoef : 0 < 6 * A - 2 := by linarith
  nlinarith

private theorem universal_copy_budget_scalar {A b γ ell v m rh rb j : ℝ}
    (hm : m ≤ 0) (hj : 0 ≤ j)
    (hcopy : A * v + γ - m * j ≤ rh + rb)
    (hrowH : rh ≤ v * (1 - 2 * A - b) + b * ell)
    (hrowB : rb ≤ v * (1 - 3 * A + b)) :
    (6 * A - 2) * v + γ ≤ b * ell := by
  have hnonneg : 0 ≤ -m * j := mul_nonneg (by linarith) hj
  nlinarith

/-- On a copied H row, every physical missing recipient belongs to the
partner fiber, the same original whole atom, or the common region outside the bad region. -/
theorem UniversalPhysicalPrimal.ae_universalHole_missing_recipient_class
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        S.ρ q.2 = p.val ∨ q ∈ S.sameAtomRelation ∨
          q.2 ∈ S.universalPartnerCommonRegion r p \
            S.universalUpperE2BadRegion r p d c := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let U := S.universalPartnerCommonRegion r p
  let I := {x | S.ρ x = r.val}
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hI := (S.hfibers r.val r.property).1
  have hHigh := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell.2)
  have hNeutral := (ae_restrict_iff' hI).mp hN
  have hHL : Disjoint S.H S.L := S.hpartition.2.2.2.2.1
  have hLN : Disjoint S.L S.N := S.hpartition.2.2.2.2.2.2
  filter_upwards [S.ae_physical_missing_same_atom_or_relation hW hd hgap,
    S.hrelation, P.ae_universalUpperE2_hole_bad_join S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
    Measure.quasiMeasurePreserving_fst.ae hHigh,
    Measure.quasiMeasurePreserving_snd.ae hHigh,
    Measure.quasiMeasurePreserving_snd.ae hNeutral]
    with q hzero hrel hjoin hphysical hxHigh hzHigh hzNeutral hx hG
  rcases hzero hG with hSame | hZ
  · exact Or.inr (Or.inl hSame)
  have hxS : q.1 ∈ S.H := hxHigh hx
  have hzL : q.2 ∈ S.L := by
    rcases hrel hZ with hcross | hcross
    · exact hcross.2.1
    · exact False.elim ((Set.disjoint_left.mp hHL) hxS hcross.2.1)
  by_cases hzP : S.ρ q.2 = p.val
  · exact Or.inl hzP
  have hzI : S.ρ q.2 ≠ r.val := by
    intro hr
    exact (Set.disjoint_left.mp hLN) hzL (hzNeutral hr)
  have hzH : q.2 ∉ H := by
    intro hh
    exact (Set.disjoint_left.mp hHL) (hzHigh hh) hzL
  have hzB : q.2 ∉ B := by
    intro hb
    have hA : adjacencyKernel W q.1 q.2 = 1 := hjoin hx hb
    change adjacencyKernel W q.1 q.2 = _ at hphysical
    rw [hphysical, hG] at hA
    norm_num at hA
  exact Or.inr (Or.inr ⟨by
    change q.2 ∉ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪ H
    intro h
    rcases h with (h | h) | h
    · exact hzI h
    · exact hzP h
    · exact hzH h, hzB⟩)

/-- A bad row can miss only its own original atom or the good common
region; the partner joins the bad region, and H joins it by actual degree order. -/
theorem UniversalPhysicalPrimal.ae_universalBad_missing_recipient_class
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalUpperE2BadRegion r p d c →
      PhysicalRepresentative.adjacency W m q.1 q.2 = false →
        q ∈ S.sameAtomRelation ∨
          q.2 ∈ S.universalGoodCommonRegion r p d c := by
  let B := S.universalUpperE2BadRegion r p d c
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let I := {z | S.ρ z = r.val}
  have hI := (S.hfibers r.val r.property).1
  have hU := S.measurableSet_universalPartnerCommonRegion r p
  have hbad := P.ae_universalUpperE2Bad_subset_common S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin
  have hPpos := (ae_restrict_iff' hU).mp
    (S.ae_partner_row_pos_on_universalCommon r p)
  have hneutral := (ae_restrict_iff' hI).mp hN
  have hzero := S.ae_physical_missing_same_atom_or_relation hW hd hgap
  have hbadSame := P.ae_universalUpperE2Bad_missing_iff_sameAtom S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hjoin := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (P.ae_universalUpperE2_hole_bad_join S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hPhysical := PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  have hroot := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency p hW hd hgap)
  filter_upwards [hzero, hbadSame, hjoin, hPhysical, hroot,
    adjacencyKernel_symm W, S.hrelation,
    Measure.quasiMeasurePreserving_fst.ae hbad,
    Measure.quasiMeasurePreserving_fst.ae hPpos,
    Measure.quasiMeasurePreserving_snd.ae hneutral]
    with q hzero hbadSame hjoin hphysical hroot hsym hrel hbc hpPos hnI hb hG
  have hUq : q.1 ∈ U := hbc hb
  have hnotr : S.ρ q.1 ≠ r.val := fun h => hb.1 (Or.inl h)
  have hnotp : S.ρ q.1 ≠ p.val := fun h => hb.1 (Or.inr h)
  have hNp : q.1 ∈ S.rootNeighborhood p := by
    exact ⟨hnotp, hpPos hUq⟩
  by_cases hzB : q.2 ∈ B
  · have hA : adjacencyKernel W q.1 q.2 = 0 := by
      change adjacencyKernel W q.1 q.2 = _ at hphysical
      rw [hphysical, hG]
      norm_num
    exact Or.inl ((hbadSame hb hzB).mp hA)
  have hzI : S.ρ q.2 ≠ r.val := by
    intro hzr
    rcases hzero hG with hAtom | hZ
    · exact hnotr (hAtom.1.trans hzr)
    · rcases hrel hZ with hcross | hcross
      · exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2) hcross.2.1 (hnI hzr)
      · exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1) hcross.1 (hnI hzr)
  have hzP : S.ρ q.2 ≠ p.val := by
    intro hzp
    have hr := hroot hzp
    change PhysicalRepresentative.adjacency W m q.2 q.1 = true ↔
      q.1 ∈ S.rootNeighborhood p at hr
    have htrue := hr.mpr hNp
    rw [PhysicalRepresentative.adjacency_symm W m] at htrue
    rw [hG] at htrue
    contradiction
  have hzH : q.2 ∉ H := by
    intro hh
    have hj : adjacencyKernel W q.2 q.1 = 1 := hjoin hh hb
    have hA : adjacencyKernel W q.1 q.2 = 0 := by
      change adjacencyKernel W q.1 q.2 = _ at hphysical
      rw [hphysical, hG]
      norm_num
    rw [hsym] at hA
    linarith
  exact Or.inr ⟨by
    change q.2 ∉ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪ H
    intro h
    rcases h with (h | h) | h
    · exact hzI h
    · exact hzP h
    · exact hzH h, hzB⟩

/-- Homogeneous original whole rows give the same physical charge to
two recipients in one original atom, including diffuse exterior sources. -/
theorem ae_physical_charge_eq_on_sameAtom
    (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ q ∂μ.prod μ, ∀ᵐ z ∂μ,
      (q.1, z) ∈ S.sameAtomRelation →
        PhysicalRepresentative.charge W m q.2 z =
          PhysicalRepresentative.charge W m q.2 q.1 := by
  let Y := PhysicalRepresentative.charge W m
  let : Countable S.I := S.hI.to_subtype
  have hrows : ∀ᵐ q ∂μ.prod μ, ∀ i : S.I,
      S.ρ q.1 = i.val → Y q.2 q.1 = S.rootChargeRow i q.2 := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [S.ae_root_charge i hW hd hgap] with q hq hr
    change PhysicalRepresentative.charge W m q.2 q.1 = S.rootChargeRow i q.2
    rw [PhysicalRepresentative.charge_symm W m q.2 q.1]
    exact hq hr
  have hcolumns : ∀ᵐ q ∂μ.prod μ, ∀ i : S.I,
      ∀ᵐ z ∂μ, S.ρ z = i.val → Y q.2 z = S.rootChargeRow i q.2 := by
    apply ae_all_iff.mpr
    intro i
    have hswapped := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_root_charge i hW hd hgap)
    have hcolumns : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
        S.ρ z = i.val → Y y z = S.rootChargeRow i y := by
      have hsec := Measure.ae_ae_of_ae_prod hswapped
      filter_upwards [hsec] with y hy
      filter_upwards [hy] with z hz hr
      change S.ρ z = i.val → Y z y = S.rootChargeRow i y at hz
      change PhysicalRepresentative.charge W m y z = S.rootChargeRow i y
      rw [PhysicalRepresentative.charge_symm W m y z]
      exact hz hr
    exact Measure.quasiMeasurePreserving_snd.ae hcolumns
  filter_upwards [hrows, hcolumns] with q hrow hcol
  filter_upwards [(ae_all_iff).mpr hcol] with z hz hsame
  let i : S.I := ⟨S.ρ q.1, hsame.2⟩
  have hx : S.ρ q.1 = i.val := rfl
  have hz' : S.ρ z = i.val := hsame.1.symm
  exact (hz i hz').trans (hrow i hx).symm

/-- The actual rooted triangle bounds the positive H-to-good-common
charge by the same endpoint allowance used for bad-to-good-common pairs. -/
theorem UniversalPhysicalPrimal.ae_hole_good_charge_le_endpoint
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂(μ.restrict (S.universalPartnerHoleRegion r p)).prod
      (μ.restrict (S.universalGoodCommonRegion r p d c)),
        chargeKernel W q.1 q.2 ≤
          max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
            (1 + m))) 0 := by
  let H := S.universalPartnerHoleRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  let θ := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  let Y := PhysicalRepresentative.charge W m
  let G := PhysicalRepresentative.adjacency W m
  have hApos : 0 < S.originalAtomMass r := by linarith
  have hθ : 1 + m < θ := by
    have hh : 2 * (1 + m) <
        3 * (2 * (c - m * d) + m) / S.originalAtomMass r := by
      apply (lt_div_iff₀ hApos).mpr
      nlinarith [hmargin]
    dsimp [θ]
    linarith
  have hHθ := P.ae_universal_upperE2_hole_star_threshold S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hrestricted : (μ.restrict H).prod (μ.restrict Good) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hrestricted (S.ae_universal_root_triangle r hW hd hgap hN),
    ae_mono hrestricted
      (PhysicalRepresentative.charge_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support),
    Measure.quasiMeasurePreserving_fst.ae hHθ,
    Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (S.measurableSet_universalPartnerHoleRegion r p)),
    Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (S.measurableSet_universalGoodCommonRegion r p d c))]
    with q htri hY hxθ hxH hzGood
  have hzθ : θ ≤ S.rootChargeRow r q.2 := by
    apply le_of_not_gt
    intro hh
    exact hzGood.2 ⟨by
      intro hhead
      exact hzGood.1 (Or.inl hhead), hh⟩
  have hxi : S.ρ q.1 ≠ r.val := by
    intro hh
    exact hxH (Or.inl (Or.inl hh))
  have hzi : S.ρ q.2 ≠ r.val := by
    intro hh
    exact hzGood.1 (Or.inl (Or.inl hh))
  by_cases hG : G q.1 q.2 = true
  · have ht := htri hxi hzi hG
    have hbound : chargeKernel W q.1 q.2 ≤ 1 - 2 * θ := by
      rw [hY] at ht
      linarith [hxθ, hzθ]
    exact hbound.trans ((show 1 - 2 * θ ≤ -m - θ by linarith [hθ]).trans
      (le_max_left _ _))
  · have hz := PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2
      (Bool.eq_false_iff.mpr hG)
    rw [← hY, hz]
    exact le_max_right _ _

/-- The only exceptional H missing recipient is the partner fiber; its
actual physical charge is at most the original multiplier magnitude. -/
theorem UniversalPhysicalPrimal.ae_bad_partner_charge_le_multiplier
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂(μ.restrict (S.universalUpperE2BadRegion r p d c)).prod
      (μ.restrict {z | S.ρ z = p.val}),
        PhysicalRepresentative.charge W m q.1 q.2 ≤ -m := by
  let B := S.universalUpperE2BadRegion r p d c
  let F := {z | S.ρ z = p.val}
  have hB := S.measurableSet_universalUpperE2BadRegion r p d c
  have hF := (S.hfibers p.val p.property).1
  have hβ : ∀ᵐ y ∂μ.restrict B, S.rootChargeRow p y ≤ -m := by
    filter_upwards [P.ae_universalUpperE2Bad_partner_charge S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin,
      ae_restrict_mem hB,
      ae_restrict_of_ae (S.ae_universal_row_pos_on_outside r hW hd hgap hN),
      ae_restrict_of_ae (S.ae_universalRootDeficit_eq_shifted_row r hW hd hgap)]
      with y hpair' hy hpos hrow
    have hnotr : S.ρ y ≠ r.val := fun hr => hy.1 (Or.inl hr)
    have hrpos := hpos hnotr
    change 1 - S.rootChargeRow r y =
      1 - r.val y - m * (if 0 < r.val y then 1 else 0) at hrow
    rw [ite_eq_left hrpos] at hrow
    linarith [hpair']
  have hroot := S.ae_root_charge p hW hd hgap
  have hswapped := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hroot
  have hle : (μ.restrict B).prod (μ.restrict F) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hle hswapped,
    Measure.quasiMeasurePreserving_fst.ae hβ,
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hF)]
    with q hr hb hf
  change S.ρ q.2 = p.val →
    PhysicalRepresentative.charge W m q.2 q.1 = S.rootChargeRow p q.1 at hr
  rw [PhysicalRepresentative.charge_symm W m q.1 q.2]
  exact (hr hf).trans_le hb

private theorem UniversalPhysicalPrimal.ae_hole_bad_missing_row_bound
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalUpperE2BadRegion r p d c →
      max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
        (1 + m))) 0 < PhysicalRepresentative.charge W m q.1 q.2 →
      ∀ᵐ z ∂μ,
        PhysicalRepresentative.adjacency W m q.1 z = false →
          (S.ρ z = p.val → PhysicalRepresentative.charge W m q.2 z ≤ -m) ∧
          (S.ρ z ≠ p.val → PhysicalRepresentative.charge W m q.2 z ≤
            PhysicalRepresentative.charge W m q.1 q.2) := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let Good := S.universalGoodCommonRegion r p d c
  let F := {z | S.ρ z = p.val}
  let Y := PhysicalRepresentative.charge W m
  have hB := S.measurableSet_universalUpperE2BadRegion r p d c
  have hGood := S.measurableSet_universalGoodCommonRegion r p d c
  have hF := (S.hfibers p.val p.property).1
  have hBG := IndependentAtomCopy.ae_prod_restrict_imp B Good hB hGood
    (fun v => chargeKernel W v.1 v.2 ≤
      max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
        (1 + m))) 0)
    (P.ae_bad_good_charge_le_endpoint S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hBGphysical : ∀ᵐ v ∂μ.prod μ, v.1 ∈ B → v.2 ∈ Good →
      Y v.1 v.2 ≤ max (-m - (3 * (2 * (c - m * d) + m) /
        S.originalAtomMass r - (1 + m))) 0 := by
    filter_upwards [hBG, PhysicalRepresentative.charge_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with v hb he hBv hGv
    change PhysicalRepresentative.charge W m v.1 v.2 ≤ _
    rw [he]
    exact hb hBv hGv
  have hBP := IndependentAtomCopy.ae_prod_restrict_imp B F hB hF
    (fun v => Y v.1 v.2 ≤ -m)
    (P.ae_bad_partner_charge_le_multiplier S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hclass := Measure.ae_ae_of_ae_prod
    (P.ae_universalHole_missing_recipient_class S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hgood := Measure.ae_ae_of_ae_prod hBGphysical
  have hpartner := Measure.ae_ae_of_ae_prod hBP
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hclass,
    Measure.quasiMeasurePreserving_snd.ae hgood,
    Measure.quasiMeasurePreserving_snd.ae hpartner,
    S.ae_physical_charge_eq_on_sameAtom hW hd hgap]
    with q hclass hgood hpartner hsame hqH hqB hlarge
  filter_upwards [hclass, hgood, hpartner, hsame] with z hc hg hp hs hz
  rcases hc hqH hz with hzP | hsameAtom | hzGood
  · exact ⟨fun _ => hp hqB hzP, fun hn => False.elim (hn hzP)⟩
  · exact ⟨fun h => False.elim (by
      have hnotp : S.ρ q.1 ≠ p.val := fun he => hqH (Or.inl (Or.inr he))
      exact hnotp (hsameAtom.1.trans h)), fun _ =>
        (hs hsameAtom).trans_le (le_of_eq (PhysicalRepresentative.charge_symm
          W m q.2 q.1))⟩
  · exact ⟨fun h => False.elim (by
      have hnotp : S.ρ z ≠ p.val := fun he => hzGood.1 (Or.inl (Or.inr he))
      exact hnotp h), fun _ => (hg hqB hzGood).trans hlarge.le⟩

private theorem UniversalPhysicalPrimal.ae_bad_hole_missing_row_bound
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalUpperE2BadRegion r p d c →
      max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
        (1 + m))) 0 < PhysicalRepresentative.charge W m q.1 q.2 →
      ∀ᵐ z ∂μ,
        PhysicalRepresentative.adjacency W m q.2 z = false →
          PhysicalRepresentative.charge W m q.1 z ≤
            PhysicalRepresentative.charge W m q.1 q.2 := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let Good := S.universalGoodCommonRegion r p d c
  let Y := PhysicalRepresentative.charge W m
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hGood := S.measurableSet_universalGoodCommonRegion r p d c
  have hHG := IndependentAtomCopy.ae_prod_restrict_imp H Good hH hGood
    (fun v => chargeKernel W v.1 v.2 ≤
      max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
        (1 + m))) 0)
    (P.ae_hole_good_charge_le_endpoint S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hHGphysical : ∀ᵐ v ∂μ.prod μ, v.1 ∈ H → v.2 ∈ Good →
      Y v.1 v.2 ≤ max (-m - (3 * (2 * (c - m * d) + m) /
        S.originalAtomMass r - (1 + m))) 0 := by
    filter_upwards [hHG, PhysicalRepresentative.charge_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with v hb he hHv hGv
    change PhysicalRepresentative.charge W m v.1 v.2 ≤ _
    rw [he]
    exact hb hHv hGv
  have hclass := Measure.ae_ae_of_ae_prod
    (P.ae_universalBad_missing_recipient_class S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hgood := Measure.ae_ae_of_ae_prod hHGphysical
  have hsame :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_physical_charge_eq_on_sameAtom hW hd hgap)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hclass,
    Measure.quasiMeasurePreserving_fst.ae hgood, hsame]
    with q hclass hgood hsame hqH hqB hlarge
  filter_upwards [hclass, hgood, hsame] with z hc hg hs hz
  rcases hc hqB hz with hsameAtom | hzGood
  · exact le_of_eq (hs hsameAtom)
  · exact (hg hqH hzGood).trans hlarge.le

private theorem UniversalPhysicalPrimal.ae_hole_bad_charge_le_of_missing_rows
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hprice : S.originalAtomMass p * (-m) - (2 * (c - m * d) + m) ≤
      (-m) * (6 * S.originalAtomMass r - 2))
    (hrowH : ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalUpperE2BadRegion r p d c →
      max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
        (1 + m))) 0 < PhysicalRepresentative.charge W m q.1 q.2 →
      ∀ᵐ z ∂μ,
        PhysicalRepresentative.adjacency W m q.1 z = false →
          (S.ρ z = p.val → PhysicalRepresentative.charge W m q.2 z ≤ -m) ∧
          (S.ρ z ≠ p.val →
            PhysicalRepresentative.charge W m q.2 z ≤
              PhysicalRepresentative.charge W m q.1 q.2))
    (hrowB : ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalUpperE2BadRegion r p d c →
      max (-m - (3 * (2 * (c - m * d) + m) / S.originalAtomMass r -
        (1 + m))) 0 < PhysicalRepresentative.charge W m q.1 q.2 →
      ∀ᵐ z ∂μ,
        PhysicalRepresentative.adjacency W m q.2 z = false →
          PhysicalRepresentative.charge W m q.1 z ≤
            PhysicalRepresentative.charge W m q.1 q.2) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalUpperE2BadRegion r p d c →
      0 < PhysicalRepresentative.charge W m q.1 q.2 →
        PhysicalRepresentative.charge W m q.1 q.2 ≤ -m := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let F := {z | S.ρ z = p.val}
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let γ := 2 * (c - m * d) + m
  let ell := -m
  let θ := 3 * γ / A - (1 + m)
  let err := max (ell - θ) 0
  have hell0 : 0 ≤ ell := by dsimp [ell]; linarith [hell.1]
  have hθ : 0 < θ := by
    have hh : 2 * (1 + m) < 3 * γ / A := by
      apply (lt_div_iff₀ (show 0 < A by linarith [hA])).mpr
      nlinarith [hmargin]
    dsimp [θ]
    linarith [hell.2]
  have herr : err ≤ ell := max_le (by linarith [hθ]) hell0
  have hcapH := S.ae_universalHole_physical_missing_except_partner_le r p hpair
    hW hd hgap hell.2 hN
  have hcapB := P.ae_universalBad_physical_missing_mass_le S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hcopy := S.ae_universal_copy_inequality r hW hd hgap hN
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hB := S.measurableSet_universalUpperE2BadRegion r p d c
  have hF := (S.hfibers p.val p.property).1
  have hG := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hYbound := PhysicalRepresentative.charge_bound W m
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  filter_upwards [hcopy, Measure.quasiMeasurePreserving_fst.ae
    ((ae_restrict_iff' hH).mp hcapH), Measure.quasiMeasurePreserving_snd.ae
    ((ae_restrict_iff' hB).mp hcapB), hrowH, hrowB]
    with q hcopy hcapH hcapB hrowH hrowB hqH hqB hqpos
  have hnotI : S.ρ q.1 ≠ r.val ∧ S.ρ q.2 ≠ r.val := by
    constructor
    · intro h
      exact hqH (Or.inl (Or.inl h))
    · intro h
      exact hqB.1 (Or.inl h)
  have hc := hcopy hnotI.1 hnotI.2 hqpos
  let v := Y q.1 q.2
  let Mx := IndependentAtomCopy.missingSection G q.1
  let My := IndependentAtomCopy.missingSection G q.2
  by_cases hsmall : v ≤ err
  · exact hsmall.trans herr
  have hlarge : err < v := lt_of_not_ge hsmall
  have hx := IndependentAtomCopy.missing_row_le_mass G hG Y hY hYbound F hF
    q.1 q.2 v ell hell0 (hrowH hqH hqB hlarge)
  have hy : (∫ z in My, Y q.1 z ∂μ) ≤ v * μ.real My := by
    have h := IndependentAtomCopy.missing_row_le_mass G hG Y hY hYbound
      (∅ : Set Ω) MeasurableSet.empty q.2 q.1 v 0 le_rfl
      ((hrowB hqH hqB hlarge).mono (fun z hz hG => by
        constructor
        · intro h; simp at h
        · intro _; exact hz hG))
    simpa [My] using h
  have hj : 0 ≤ μ.real (Mx ∩ My) := measureReal_nonneg
  have hbudget : (6 * A - 2) * v + γ ≤ b * ell := by
    apply universal_copy_budget_scalar hm.le hj
      (show A * v + γ - m * μ.real (Mx ∩ My) ≤
        (∫ z in Mx, Y q.2 z ∂μ) + (∫ z in My, Y q.1 z ∂μ) by
          change A * v + γ - m * μ.real (Mx ∩ My) ≤
            (∫ z in Mx, Y q.2 z ∂μ) +
              (∫ z in My, Y q.1 z ∂μ) at hc
          exact hc)
      (show (∫ z in Mx, Y q.2 z ∂μ) ≤ v * (1 - 2 * A - b) + b * ell by
        have hFmass : μ.real F = b := rfl
        rw [hFmass] at hx
        nlinarith [mul_nonneg hqpos.le (sub_nonneg.mpr
          (show μ.real (Mx \ F) ≤ 1 - 2 * A - b by exact hcapH hqH))])
      (show (∫ z in My, Y q.1 z ∂μ) ≤ v * (1 - 3 * A + b) by
        nlinarith [mul_nonneg hqpos.le (sub_nonneg.mpr
          (show μ.real My ≤ 1 - 3 * A + b by exact hcapB hqB))])
  exact universal_copy_cap_scalar hA hbudget hprice

/-- Under the actual scalar price guard, an original hole-to-bad charge
is at most the multiplier magnitude. -/
theorem UniversalPhysicalPrimal.ae_hole_bad_charge_le_multiplier
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hprice : S.originalAtomMass p * (-m) - (2 * (c - m * d) + m) ≤
      (-m) * (6 * S.originalAtomMass r - 2)) :
    ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalUpperE2BadRegion r p d c →
      0 < PhysicalRepresentative.charge W m q.1 q.2 →
        PhysicalRepresentative.charge W m q.1 q.2 ≤ -m := by
  exact P.ae_hole_bad_charge_le_of_missing_rows S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin hprice
    (P.ae_hole_bad_missing_row_bound S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
    (P.ae_bad_hole_missing_row_bound S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)

/-- Saturation of the original root–partner edge leaves nonpositive
physical charge from the partner to every good common recipient. -/
theorem UniversalPhysicalPrimal.ae_partner_good_charge_nonpos
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ,
      S.ρ q.1 = p.val →
      q.2 ∈ S.universalGoodCommonRegion r p d c →
        PhysicalRepresentative.charge W m q.1 q.2 ≤ 0 := by
  let U := S.universalPartnerCommonRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  let θ := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  have hApos : 0 < S.originalAtomMass r := by linarith
  have hθ : 0 < θ := by
    have hh : 2 * (1 + m) <
        3 * (2 * (c - m * d) + m) / S.originalAtomMass r := by
      apply (lt_div_iff₀ hApos).mpr
      nlinarith [hmargin]
    dsimp [θ]
    linarith [hell.2]
  have hscore := S.ae_universal_saturated_common_score_nonpos r p hpair
    hW hd hgap hN
  have hrow := S.ae_root_charge p hW hd hgap
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hscore, hrow]
    with q hs hr hqp hGood
  have hU : q.2 ∈ U := hGood.1
  have hnotr : S.ρ q.2 ≠ r.val := by
    intro hh
    exact hGood.1 (Or.inl (Or.inl hh))
  have hθz : θ ≤ S.rootChargeRow r q.2 := by
    apply le_of_not_gt
    intro hh
    exact hGood.2 ⟨by
      intro h
      exact hGood.1 (Or.inl h), hh⟩
  have hNp : q.2 ∈ S.rootNeighborhood p :=
    S.common_region_mem_rootNeighborhood r p hU
  have hsum := hs hnotr hNp
  change S.ρ q.1 = p.val →
    PhysicalRepresentative.charge W m q.1 q.2 = S.rootChargeRow p q.2 at hr
  rw [hr hqp]
  linarith

private theorem UniversalPhysicalPrimal.ae_hole_or_good_charge_le_multiplier
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ,
      (q.1 ∈ S.universalPartnerHoleRegion r p ∨
        q.1 ∈ S.universalGoodCommonRegion r p d c) →
      (q.2 ∈ S.universalPartnerHoleRegion r p ∨
        q.2 ∈ S.universalGoodCommonRegion r p d c) →
        PhysicalRepresentative.charge W m q.1 q.2 ≤ -m := by
  let H := S.universalPartnerHoleRegion r p
  let Good := S.universalGoodCommonRegion r p d c
  let θ := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  have hApos : 0 < S.originalAtomMass r := by linarith
  have hθ : 1 + m < θ := by
    have hh : 2 * (1 + m) <
        3 * (2 * (c - m * d) + m) / S.originalAtomMass r := by
      apply (lt_div_iff₀ hApos).mpr
      nlinarith [hmargin]
    dsimp [θ]
    linarith
  have hHθ := (ae_restrict_iff'
    (S.measurableSet_universalPartnerHoleRegion r p)).mp
      (P.ae_universal_upperE2_hole_star_threshold S r p hpair
        hW hd hgap hN hA hAhalf hell hmargin)
  have hthreshold : ∀ᵐ x ∂μ,
      (x ∈ H ∨ x ∈ Good) → θ ≤ S.rootChargeRow r x := by
    filter_upwards [hHθ] with x hx hcase
    rcases hcase with hH | hGood
    · exact hx hH
    · apply le_of_not_gt
      intro hh
      have hV : x ∈ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ := by
        intro h
        exact hGood.1 (Or.inl h)
      exact hGood.2 ⟨hV, hh⟩
  filter_upwards [S.ae_universal_root_triangle r hW hd hgap hN,
    Measure.quasiMeasurePreserving_fst.ae hthreshold,
    Measure.quasiMeasurePreserving_snd.ae hthreshold]
    with q htri hx hy hcaseX hcaseY
  have hxr : S.ρ q.1 ≠ r.val := by
    rcases hcaseX with hh | hg
    · exact fun he => hh (Or.inl (Or.inl he))
    · exact fun he => hg.1 (Or.inl (Or.inl he))
  have hyr : S.ρ q.2 ≠ r.val := by
    rcases hcaseY with hh | hg
    · exact fun he => hh (Or.inl (Or.inl he))
    · exact fun he => hg.1 (Or.inl (Or.inl he))
  by_cases hG : PhysicalRepresentative.adjacency W m q.1 q.2 = true
  · have ht := htri hxr hyr hG
    linarith [hx hcaseX, hy hcaseY, hθ, hell.2]
  · have hz := PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2
      (Bool.eq_false_iff.mpr hG)
    rw [hz]
    linarith [hell.1]

private theorem ae_partner_hole_or_partner_charge_zero
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ q ∂μ.prod μ,
      S.ρ q.1 = p.val →
      (S.ρ q.2 = p.val ∨ q.2 ∈ S.universalPartnerHoleRegion r p) →
        PhysicalRepresentative.charge W m q.1 q.2 = 0 := by
  filter_upwards [S.ae_root_adjacency p hW hd hgap] with q hr hqp hcase
  have hnotN : q.2 ∉ S.rootNeighborhood p := by
    rcases hcase with hP | hH
    · exact fun h => h.1 hP
    · exact fun h => hH (Or.inr h)
  have hfalse : PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact hnotN ((hr hqp).mp ht)
  exact PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2 hfalse

/-- The actual common-root copy estimate bounds every positive original
body charge on the large-mass price branch. -/
theorem UniversalPhysicalPrimal.ae_universal_positive_body_le_multiplier
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (hprice : S.originalAtomMass p * (-m) - (2 * (c - m * d) + m) ≤
      (-m) * (6 * S.originalAtomMass r - 2)) :
    ∀ᵐ q ∂μ.prod μ,
      IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} q.1 q.2 ≤ -m := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let Good := S.universalGoodCommonRegion r p d c
  let F := {x | S.ρ x = p.val}
  let Y := PhysicalRepresentative.charge W m
  let ell := -m
  let err := max (-m - (3 * (2 * (c - m * d) + m) /
    S.originalAtomMass r - (1 + m))) 0
  have hell0 : 0 ≤ ell := by dsimp [ell]; linarith [hell.1]
  have hApos : 0 < S.originalAtomMass r := by linarith [hA]
  have hθ : 0 < 3 * (2 * (c - m * d) + m) /
      S.originalAtomMass r - (1 + m) := by
    have hh : 2 * (1 + m) <
        3 * (2 * (c - m * d) + m) / S.originalAtomMass r := by
      apply (lt_div_iff₀ hApos).mpr
      nlinarith [hmargin]
    linarith [hell.2]
  have herr : err ≤ ell := by
    dsimp [err, ell]
    exact max_le (by linarith [hθ]) (by linarith [hell.1])
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hB := S.measurableSet_universalUpperE2BadRegion r p d c
  have hGood := S.measurableSet_universalGoodCommonRegion r p d c
  have hF := (S.hfibers p.val p.property).1
  have hYeq := PhysicalRepresentative.charge_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  have hBBraw := IndependentAtomCopy.ae_prod_restrict_imp B B hB hB
    (fun q => chargeKernel W q.1 q.2 ≤ 0)
    (P.ae_bad_bad_charge_nonpos S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hBB : ∀ᵐ q ∂μ.prod μ, q.1 ∈ B → q.2 ∈ B → Y q.1 q.2 ≤ 0 := by
    filter_upwards [hBBraw, hYeq] with q hr he hqB hzB
    change PhysicalRepresentative.charge W m q.1 q.2 ≤ 0
    rw [he]
    exact hr hqB hzB
  have hBGraw := IndependentAtomCopy.ae_prod_restrict_imp B Good hB hGood
    (fun q => chargeKernel W q.1 q.2 ≤ err)
    (P.ae_bad_good_charge_le_endpoint S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hBG : ∀ᵐ q ∂μ.prod μ,
      q.1 ∈ B → q.2 ∈ Good → Y q.1 q.2 ≤ err := by
    filter_upwards [hBGraw, hYeq] with q hr he hqB hzGood
    change PhysicalRepresentative.charge W m q.1 q.2 ≤ err
    rw [he]
    exact hr hqB hzGood
  have hBP := IndependentAtomCopy.ae_prod_restrict_imp B F hB hF
    (fun q => Y q.1 q.2 ≤ ell)
    (P.ae_bad_partner_charge_le_multiplier S r p hpair hW hd hgap hN
      hA hAhalf hell hmargin)
  have hHB := P.ae_hole_bad_charge_le_multiplier S r p hpair hW hd hgap hN
    hA hAhalf hell hmargin hprice
  have hGG := P.ae_hole_or_good_charge_le_multiplier S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hPG := UniversalPhysicalPrimal.ae_partner_good_charge_nonpos S r p hpair
    hW hd hgap hN hA hAhalf hell hmargin
  have hPH := ae_partner_hole_or_partner_charge_zero S r p hW hd hgap
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have hBP' := hswap.ae hBP
  have hBG' := hswap.ae hBG
  have hHB' := hswap.ae hHB
  have hPG' := hswap.ae hPG
  have hPH' := hswap.ae hPH
  have hparts (x : Ω) (hxr : S.ρ x ≠ r.val) :
      x ∈ F ∨ x ∈ H ∨ x ∈ B ∨ x ∈ Good := by
    by_cases hxp : x ∈ F
    · exact Or.inl hxp
    by_cases hxH : x ∈ H
    · exact Or.inr (Or.inl hxH)
    have hxU : x ∈ S.universalPartnerCommonRegion r p := by
      change x ∉ {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪ H
      intro hh
      rcases hh with (hr | hp) | hH'
      · exact hxr hr
      · exact hxp hp
      · exact hxH hH'
    by_cases hxB : x ∈ B
    · exact Or.inr (Or.inr (Or.inl hxB))
    · exact Or.inr (Or.inr (Or.inr ⟨hxU, hxB⟩))
  filter_upwards [hBB, hBG, hBP, hHB, hGG, hPG, hPH,
    hBP', hBG', hHB', hPG', hPH']
    with q hBB hBG hBP hHB hGG hPG hPH hBP' hBG' hHB' hPG' hPH'
  by_cases hx : S.ρ q.1 ≠ r.val ∧ S.ρ q.2 ≠ r.val
  · have hcap : Y q.1 q.2 ≤ ell := by
      change PhysicalRepresentative.charge W m q.1 q.2 ≤ ell
      rcases hparts q.1 hx.1 with hP1 | hH1 | hB1 | hG1
      · rcases hparts q.2 hx.2 with hP2 | hH2 | hB2 | hG2
        · rw [hPH hP1 (Or.inl hP2)]; exact hell0
        · rw [hPH hP1 (Or.inr hH2)]; exact hell0
        · rw [PhysicalRepresentative.charge_symm W m q.1 q.2]
          exact hBP' hB2 hP1
        · exact (hPG hP1 hG2).trans hell0
      · rcases hparts q.2 hx.2 with hP2 | hH2 | hB2 | hG2
        · have hh := hPH' hP2 (Or.inr hH1)
          change PhysicalRepresentative.charge W m q.2 q.1 = 0 at hh
          rw [PhysicalRepresentative.charge_symm W m q.1 q.2, hh]
          exact hell0
        · exact hGG (Or.inl hH1) (Or.inl hH2)
        · by_cases hpos : 0 < Y q.1 q.2
          · exact hHB hH1 hB2 hpos
          · linarith
        · exact hGG (Or.inl hH1) (Or.inr hG2)
      · rcases hparts q.2 hx.2 with hP2 | hH2 | hB2 | hG2
        · exact hBP hB1 hP2
        · rw [PhysicalRepresentative.charge_symm W m q.1 q.2]
          by_cases hpos : 0 < Y q.2 q.1
          · exact hHB' hH2 hB1 hpos
          · linarith
        · exact (hBB hB1 hB2).trans hell0
        · exact (hBG hB1 hG2).trans herr
      · rcases hparts q.2 hx.2 with hP2 | hH2 | hB2 | hG2
        · rw [PhysicalRepresentative.charge_symm W m q.1 q.2]
          exact (hPG' hP2 hG1).trans hell0
        · exact hGG (Or.inr hG1) (Or.inl hH2)
        · rw [PhysicalRepresentative.charge_symm W m q.1 q.2]
          exact (hBG' hB2 hG1).trans herr
        · exact hGG (Or.inr hG1) (Or.inr hG2)
    dsimp only [IndependentAtomCopy.positiveBody]
    have hx' : q.1 ∉ {x | S.ρ x = r.val} ∧
        q.2 ∉ {x | S.ρ x = r.val} := hx
    rw [ite_eq_left hx']
    exact max_le hcap hell0
  · dsimp only [IndependentAtomCopy.positiveBody]
    have hx' : ¬(q.1 ∉ {x | S.ρ x = r.val} ∧
        q.2 ∉ {x | S.ρ x = r.val}) := hx
    rw [ite_eq_right hx']
    exact hell0

end Erdos1017.CappedModel.SelectedHighLowStructure
