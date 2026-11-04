module

public import Erdos1017.Exclusions.E2.Middle.UniversalIntegratedDeficitFloor
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitAtoms
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitRows
public import Erdos1017.Exclusions.Common.E2.SelectedEmptySatE2Inventory
public import Erdos1017.Exclusions.Common.Universal.UniversalDeficitCompleteParts

/-!
# Integrated deficit floor on the universal partner hole

Integrating the universal triangle over `H` leaves the same-atom missing
deficit, clique dust contributes zero to both missing-square integrals, and the
integrated atomic floor bounds the weighted missing-pair integral, yielding the
three necessary polynomials for arbitrary numerical caps
(`universal_deficit_three_polynomials`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem measurable_adjacency : Measurable (fun q : Ω × Ω =>
    adjacencyKernel W q.1 q.2) :=
  (W.stronglyMeasurable_moment
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem missing_kernel_integrable (E F : Set Ω) :
    Integrable (fun q : Ω × Ω => 1 - adjacencyKernel W q.1 q.2)
      ((μ.restrict E).prod (μ.restrict F)) := by
  apply Integrable.of_bound
    (measurable_const.sub (measurable_adjacency (W := W))).aestronglyMeasurable 1
  exact Eventually.of_forall (fun q => by
    have h := adjacency_moment_mem W q
    change 0 ≤ adjacencyKernel W q.1 q.2 ∧ adjacencyKernel W q.1 q.2 ≤ 1 at h
    change ‖1 - adjacencyKernel W q.1 q.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.2)]
    linarith only [h.1])

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem missing_section_integrable (E F : Set Ω) :
    IntegrableOn (fun x => ∫ y in F, 1 - adjacencyKernel W x y ∂μ) E μ :=
  (missing_kernel_integrable E F).integral_prod_left

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem missing_deficit_integrable (S : SelectedHighLowStructure W m)
    (r : S.I) (E F : Set Ω) :
    IntegrableOn (fun x => (∫ y in F, 1 - adjacencyKernel W x y ∂μ) *
      S.universalRootDeficit r x) E μ := by
  have hb : ∀ᵐ x ∂μ.restrict E, ‖S.universalRootDeficit r x‖ ≤ 4 :=
    Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (S.universalRootDeficit_mem_Icc r x).1]
      exact (S.universalRootDeficit_mem_Icc r x).2)
  simpa only [mul_comm, IntegrableOn] using Integrable.bdd_mul
    (missing_section_integrable (W := W) E F)
    (S.measurable_universalRootDeficit r).aestronglyMeasurable hb

/-- Integrating the actual universal triangle over H leaves its original
same-atom missing deficit. No extra diagonal is assigned to dust. -/
theorem ae_universalPartnerHole_integrated_triangle
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      (1 + m) * (μ.real (S.universalPartnerHoleRegion r p) -
        S.universalPartnerHoleMissingMass r p x) ≤
      (μ.real (S.universalPartnerHoleRegion r p) -
        2 * S.universalPartnerHoleMissingMass r p x) * S.universalRootDeficit r x +
        ∫ y in S.universalPartnerHoleRegion r p, S.universalRootDeficit r y ∂μ := by
  let H := S.universalPartnerHoleRegion r p
  let D := S.universalRootDeficit r
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hpairs := S.ae_universal_deficit_triangle r hW hd hgap
    (S.neutral_atom_adjacency r hW hd hgap hN)
  have hs := Measure.ae_ae_of_ae_prod (hpairs.and hW.moment_mem)
  filter_upwards [ae_restrict_of_ae hs,
    S.ae_universalPartnerHole_missing_deficit_eq_mass_mul r p hpair hW hd hgap hell,
    ae_restrict_mem hH] with x hx hmissing hxH
  let f : Ω → ℝ := fun y => 1 - adjacencyKernel W x y
  have hf : IntegrableOn f H μ := by
    apply Integrable.of_bound
      ((measurable_const.sub (measurable_adjacency (W := W))).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun y => by
      have h := adjacency_moment_mem W (x, y)
      change 0 ≤ adjacencyKernel W x y ∧ adjacencyKernel W x y ≤ 1 at h
      change ‖1 - adjacencyKernel W x y‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.2)]
      linarith only [h.1])
  have hD : IntegrableOn D H μ := (S.integrable_universalRootDeficit r).integrableOn
  have hfD : IntegrableOn (fun y => f y * D y) H μ := by
    have hi := Integrable.bdd_mul hf
      (S.measurable_universalRootDeficit r).aestronglyMeasurable (c := 4)
    apply (by simpa only [mul_comm] using hi)
    exact Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (S.universalRootDeficit_mem_Icc r y).1]
      exact (S.universalRootDeficit_mem_Icc r y).2)
  have hi := integral_mono_ae ((integrable_const (1 + m)).sub (hf.const_mul (1 + m)))
    ((((integrable_const (D x)).add hD).sub (hf.const_mul (D x))).sub hfD) (by
      filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem hH] with y hy hyH
      have ht := hy.1 (fun hh => hxH (Or.inl (Or.inl hh)))
        (fun hh => hyH (Or.inl (Or.inl hh)))
      have hk := hy.2
      change 0 ≤ shiftedKernel W m x y ∧ shiftedKernel W m x y ≤ 4 at hk
      have he : shiftedKernel W m x y = chargeKernel W x y - m * adjacencyKernel W x y :=
        shiftedMoment_eq W m (x, y)
      dsimp only [Pi.sub_apply, Pi.add_apply, f, D]
      nlinarith only [ht, hk.1, he])
  simp only [Pi.sub_apply, Pi.add_apply] at hi
  have he₁ := integral_sub
    (((integrable_const (D x)).add hD).sub (hf.const_mul (D x))) hfD
  have he₂ := integral_sub ((integrable_const (D x)).add hD) (hf.const_mul (D x))
  have he₃ := integral_add (integrable_const (D x)) hD
  simp only [Pi.sub_apply, Pi.add_apply] at he₁ he₂ he₃
  rw [integral_sub (integrable_const _) (hf.const_mul _), integral_const_mul,
    he₁, he₂, he₃, integral_const_mul] at hi
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hi
  change (∫ y in H, f y * D y ∂μ) =
    S.universalPartnerHoleMissingMass r p x * D x at hmissing
  rw [hmissing] at hi
  change μ.real H * (1 + m) - (1 + m) * (∫ y in H, f y ∂μ) ≤
    μ.real H * D x + (∫ y in H, D y ∂μ) - D x * (∫ y in H, f y ∂μ) -
      (∫ y in H, f y ∂μ) * D x at hi
  change (1 + m) * (μ.real H - ∫ y in H, f y ∂μ) ≤
    (μ.real H - 2 * (∫ y in H, f y ∂μ)) * D x + ∫ y in H, D y ∂μ
  nlinarith only [hi]

/-- An original whole-atom cap also bounds every actual H missing section;
positive sections are whole fibers and all other sections have mass zero. -/
theorem ae_universalPartnerHole_missing_mass_le
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c C : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hC : 0 ≤ C)
    (hparts : ∀ j : S.I, (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) → S.originalAtomMass j ≤ C) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.universalPartnerHoleMissingMass r p x ≤ C := by
  filter_upwards [S.ae_universalPartnerHole_atom_of_missing_mass_pos
    r p hpair hW hd hgap hell] with x hx
  by_cases hpos : 0 < S.universalPartnerHoleMissingMass r p x
  · obtain ⟨j, _, hj, he, _⟩ := hx hpos
    rw [he]
    exact hparts j hj
  · exact (le_of_not_gt hpos).trans hC

/-- Genuine clique dust contributes zero to both missing-square integrals. -/
theorem ae_universalPartnerHole_dust_missing_mass_zero
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      S.ρ x ∉ S.I → S.universalPartnerHoleMissingMass r p x = 0 := by
  filter_upwards [S.ae_universalPartnerHole_atom_of_missing_mass_pos
    r p hpair hW hd hgap hell] with x hx hdust
  apply le_antisymm _ (S.universalPartnerHoleMissingMass_nonneg r p x)
  by_contra hn
  obtain ⟨j, hj, _, _, _⟩ := hx (lt_of_not_ge hn)
  exact hdust (hj ▸ j.property)

/-- The integrated atomic floor is a bound on the actual original weighted
missing-pair integral. The domain and half-mass alternatives are derived. -/
theorem universal_integrated_atomic_deficit_floor
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c C y : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hy : (1 - m - 4 * (c - m * d)) / (1 + m) ≤ y) (hC : 0 ≤ C)
    (hparts : ∀ j : S.I, (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) → S.originalAtomMass j ≤ C)
    (hremain : 0 < μ.real (S.universalPartnerHoleRegion r p) - C -
      (y - μ.real (S.universalPartnerCommonRegion r p))) :
    let H := S.universalPartnerHoleRegion r p
    let η := μ.real H
    let P := y - μ.real (S.universalPartnerCommonRegion r p)
    let Q := ∫ x in H, S.universalPartnerHoleMissingMass r p x ∂μ
    let T := ∫ x in H, S.universalPartnerHoleMissingMass r p x *
      S.universalRootDeficit r x ∂μ
    η / 2 ≤ P ∧ C < η / 2 ∧ (1 + m) * Q * (η - C - P) / (η - 2 * C) ≤ T := by
  dsimp only
  let H := S.universalPartnerHoleRegion r p
  let D := S.universalRootDeficit r
  let a := S.universalPartnerHoleMissingMass r p
  let P := y - μ.real (S.universalPartnerCommonRegion r p)
  have hδ : 0 < 1 + m := by linarith only [hell]
  have hDH : IntegrableOn D H μ := (S.integrable_universalRootDeficit r).integrableOn
  have hcap : (∫ x in H, D x ∂μ) ≤ (1 + m) * P := by
    have hy' := (div_le_iff₀ hδ).mp hy
    have hh := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
    change (∫ x in H, D x ∂μ) ≤ _ at hh
    dsimp only [P]
    nlinarith only [hy', hh]
  have hrows := S.ae_universalPartnerHole_integrated_triangle r p hpair hW hd hgap hell hN
  have hacap := S.ae_universalPartnerHole_missing_mass_le r p hpair hW hd hgap hell hC hparts
  have hlower := UniversalDeficit.complete_part_lower_of_integrated_rows
    (ν := μ.restrict H) D a hDH hδ (hrows.and hacap |>.mono fun x hx =>
      ⟨(S.universalRootDeficit_mem_Icc r x).1, hx.2, by
        simpa only [measureReal_restrict_apply_univ] using hx.1⟩)
  rw [measureReal_restrict_apply_univ] at hlower
  obtain ⟨hhalf, hCstrict⟩ := UniversalDeficit.floor_domain hδ hlower hcap hremain
  refine ⟨hhalf, hCstrict, ?_⟩
  have hpoint : ∀ᵐ x ∂μ.restrict H,
      (1 + m) * (μ.real H - C - P) / (μ.real H - 2 * C) * a x ≤ a x * D x := by
    filter_upwards [hrows, hacap] with x hx hax
    have hf := UniversalDeficit.uniform_atomic_floor hδ hhalf hCstrict hax hx hcap
    have ha := S.universalPartnerHoleMissingMass_nonneg r p x
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hf ha
  have hi := integral_mono_ae
    ((missing_section_integrable (W := W) H H).const_mul _)
    (S.missing_deficit_integrable r H H) hpoint
  rw [integral_const_mul] at hi
  change (1 + m) * (∫ x in H, a x ∂μ) * (μ.real H - C - P) / (μ.real H - 2 * C) ≤
    ∫ x in H, a x * D x ∂μ
  change (1 + m) * (μ.real H - C - P) / (μ.real H - 2 * C) * (∫ x in H, a x ∂μ) ≤
    ∫ x in H, a x * D x ∂μ at hi
  convert hi using 1; ring

/-- The same original stationary deficit rows pay one joint H-square,
H/U-hole and weighted-atomic budget. -/
theorem universal_integrated_deficit_joint
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c y : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hy : (1 - m - 4 * (c - m * d)) / (1 + m) ≤ y) :
    let H := S.universalPartnerHoleRegion r p
    let U := S.universalPartnerCommonRegion r p
    let η := μ.real H
    let D := S.universalRootDeficit r
    let a := S.universalPartnerHoleMissingMass r p
    let k := S.universalPartnerCommonMissingMass r p
    (1 + m) * (η ^ 2 - (∫ x in H, a x ∂μ) + (∫ x in H, k x ∂μ)) +
      2 * (∫ x in H, a x * D x ∂μ) ≤
        η * ((1 + m) * (y - μ.real U)) +
          (η + μ.real U - S.originalAtomMass r) * (∫ x in H, D x ∂μ) := by
  dsimp only
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let D := S.universalRootDeficit r
  let a := S.universalPartnerHoleMissingMass r p
  let k := S.universalPartnerCommonMissingMass r p
  let η := μ.real H
  have hδ : 0 < 1 + m := by linarith only [hell]
  have hy' := (div_le_iff₀ hδ).mp hy
  have hrows := S.ae_universalPartnerHole_deficit_row r p hpair hW hd hgap hell hN
  have hfloor := S.ae_universalPartnerHole_commonMissing_pos_deficit_gt
    r p hpair hW hd hgap hell hN
  have hpoint : ∀ᵐ x ∂μ.restrict H,
      (1 + m) * (η - a x + k x) + 2 * (a x * D x) ≤
        (1 + m) * (y - μ.real U) + (η + μ.real U - S.originalAtomMass r) * D x := by
    filter_upwards [hrows, hfloor] with x hx hk
    have hB := S.universalPartnerCommonMissingDeficit_ge_floor r p hpair hW hd hgap hell hN x
    have hk0 := S.universalPartnerCommonMissingMass_nonneg r p x
    have hkd : (1 + m) * k x ≤ k x * D x := by
      by_cases hpos : 0 < k x
      · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hk hpos).le hpos.le
      · have he : k x = 0 := le_antisymm (le_of_not_gt hpos) hk0
        simp [he]
    change (η + μ.real U - S.originalAtomMass r - 2 * a x - k x) * D x ≥ _ at hx
    change (1 + m) * k x ≤ _ at hB
    nlinarith only [hx, hB, hkd, hy']
  have ha : IntegrableOn a H μ := missing_section_integrable H H
  have hk : IntegrableOn k H μ := missing_section_integrable H U
  have hD : IntegrableOn D H μ := (S.integrable_universalRootDeficit r).integrableOn
  have haD : IntegrableOn (fun x => a x * D x) H μ := S.missing_deficit_integrable r H H
  have hi := integral_mono_ae
    ((((integrable_const η).sub ha).add hk).const_mul (1 + m) |>.add (haD.const_mul 2))
    ((integrable_const ((1 + m) * (y - μ.real U))).add
      (hD.const_mul (η + μ.real U - S.originalAtomMass r))) hpoint
  have he₁ := integral_add
    (((integrable_const η).sub ha).add hk |>.const_mul (1 + m)) (haD.const_mul 2)
  have he₂ := integral_add ((integrable_const η).sub ha) hk
  have he₃ := integral_sub (integrable_const η) ha
  have he₄ := integral_add (integrable_const ((1 + m) * (y - μ.real U)))
    (hD.const_mul (η + μ.real U - S.originalAtomMass r))
  simp only [Pi.add_apply, Pi.sub_apply] at hi he₁ he₂ he₃ he₄
  rw [he₁, he₄, integral_const_mul, integral_const_mul, integral_const_mul, he₂, he₃] at hi
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hi
  change (1 + m) * (η ^ 2 - (∫ x in H, a x ∂μ) + (∫ x in H, k x ∂μ)) +
    2 * (∫ x in H, a x * D x ∂μ) ≤
      η * ((1 + m) * (y - μ.real U)) + (η + μ.real U - S.originalAtomMass r) * (∫ x in H, D x ∂μ)
  simp only [integral_const_mul] at hi
  change (1 + m) * (η * η - (∫ x in H, a x ∂μ) + (∫ x in H, k x ∂μ)) +
    2 * (∫ x in H, a x * D x ∂μ) ≤ (1 + m) * (η * (y - μ.real U)) +
      (η + μ.real U - S.originalAtomMass r) * (∫ x in H, D x ∂μ) at hi
  nlinarith only [hi]

/-- The H-square is one subinventory of the literal complement of the two
heads. Its upper bound therefore uses the original total missing mass. -/
theorem universalPartnerHole_square_le_missing_residual
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    (∫ x in S.universalPartnerHoleRegion r p,
      S.universalPartnerHoleMissingMass r p x ∂μ) ≤
      1 - 2 * d - (S.originalAtomMass r) ^ 2 - (S.originalAtomMass p) ^ 2 -
        2 * S.originalAtomMass p * μ.real (S.universalPartnerHoleRegion r p) := by
  let H := S.universalPartnerHoleRegion r p
  let O := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ
  let M : Ω × Ω → ℝ := fun q => 1 - if PhysicalRepresentative.adjacency W m q.1 q.2
    then 1 else 0
  have hH := S.measurableSet_universalPartnerHoleRegion r p
  have hO : MeasurableSet O := ((S.hfibers r.val r.property).1.union
    (S.hfibers p.val p.property).1).compl
  have hsub : H ⊆ O := fun x hx hh => hx (Or.inl hh)
  have hMint : Integrable M (μ.prod μ) := by
    apply Integrable.of_bound
      (measurable_const.sub ((measurable_of_countable (fun b : Bool =>
        if b then (1 : ℝ) else 0)).comp
          (PhysicalRepresentative.measurable_adjacency W m))).aestronglyMeasurable 1
    exact Eventually.of_forall (fun q => by
      change ‖1 - if PhysicalRepresentative.adjacency W m q.1 q.2 then (1 : ℝ) else 0‖ ≤ 1
      split_ifs <;> norm_num)
  have hbound : (∫ q, M q ∂(μ.restrict H).prod (μ.restrict H)) ≤
      ∫ q, M q ∂(μ.restrict O).prod (μ.restrict O) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    apply setIntegral_mono_set hMint.integrableOn
      (Eventually.of_forall (fun q => by dsimp only [M]; split_ifs <;> norm_num))
    exact Eventually.of_forall (fun q hq => ⟨hsub hq.1, hsub hq.2⟩)
  have hmoment : (∫ x in H, S.universalPartnerHoleMissingMass r p x ∂μ) =
      ∫ q, M q ∂(μ.restrict H).prod (μ.restrict H) := by
    change (∫ x in H, ∫ y in H, 1 - adjacencyKernel W x y ∂μ ∂μ) = _
    rw [← integral_prod _ (missing_kernel_integrable H H)]
    apply integral_congr_ae
    filter_upwards [(Measure.absolutelyContinuous_restrict.prod
      Measure.absolutelyContinuous_restrict).ae_le
        (PhysicalRepresentative.adjacency_moment_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support)] with q hq
    change adjacencyKernel W q.1 q.2 = _ at hq
    dsimp only [M]
    rw [hq]
  have htotal := (S.empty_sat_deleted_partner_inventory r p hpair hW hd hgap hN).2.2.1
  rw [hmoment]
  exact hbound.trans_eq htotal

/-- The same actual atomic square and weighted square yield all three
necessary polynomials for arbitrary numerical caps on this original state. -/
theorem universal_deficit_three_polynomials
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c C y h : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hy : (1 - m - 4 * (c - m * d)) / (1 + m) ≤ y) (hh : 1 - 2 * d ≤ h) (hC : 0 ≤ C)
    (hparts : ∀ j : S.I, (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val},
      x ∈ S.universalPartnerHoleRegion r p) → S.originalAtomMass j ≤ C)
    (hremain : 0 < μ.real (S.universalPartnerHoleRegion r p) - C -
      (y - μ.real (S.universalPartnerCommonRegion r p)))
    (hcoef : 0 ≤ μ.real (S.universalPartnerHoleRegion r p) +
      μ.real (S.universalPartnerCommonRegion r p) - S.originalAtomMass r) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let η := μ.real (S.universalPartnerHoleRegion r p)
    let u := μ.real (S.universalPartnerCommonRegion r p)
    let Q₀ := h - A ^ 2 - b ^ 2 - 2 * b * η
    let z := 2 * (y - u) - η
    let w := 1 - A - b - y
    let x := y - A
    0 ≤ Q₀ ∧ 0 ≤ z * C * η - (w ^ 2 - x * (y - u)) * (η - 2 * C) ∧
      0 ≤ z * Q₀ - (w ^ 2 - x * (y - u)) * (η - 2 * C) := by
  dsimp only
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let D := S.universalRootDeficit r
  let a := S.universalPartnerHoleMissingMass r p
  let k := S.universalPartnerCommonMissingMass r p
  have hδ : 0 < 1 + m := by linarith only [hell]
  have hcap : (∫ x in H, D x ∂μ) ≤ (1 + m) * (y - μ.real U) := by
    have hy' := (div_le_iff₀ hδ).mp hy
    have hh' := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
    change (∫ x in H, D x ∂μ) ≤ _ at hh'
    nlinarith only [hy', hh']
  obtain ⟨hhalf, hCstrict, hfloor⟩ := S.universal_integrated_atomic_deficit_floor
    r p hpair hW hd hgap hell hN hy hC hparts hremain
  have hQC : (∫ x in H, a x ∂μ) ≤ C * μ.real H := by
    have hbound := integral_mono_ae (missing_section_integrable (W := W) H H)
      (integrable_const C)
      (S.ae_universalPartnerHole_missing_mass_le r p hpair hW hd hgap hell hC hparts)
    change (∫ x in H, a x ∂μ) ≤ ∫ x in H, C ∂μ at hbound
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
      using hbound
  have hQh : (∫ x in H, a x ∂μ) ≤
      h - (S.originalAtomMass r) ^ 2 - (S.originalAtomMass p) ^ 2 -
        2 * S.originalAtomMass p * μ.real H := by
    have hbound := S.universalPartnerHole_square_le_missing_residual r p hpair hW hd hgap hN
    change (∫ x in H, a x ∂μ) ≤ _ at hbound
    linarith only [hbound, hh]
  exact UniversalDeficit.three_polynomials hδ (S.universalPartner_regions_mass r p hpair.1)
    (integral_nonneg (fun x => S.universalPartnerHoleMissingMass_nonneg r p x))
    (integral_nonneg (fun x => S.universalPartnerCommonMissingMass_nonneg r p x))
    hhalf hCstrict hremain hcoef hcap hfloor
    (S.universal_integrated_deficit_joint r p hpair hW hd hgap hell hN hy) hQC hQh

end Erdos1017.CappedModel.SelectedHighLowStructure
