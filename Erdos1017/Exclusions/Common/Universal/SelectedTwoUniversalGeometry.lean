module

public import Erdos1017.Exclusions.Common.Physical.IndependentHeadSupport
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedCommonMass
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyInequality

/-!
# Support geometry of two neutral saturated heads

Two neutral saturated heads satisfy the correlated support inequality, with the
geometry, stationary rows and restricted support bounds derived on the same
model.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
private theorem three_region_measure (I J : Set Ω) (hI : MeasurableSet I)
    (hJ : MeasurableSet J) (hdis : Disjoint I J) :
    μ.restrict I + μ.restrict J + μ.restrict (I ∪ J)ᶜ = μ := by
  rw [← Measure.restrict_union hdis hJ, Measure.restrict_add_restrict_compl (hI.union hJ)]

private theorem integral_split_regions (K : Ω × Ω → ℝ) (hK : Measurable K)
    (B : ℝ) (hB : ∀ p, ‖K p‖ ≤ B) (I J : Set Ω)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (hdis : Disjoint I J)
    (ν : Measure Ω) [IsFiniteMeasure ν] :
    (∫ p, K p ∂ν.prod μ) =
      (∫ p, K p ∂ν.prod (μ.restrict I)) +
        (∫ p, K p ∂ν.prod (μ.restrict J)) +
        ∫ p, K p ∂ν.prod (μ.restrict (I ∪ J)ᶜ) := by
  have hi (ρ : Measure (Ω × Ω)) [IsFiniteMeasure ρ] : Integrable K ρ :=
    Integrable.of_bound hK.aestronglyMeasurable B (Eventually.of_forall hB)
  calc
    _ = ∫ p, K p ∂ν.prod
        (μ.restrict I + μ.restrict J + μ.restrict (I ∪ J)ᶜ) := by
      rw [three_region_measure I J hI hJ hdis]
    _ = _ := by
      rw [Measure.prod_add, Measure.prod_add, integral_add_measure (hi _) (hi _),
        integral_add_measure (hi _) (hi _)]

private theorem integral_pair_swap (K : Ω × Ω → ℝ) (hsym : ∀ p, K p = K p.swap)
    (ν ρ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    (∫ p, K p ∂ν.prod ρ) = ∫ p, K p ∂ρ.prod ν := by
  calc
    _ = ∫ p, K p.swap ∂ν.prod ρ := integral_congr_ae (Eventually.of_forall hsym)
    _ = _ := integral_prod_swap K

private theorem integral_three_region_partition (K : Ω × Ω → ℝ) (hK : Measurable K)
    (B : ℝ) (hB : ∀ p, ‖K p‖ ≤ B) (hsym : ∀ p, K p = K p.swap)
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J) (hdis : Disjoint I J) :
    (∫ p, K p ∂μ.prod μ) =
      2 * (∫ p, K p ∂(μ.restrict I).prod μ) +
        2 * (∫ p, K p ∂(μ.restrict J).prod μ) -
        (∫ p, K p ∂(μ.restrict I).prod (μ.restrict I)) -
        (∫ p, K p ∂(μ.restrict J).prod (μ.restrict J)) -
        2 * (∫ p, K p ∂(μ.restrict I).prod (μ.restrict J)) +
        ∫ p, K p ∂(μ.restrict (I ∪ J)ᶜ).prod (μ.restrict (I ∪ J)ᶜ) := by
  have h := integral_split_regions (μ := μ) K hK B hB I J hI hJ hdis μ
  have hi := integral_split_regions (μ := μ) K hK B hB I J hI hJ hdis (μ.restrict I)
  have hj := integral_split_regions (μ := μ) K hK B hB I J hI hJ hdis (μ.restrict J)
  have hr := integral_split_regions (μ := μ) K hK B hB I J hI hJ hdis (μ.restrict (I ∪ J)ᶜ)
  rw [integral_pair_swap K hsym μ (μ.restrict I),
    integral_pair_swap K hsym μ (μ.restrict J),
    integral_pair_swap K hsym μ (μ.restrict (I ∪ J)ᶜ)] at h
  rw [integral_pair_swap K hsym (μ.restrict J) (μ.restrict I)] at hj
  rw [integral_pair_swap K hsym (μ.restrict (I ∪ J)ᶜ) (μ.restrict I),
    integral_pair_swap K hsym (μ.restrict (I ∪ J)ᶜ) (μ.restrict J)] at hr
  linarith only [h, hi, hj, hr]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

private theorem ae_neutral_row_positive (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ y ∂μ, S.ρ y ≠ r.val → 0 < r.val y := by
  have hrow := Measure.ae_ae_of_ae_prod (S.ae_root_adjacency r hW hd hgap)
  have huniv := Measure.ae_ae_of_ae_prod (S.neutral_atom_physical_adjacency r hW hd hgap hN)
  obtain ⟨x, hx, hr, hu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    ((ae_restrict_of_ae hrow).and (ae_restrict_of_ae huniv))
  filter_upwards [hr, hu] with y hr hu hy
  exact ((hr hx).mp ((hu hx).mpr hy)).2

private def physicalMissing (W : Model Ω μ) (m : ℝ) (p : Ω × Ω) : ℝ :=
  1 - if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0

omit [IsProbabilityMeasure μ] [StandardBorelSpace Ω] [MeasurableEq Ω]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem physicalMissing_measurable : Measurable (physicalMissing W m) :=
  measurable_const.sub (Measurable.ite (measurableSet_eq_fun
    (PhysicalRepresentative.measurable_adjacency W m) measurable_const)
      measurable_const measurable_const)

omit [IsProbabilityMeasure μ] [StandardBorelSpace Ω] [MeasurableEq Ω]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem physicalMissing_mem (p : Ω × Ω) : physicalMissing W m p ∈ Icc (0 : ℝ) 1 := by
  unfold physicalMissing
  split_ifs <;> norm_num

private theorem neutral_missing_row (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      physicalMissing W m p = {x | S.ρ x = r.val}.indicator (fun _ => 1) p.2 := by
  filter_upwards [S.neutral_atom_physical_adjacency r hW hd hgap hN] with p hp hx
  unfold physicalMissing
  by_cases hy : S.ρ p.2 = r.val
  · have hA : PhysicalRepresentative.adjacency W m p.1 p.2 ≠ true :=
      fun h => (hp hx).mp h hy
    simp [hA, hy]
  · have hA := (hp hx).mpr hy
    simp [hA, hy]

private theorem neutral_row_integrals (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let I := {x | S.ρ x = r.val}
    let a := μ.real I
    (∫ p, PhysicalRepresentative.charge W m p.1 p.2 ∂(μ.restrict I).prod μ) =
        a * (2 * (c - m * d) + m * (1 - a)) ∧
      (∫ p, physicalMissing W m p ∂(μ.restrict I).prod μ) = a ^ 2 ∧
      (∫ p, PhysicalRepresentative.charge W m p.1 p.2
        ∂(μ.restrict I).prod (μ.restrict I)) = 0 ∧
      (∫ p, physicalMissing W m p ∂(μ.restrict I).prod (μ.restrict I)) = a ^ 2 := by
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  let Y := PhysicalRepresentative.charge W m
  let G : Ω × Ω → ℝ := fun p =>
    if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0
  have hGi (x : Ω) : Integrable (fun z => G (x, z)) μ := by
    apply Integrable.of_bound
      ((Measurable.ite (measurableSet_eq_fun
        (PhysicalRepresentative.measurable_adjacency W m) measurable_const)
          measurable_const measurable_const).comp
            (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      change ‖(if PhysicalRepresentative.adjacency W m x z = true then (1 : ℝ) else 0)‖ ≤ 1
      split_ifs <;> norm_num)
  have hYi (x : Ω) : Integrable (Y x) μ := Integrable.of_bound
    ((PhysicalRepresentative.measurable_charge W m).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    (Eventually.of_forall (PhysicalRepresentative.charge_bound W m x))
  have hYprod : Integrable (Function.uncurry Y) ((μ.restrict I).prod μ) :=
    Integrable.of_bound (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
      (Eventually.of_forall (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2))
  have hrow := neutral_missing_row S r hW hd hgap hN
  have hrestricted : ∀ᵐ p ∂(μ.restrict I).prod μ,
      physicalMissing W m p = I.indicator (fun _ => 1) p.2 := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl) hrow,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI)] with p hp hx
    exact hp hx
  have hrowY : ∀ᵐ x ∂μ.restrict I,
      (∫ z, Y x z ∂μ) = 2 * (c - m * d) + m * (1 - μ.real I) := by
    filter_upwards [ae_restrict_of_ae (S.ae_physical_shifted_stationary hW hd hgap),
      Measure.ae_ae_of_ae_prod hrestricted] with x hs hx
    have hG : (∫ z, G (x, z) ∂μ) = 1 - μ.real I := by
      have he : (fun z => G (x, z)) =ᵐ[μ] fun z => 1 - I.indicator (fun _ => 1) z := by
        filter_upwards [hx] with z hz
        change 1 - G (x, z) = I.indicator (fun _ => 1) z at hz
        linarith only [hz]
      rw [integral_congr_ae he,
        integral_sub (integrable_const 1) ((integrable_const 1).indicator hI),
        integral_indicator hI, setIntegral_const, integral_const]
      simp only [probReal_univ, smul_eq_mul, mul_one]
    change (∫ z, Y x z - m * G (x, z) ∂μ) = _ at hs
    rw [integral_sub (hYi x) ((hGi x).const_mul m), integral_const_mul, hG] at hs
    linarith only [hs]
  have htotal : (∫ p, Y p.1 p.2 ∂(μ.restrict I).prod μ) =
      μ.real I * (2 * (c - m * d) + m * (1 - μ.real I)) := by
    change (∫ p, Function.uncurry Y p ∂(μ.restrict I).prod μ) = _
    rw [integral_prod _ hYprod]
    change (∫ x in I, ∫ z, Y x z ∂μ ∂μ) = _
    rw [integral_congr_ae hrowY, integral_const]
    simp only [measureReal_restrict_apply_univ, smul_eq_mul]
  have hmissing : (∫ p, physicalMissing W m p ∂(μ.restrict I).prod μ) = (μ.real I) ^ 2 := by
    rw [integral_congr_ae hrestricted, integral_fun_snd, integral_indicator hI,
      setIntegral_const]
    simp only [measureReal_restrict_apply_univ, smul_eq_mul, mul_one, pow_two]
  have hself : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I),
      physicalMissing W m p = 1 := by
    filter_upwards [ae_mono (Measure.prod_mono le_rfl Measure.restrict_le_self) hrestricted,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hI)] with p hp hx
    simpa only [indicator_of_mem hx] using hp
  have hYself : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), Y p.1 p.2 = 0 := by
    filter_upwards [hself] with p hp
    have hA : PhysicalRepresentative.adjacency W m p.1 p.2 = false := by
      unfold physicalMissing at hp
      split_ifs at hp with h
      · norm_num at hp
      · exact Bool.eq_false_iff.mpr h
    exact PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 hA
  refine ⟨htotal, hmissing, integral_eq_zero_of_ae hYself, ?_⟩
  change (∫ p, physicalMissing W m p ∂(μ.restrict I).prod (μ.restrict I)) = (μ.real I) ^ 2
  rw [integral_congr_ae hself, integral_const]
  simp only [smul_eq_mul, mul_one, ← univ_prod_univ, measureReal_prod_prod,
    measureReal_restrict_apply_univ, pow_two]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem integral_one_rectangle (I J : Set Ω) :
    (∫ _p : Ω × Ω, (1 : ℝ) ∂(μ.restrict I).prod (μ.restrict J)) =
      μ.real I * μ.real J := by
  rw [integral_const]
  simp only [smul_eq_mul, mul_one, ← univ_prod_univ, measureReal_prod_prod,
    measureReal_restrict_apply_univ]

/-- Two actual neutral saturated heads give the original correlated support
inequality. All geometry, stationary rows and restricted support bounds
are derived on the same probability law. -/
theorem IsSaturatedAtomPair.two_universal_support_geometry
    {S : SelectedHighLowStructure W m} {r u : S.I}
    (hpair : S.IsSaturatedAtomPair r u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hNr : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hNu : ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, x ∈ S.N)
    (horder : μ.real {x | S.ρ x = u.val} ≤ μ.real {x | S.ρ x = r.val}) :
    let a := μ.real {x | S.ρ x = r.val}
    let b := μ.real {x | S.ρ x = u.val}
    let s := a + b
    let v := a - b
    let h := 1 - 2 * d
    let gamma := 2 * c + m * h
    let T := (1 + m) * s - 2 * gamma
    s < 1 ∧ 0 ≤ v ∧ s ^ 2 + v ^ 2 ≤ 2 * h ∧ 0 ≤ T ∧
      (1 + m) * (s - 2 * h) + 2 * m * v ^ 2 + (2 * s - 1) * T -
        (1 - s) ^ 2 / 12 +
        (12 / 25) * max ((1 - m) * v - T - (1 - s) / 12) 0 ^ 2 ≤ 0 := by
  classical
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = u.val}
  let R := (I ∪ J)ᶜ
  let a := μ.real I
  let b := μ.real J
  let s := a + b
  let v := a - b
  let h := 1 - 2 * d
  let gamma := 2 * c + m * h
  let T := (1 + m) * s - 2 * gamma
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let K : Ω × Ω → ℝ := fun p => Y p.1 p.2
  let M := physicalMissing W m
  let Q := ∫ p, M p ∂(μ.restrict R).prod (μ.restrict R)
  let C₀ := FiniteCappedSamplingCost.physicalObjective (μ.restrict R) Y
  let HI := (∫ p, K p ∂(μ.restrict I).prod (μ.restrict R)) / a
  let HP := (∫ p, K p ∂(μ.restrict J).prod (μ.restrict R)) / b
  change s < 1 ∧ 0 ≤ v ∧ s ^ 2 + v ^ 2 ≤ 2 * h ∧ 0 ≤ T ∧ _
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hJ : MeasurableSet J := (S.hfibers u.val u.property).1
  have hR : MeasurableSet R := (hI.union hJ).compl
  have hdis : Disjoint I J := Set.disjoint_left.mpr (fun x hx hy =>
    hpair.1 (Subtype.ext (hx.symm.trans hy)))
  have hIR : Disjoint I R := Set.disjoint_left.mpr (fun _ hx hy => hy (Or.inl hx))
  have ha : 0 < a := ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top _ _)
  have hb : 0 < b := ENNReal.toReal_pos (S.hfibers u.val u.property).2.1.ne' (measure_ne_top _ _)
  have hRmass : μ.real R = 1 - s := by
    dsimp only [R, s, a, b]
    rw [measureReal_compl (hI.union hJ), probReal_univ, measureReal_union hdis hJ]
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hK : Measurable K := hY
  have hKb (p : Ω × Ω) : ‖K p‖ ≤ 3 := PhysicalRepresentative.charge_bound W m p.1 p.2
  have hM : Measurable M := physicalMissing_measurable
  have hMb (p : Ω × Ω) : ‖M p‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (physicalMissing_mem p).1]
    exact (physicalMissing_mem p).2
  have hKsym (p : Ω × Ω) : K p = K p.swap := PhysicalRepresentative.charge_symm W m p.1 p.2
  have hMsym (p : Ω × Ω) : M p = M p.swap := by
    dsimp only [M, physicalMissing]
    rw [PhysicalRepresentative.adjacency_symm W m p.1 p.2]
    rfl
  obtain ⟨hIY, hIM, hIIY, hIIM⟩ := neutral_row_integrals S r hW hd hgap hNr
  obtain ⟨hJY, hJM, hJJY, hJJM⟩ := neutral_row_integrals S u hW hd hgap hNu
  have hIJY : (∫ p, K p ∂(μ.restrict I).prod (μ.restrict J)) = a * b := by
    have he : K =ᵐ[(μ.restrict I).prod (μ.restrict J)] fun _ => 1 := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) hpair.2,
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
          (PhysicalRepresentative.charge_ae_eq W m
            (hW.strict_gap_structure hd hgap).strict_support),
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hJ)] with p hp hy hi hj
      exact hy.trans (hp hi hj)
    rw [integral_congr_ae he, integral_one_rectangle]
  have hIJM : (∫ p, M p ∂(μ.restrict I).prod (μ.restrict J)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) (neutral_missing_row S r hW hd hgap hNr),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hJ)] with p hp hi hj
    have hn : p.2 ∉ I := fun hx => Set.disjoint_left.mp hdis hx hj
    have he : M p = I.indicator (fun _ => 1) p.2 := hp hi
    rw [indicator_of_notMem hn] at he
    exact he
  have htotalY : (∫ p, K p ∂μ.prod μ) = 2 * c := by
    have he := (PhysicalRepresentative.objective_eq W m
      (hW.strict_gap_structure hd hgap).strict_support).trans hW.objective_eq
    change (∫ p, K p ∂μ.prod μ) / 2 = c at he
    linarith only [he]
  have htotalM : (∫ p, M p ∂μ.prod μ) = h := by
    let G : Ω × Ω → ℝ := fun p => if A p.1 p.2 = true then 1 else 0
    have hGb (p : Ω × Ω) : ‖G p‖ ≤ 1 := by
      change ‖(if A p.1 p.2 = true then (1 : ℝ) else 0)‖ ≤ 1
      split_ifs <;> norm_num
    have hGi : Integrable G (μ.prod μ) := Integrable.of_bound
      (Measurable.ite (measurableSet_eq_fun hA measurable_const)
        measurable_const measurable_const).aestronglyMeasurable 1
      (Eventually.of_forall hGb)
    have he := (PhysicalRepresentative.density_eq W m
      (hW.strict_gap_structure hd hgap).strict_support).trans hW.density_eq
    change (∫ p, G p ∂μ.prod μ) / 2 = d at he
    change (∫ p, 1 - G p ∂μ.prod μ) = h
    rw [integral_sub (integrable_const 1) hGi, integral_const]
    simp only [probReal_univ, smul_eq_mul, mul_one]
    dsimp only [h]
    linarith only [he]
  have hpartitionM := integral_three_region_partition (μ := μ) M hM 1 hMb hMsym I J hI hJ hdis
  rw [htotalM, hIM, hJM, hIIM, hJJM, hIJM] at hpartitionM
  have hmissing : h = a ^ 2 + b ^ 2 + Q := by
    change h = 2 * a ^ 2 + 2 * b ^ 2 - a ^ 2 - b ^ 2 - 2 * 0 + Q at hpartitionM
    linarith only [hpartitionM]
  have hQ : 0 ≤ Q := integral_nonneg (fun p => (physicalMissing_mem p).1)
  have hcircle : s ^ 2 + v ^ 2 ≤ 2 * h := by
    dsimp only [s, v]
    nlinarith only [hmissing, hQ]
  have hs : s < 1 := by
    dsimp only [h] at hcircle
    nlinarith only [hcircle, hd.1, sq_nonneg v]
  have hv : 0 ≤ v := sub_nonneg.mpr horder
  have hsplitI := integral_split_regions (μ := μ) K hK 3 hKb I J hI hJ hdis (μ.restrict I)
  have hsplitJ := integral_split_regions (μ := μ) K hK 3 hKb I J hI hJ hdis (μ.restrict J)
  rw [hIY, hIIY, hIJY] at hsplitI
  rw [hJY, hJJY, integral_pair_swap K hKsym (μ.restrict J) (μ.restrict I), hIJY] at hsplitJ
  have hHI : HI = gamma - b - m * a := by
    apply (div_eq_iff ha.ne').mpr
    dsimp only [gamma, h]
    change a * (2 * (c - m * d) + m * (1 - a)) =
      0 + a * b + ∫ p, K p ∂(μ.restrict I).prod (μ.restrict R) at hsplitI
    nlinarith only [hsplitI]
  have hHP : HP = gamma - a - m * b := by
    apply (div_eq_iff hb.ne').mpr
    dsimp only [gamma, h]
    change b * (2 * (c - m * d) + m * (1 - b)) =
      a * b + 0 + ∫ p, K p ∂(μ.restrict J).prod (μ.restrict R) at hsplitJ
    nlinarith only [hsplitJ]
  have hpartitionY := integral_three_region_partition (μ := μ) K hK 3 hKb hKsym I J hI hJ hdis
  rw [htotalY, hIY, hJY, hIIY, hJJY, hIJY] at hpartitionY
  have hcharge : c = a * b + a * HI + b * HP + C₀ := by
    rw [hHI, hHP]
    change 2 * c = 2 * (a * (2 * (c - m * d) + m * (1 - a))) +
      2 * (b * (2 * (c - m * d) + m * (1 - b))) - 0 - 0 - 2 * (a * b) +
        ∫ p, K p ∂(μ.restrict R).prod (μ.restrict R) at hpartitionY
    dsimp only [C₀, FiniteCappedSamplingCost.physicalObjective, gamma, h, Y, K] at *
    nlinarith only [hpartitionY]
  have hcommon : {x | 0 < r.val x ∧ 0 < u.val x} =ᵐ[μ] R := by
    have hzeroR := (ae_restrict_iff' hI).mp (S.root_row_zero_on_fiber r)
    have hzeroU := (ae_restrict_iff' hJ).mp (S.root_row_zero_on_fiber u)
    filter_upwards [ae_neutral_row_positive S r hW hd hgap hNr,
      ae_neutral_row_positive S u hW hd hgap hNu, hzeroR, hzeroU] with x hr hu hzR hzU
    apply propext
    constructor
    · intro hx
      rintro (hxI | hxJ)
      · have he := hzR hxI
        linarith only [hx.1, he]
      · have he := hzU hxJ
        linarith only [hx.2, he]
    · intro hx
      exact ⟨hr (fun hi => hx (Or.inl hi)), hu (fun hj => hx (Or.inr hj))⟩
  have hcommonMass := hpair.common_neighbor_mass_bound hW hd hgap hell
  rw [measureReal_congr hcommon, hRmass] at hcommonMass
  have hT : 0 ≤ T := by
    dsimp only [T, gamma, h]
    nlinarith only [hcommonMass]
  have hphysical := S.neutral_atom_physical_adjacency r hW hd hgap hNr
  have hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), A p.1 p.2 = false := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) hphysical,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hI)] with p hp hx hy
    exact Bool.eq_false_iff.mpr (fun he => (hp hx).mp he hy)
  have hjoin : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict R), A p.1 p.2 = true := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) hphysical,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hR)] with p hp hx hy
    exact (hp hx).mpr (fun he => hy (Or.inl he))
  have hsupport := FiniteCappedSamplingCost.independent_head_support_optimized A
    (PhysicalRepresentative.adjacency_symm W m) hA Y hY 3 hKb
    (Eventually.of_forall (fun p => PhysicalRepresentative.charge_symm W m p.1 p.2))
    (Eventually.of_forall (fun p hp =>
      PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 hp))
    (PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic)
    I R hI hR (S.hfibers r.val r.property).2.1 hIR hind hjoin
  change C₀ ≤ (μ.real R) ^ 2 / 48 + Q / 2 - (12 / 25) * max (HI - μ.real R / 24) 0 ^ 2
    at hsupport
  rw [hRmass] at hsupport
  have henergy : 4 * (C₀ - Q / 2) =
      (1 + m) * (s - 2 * h) + 2 * m * v ^ 2 + (2 * s - 1) * T := by
    have heC : C₀ = c - a * b - a * HI - b * HP := by linarith only [hcharge]
    have heQ : Q = h - a ^ 2 - b ^ 2 := by linarith only [hmissing]
    rw [heC, heQ, hHI, hHP]
    dsimp only [s, v, T, gamma]
    ring
  have harg : (1 - m) * v - T - (1 - s) / 12 = 2 * (HI - (1 - s) / 24) := by
    rw [hHI]
    dsimp only [s, v, T]
    ring
  have hmax : max ((1 - m) * v - T - (1 - s) / 12) 0 =
      2 * max (HI - (1 - s) / 24) 0 := by
    rw [harg]
    by_cases hx : 0 ≤ HI - (1 - s) / 24
    · rw [max_eq_left hx, max_eq_left (mul_nonneg (by norm_num) hx)]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_right (by linarith only [le_of_not_ge hx])]
      ring
  refine ⟨hs, hv, hcircle, hT, ?_⟩
  change (1 + m) * (s - 2 * h) + 2 * m * v ^ 2 + (2 * s - 1) * T -
    (1 - s) ^ 2 / 12 + (12 / 25) * max ((1 - m) * v - T - (1 - s) / 12) 0 ^ 2 ≤ 0
  rw [hmax, ← henergy]
  nlinarith only [hsupport]

end Erdos1017.CappedModel.SelectedHighLowStructure
