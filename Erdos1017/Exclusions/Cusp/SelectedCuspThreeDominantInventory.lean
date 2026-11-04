module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeDominantCopy

/-!
# Inventory for the dominant missing atom

The original atom I and the designated source P form one independent union whose
square is disjoint from the body missing square, all rectangle moments belong to
the same positive body, and the designated atom and its remaining missing set
partition J.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original I and designated source P form one independent union.
Its entire square is disjoint from the same original body missing square. -/
theorem cusp_three_dominant_missing_body_square_le (S : SelectedHighLowStructure W m) (i j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    (∫ p : Ω × Ω, (IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) ≤
        1 - 2 * d - (S.originalAtomMass i + μ.real (S.cuspThreeDominantAtom i j)) ^ 2 := by
  let G := PhysicalRepresentative.adjacency W m
  let I := {x | S.ρ x = i.val}
  let P := S.cuspThreeDominantAtom i j
  let B := I ∪ P
  let D := S.rootNeighborhood i
  let J := IndependentAtomCopy.missingBody G Dᶜ
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := S.measurableSet_cuspThreeDominantAtom i j
  have hB : MeasurableSet B := hI.union hP
  have hIP : Disjoint I P := disjoint_left.mpr (fun _ hi hp => hp.2.1 hi)
  have hBD : Disjoint B D := disjoint_left.mpr (fun _ hb hd => hb.elim
    (fun hi => disjoint_left.mp (S.rootNeighborhood_disjoint i) hi hd) (fun hp => hp.2.2 hd))
  have hD : MeasurableSet D := S.measurableSet_rootNeighborhood i
  have hcross : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ P → G p.1 p.2 = false := by
    filter_upwards [S.ae_root_adjacency i hW hd hgap] with p hp hi hj
    exact Bool.eq_false_iff.mpr (fun ha => hj.2.2 ((hp hi).mp ha))
  have hindependent : ∀ᵐ p ∂μ.prod μ, p.1 ∈ B → p.2 ∈ B → G p.1 p.2 = false := by
    filter_upwards [S.ae_root_fiber_physical_independent i hW hd hgap,
      S.ae_root_fiber_physical_independent j hW hd hgap, hcross,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hcross] with p hi hj hc hc' hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hi hx hy
    · exact hc hx hy
    · exact (PhysicalRepresentative.adjacency_symm W m _ _).trans (hc' hy hx)
    · exact hj hx.1 hy.1
  have hJ := IndependentAtomCopy.measurable_missingBody G
    (PhysicalRepresentative.measurable_adjacency W m) Dᶜ hD.compl
  have hJsq : Integrable (fun p : Ω × Ω => (J p.1 p.2) ^ 2) (μ.prod μ) :=
    Integrable.of_bound (hJ.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        dsimp [J, IndependentAtomCopy.missingBody]
        split_ifs <;> norm_num))
  have hII := (integrable_const (1 : ℝ) (μ := μ.prod μ)).indicator (hB.prod hB)
  have hG : Integrable (fun p : Ω × Ω => if G p.1 p.2 = true then (1 : ℝ) else 0)
      (μ.prod μ) := Integrable.of_bound
    (Measurable.ite ((PhysicalRepresentative.measurable_adjacency W m)
      (measurableSet_singleton true)) measurable_const measurable_const).aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by split_ifs <;> norm_num))
  have hpoint : ∀ᵐ p ∂μ.prod μ, (J p.1 p.2) ^ 2 +
      (B ×ˢ B).indicator (fun _ => (1 : ℝ)) p ≤
      1 - (if G p.1 p.2 = true then (1 : ℝ) else 0) := by
    filter_upwards [hindependent] with p hp
    by_cases hxi : p.1 ∈ B
    · by_cases hyi : p.2 ∈ B
      · have hxd : p.1 ∉ D := fun h => Set.disjoint_left.mp hBD hxi h
        have hzero : G p.1 p.2 = false := hp hxi hyi
        simp [J, IndependentAtomCopy.missingBody, hxi, hyi, hxd, hzero]
      · cases hxy : G p.1 p.2 <;> by_cases hxd : p.1 ∈ D <;>
          by_cases hyd : p.2 ∈ D <;>
          simp [J, IndependentAtomCopy.missingBody, hxi, hyi, hxd, hyd, hxy]
    · cases hxy : G p.1 p.2 <;> by_cases hxd : p.1 ∈ D <;>
        by_cases hyd : p.2 ∈ D <;>
        simp [J, IndependentAtomCopy.missingBody, hxi, hxd, hyd, hxy]
  have hbound := integral_mono_ae (hJsq.add hII) ((integrable_const 1).sub hG) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  rw [integral_add hJsq hII, integral_indicator (hB.prod hB), setIntegral_const,
    smul_eq_mul, mul_one, measureReal_prod_prod,
    integral_sub (integrable_const 1) hG, integral_const, probReal_univ, smul_eq_mul, mul_one]
    at hbound
  have hdensity := PhysicalRepresentative.density_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  rw [hW.density_eq] at hdensity
  unfold FiniteCappedSamplingCost.physicalDensity at hdensity
  have hmass : μ.real B = S.originalAtomMass i + μ.real P := by
    exact measureReal_union hIP hP
  rw [hmass] at hbound
  dsimp only [G] at hbound
  nlinarith only [hbound, hdensity]


omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- All rectangle moments belong to the same original positive body.
Cauchy pays both opposite rectangles, including their zero boundaries. -/
theorem cusp_three_dominant_body_moments (S : SelectedHighLowStructure W m) (i j : S.I) :
    let D := S.rootNeighborhood i
    let U := S.cuspThreeDominantSource i j
    let N := D ∩ S.rootNeighborhood j
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) Dᶜ
    let X := ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ
    let L := ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ
    let C := ∫ p in U ×ˢ N, max (PhysicalRepresentative.charge W m p.1 p.2) 0 ∂μ.prod μ
    let R := ∫ p in U ×ˢ D, max (PhysicalRepresentative.charge W m p.1 p.2) 0 ∂μ.prod μ
    0 ≤ X ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ R ∧ R + C ≤ L ∧ 2 * C ≤ L ∧
      L ^ 2 ≤ X ∧ 2 * C ^ 2 ≤ μ.real U * μ.real N * X := by
  let Y := PhysicalRepresentative.charge W m
  let D := S.rootNeighborhood i
  let U := D \ S.rootNeighborhood j
  let N := D ∩ S.rootNeighborhood j
  let K := IndependentAtomCopy.positiveBody Y Dᶜ
  let T : Ω × Ω → ℝ := fun p => max (Y p.1 p.2) 0
  let X := ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ
  let L := ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ
  let C := ∫ p in U ×ˢ N, T p ∂μ.prod μ
  let R := ∫ p in U ×ˢ D, T p ∂μ.prod μ
  have hD : MeasurableSet D := S.measurableSet_rootNeighborhood i
  have hNj := S.measurableSet_rootNeighborhood j
  have hU : MeasurableSet U := hD.diff hNj
  have hN : MeasurableSet N := hD.inter hNj
  have hUN : Disjoint U N := disjoint_left.mpr (fun _ hu hn => hu.2 hn.2)
  have hY := PhysicalRepresentative.measurable_charge W m
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hKm := IndependentAtomCopy.measurable_positiveBody Y hY Dᶜ hD.compl
  have hK01 := IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1
  have hKB : ∀ x y, ‖K x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hK01 x y).1]
    exact (hK01 x y).2
  have hKl : MemLp (fun p : Ω × Ω => K p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hKm.aestronglyMeasurable 1 (Eventually.of_forall (fun p => hKB _ _))
  have hKi := hKl.integrable (by norm_num)
  have hTi : Integrable T (μ.prod μ) := Integrable.of_bound
    (hY.max measurable_const).aestronglyMeasurable 1 (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (hY1 _ _) (by norm_num)))
  have hswap : (∫ p in N ×ˢ U, T p ∂μ.prod μ) = C := by
    rw [← integral_indicator (hN.prod hU)]
    dsimp only [C]
    rw [← integral_indicator (hU.prod hN), ← integral_prod_swap (fun p : Ω × Ω => (U ×ˢ N).indicator T p)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hx : p.1 ∈ N <;> by_cases hy : p.2 ∈ U <;>
        simp [Set.indicator, hx, hy, T, Y, PhysicalRepresentative.charge_symm W m])
  have hRC : R + C ≤ L := by
    have hp : ∀ p : Ω × Ω, (U ×ˢ D).indicator T p + (N ×ˢ U).indicator T p ≤ K p.1 p.2 := by
      intro p
      by_cases hxD : p.1 ∈ D <;> by_cases hyD : p.2 ∈ D <;>
        by_cases hxN : p.1 ∈ S.rootNeighborhood j <;> by_cases hyN : p.2 ∈ S.rootNeighborhood j <;>
        simp [U, N, K, T, IndependentAtomCopy.positiveBody, Set.indicator, hxD, hyD, hxN, hyN]
    have hb := integral_mono_ae ((hTi.indicator (hU.prod hD)).add (hTi.indicator (hN.prod hU)))
      hKi (Eventually.of_forall hp)
    simp only [Pi.add_apply] at hb
    rw [integral_add (hTi.indicator (hU.prod hD)) (hTi.indicator (hN.prod hU)),
      integral_indicator (hU.prod hD), integral_indicator (hN.prod hU), hswap] at hb
    exact hb
  have hCR : C ≤ R := by
    have hp : ∀ p : Ω × Ω, (U ×ˢ N).indicator T p ≤ (U ×ˢ D).indicator T p := by
      intro p
      by_cases hxD : p.1 ∈ D <;> by_cases hyD : p.2 ∈ D <;>
        by_cases hxN : p.1 ∈ S.rootNeighborhood j <;> by_cases hyN : p.2 ∈ S.rootNeighborhood j <;>
        simp [U, N, T, Set.indicator, hxD, hyD, hxN, hyN]
    have hb := integral_mono_ae (hTi.indicator (hU.prod hN)) (hTi.indicator (hU.prod hD))
      (Eventually.of_forall hp)
    rwa [integral_indicator (hU.prod hN), integral_indicator (hU.prod hD)] at hb
  have hLsq : L ^ 2 ≤ X := by
    have hone : MemLp (fun _p : Ω × Ω => (1 : ℝ)) 2 (μ.prod μ) :=
      MemLp.of_bound measurable_const.aestronglyMeasurable 1 (Eventually.of_forall (fun _ => by norm_num))
    simpa only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul] using
      KernelOperator.integral_mul_sq_le (fun p : Ω × Ω => K p.1 p.2) (fun _ => (1 : ℝ)) hKl hone
  have hCauchy : 2 * C ^ 2 ≤ μ.real U * μ.real N * X := by
    let B := (U ×ˢ N) ∪ (N ×ˢ U)
    let f : Ω × Ω → ℝ := B.indicator (fun _ => 1)
    have hB : MeasurableSet B := (hU.prod hN).union (hN.prod hU)
    have hdis : Disjoint (U ×ˢ N) (N ×ˢ U) :=
      disjoint_left.mpr (fun _ hp hq => disjoint_left.mp hUN hp.1 hq.1)
    have hfl : MemLp f 2 (μ.prod μ) := MemLp.of_bound
      (measurable_const.indicator hB).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by by_cases hp : p ∈ B <;> simp [f, hp]))
    have hfsq : (∫ p, (f p) ^ 2 ∂μ.prod μ) = 2 * (μ.real U * μ.real N) := by
      have he : (fun p => (f p) ^ 2) = B.indicator (fun _ => (1 : ℝ)) := by
        funext p
        by_cases hp : p ∈ B <;> simp [f, Set.indicator, hp]
      rw [he, integral_indicator hB, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_union hdis (hN.prod hU), measureReal_prod_prod, measureReal_prod_prod]
      ring
    have hpair : (∫ p : Ω × Ω, K p.1 p.2 * f p ∂μ.prod μ) = 2 * C := by
      have he : (fun p : Ω × Ω => K p.1 p.2 * f p) =
          (U ×ˢ N).indicator T + (N ×ˢ U).indicator T := by
        funext p
        by_cases hxD : p.1 ∈ D <;> by_cases hyD : p.2 ∈ D <;>
          by_cases hxN : p.1 ∈ S.rootNeighborhood j <;> by_cases hyN : p.2 ∈ S.rootNeighborhood j <;>
          simp [f, B, U, N, K, T, IndependentAtomCopy.positiveBody, Set.indicator, hxD, hyD, hxN, hyN]
      rw [he]
      change (∫ p, (U ×ˢ N).indicator T p + (N ×ˢ U).indicator T p ∂μ.prod μ) = 2 * C
      rw [integral_add (hTi.indicator (hU.prod hN)) (hTi.indicator (hN.prod hU)),
        integral_indicator (hU.prod hN), integral_indicator (hN.prod hU), hswap]
      dsimp only [C]
      ring
    have hb := KernelOperator.integral_mul_sq_le (fun p : Ω × Ω => K p.1 p.2) f hKl hfl
    rw [hfsq, hpair] at hb
    change (2 * C) ^ 2 ≤ X * (2 * (μ.real U * μ.real N)) at hb
    nlinarith only [hb]
  change 0 ≤ X ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ R ∧ R + C ≤ L ∧ 2 * C ≤ L ∧
    L ^ 2 ≤ X ∧ 2 * C ^ 2 ≤ μ.real U * μ.real N * X
  exact ⟨integral_nonneg (fun _ => sq_nonneg _), integral_nonneg (fun p => (hK01 p.1 p.2).1),
    integral_nonneg (fun _ => le_max_right _ _), integral_nonneg (fun _ => le_max_right _ _),
    hRC, by linarith only [hRC, hCR], hLsq, hCauchy⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The designated atom and its entire remaining missing set partition J;
the original body neighbors occupy only the complement of I and P. -/
theorem cusp_three_dominant_masses (S : SelectedHighLowStructure W m) (i j : S.I) :
    let P := S.cuspThreeDominantAtom i j
    let J := S.cuspThreeMissingRegion i
    let N := S.rootNeighborhood i ∩ S.rootNeighborhood j
    μ.real P + μ.real (J \ P) = μ.real J ∧
      μ.real N ≤ 1 - S.originalAtomMass i - μ.real P := by
  let I := {x | S.ρ x = i.val}
  let P := S.cuspThreeDominantAtom i j
  let J := S.cuspThreeMissingRegion i
  let N := S.rootNeighborhood i ∩ S.rootNeighborhood j
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := S.measurableSet_cuspThreeDominantAtom i j
  have hIP : Disjoint I P := disjoint_left.mpr (fun _ hi hp => hp.2.1 hi)
  have hPsub : P ⊆ J := fun _ hp => hp.2
  have hpart := measureReal_inter_add_sdiff (μ := μ) (s := J) hP
  rw [inter_eq_right.mpr hPsub] at hpart
  have hNsub : N ⊆ (I ∪ P)ᶜ := by
    intro x hx hn
    rcases hn with hi | hp
    · exact disjoint_left.mp (S.rootNeighborhood_disjoint i) hi hx.1
    · exact hp.2.2 hx.1
  have hn := measureReal_mono (μ := μ) hNsub
  rw [measureReal_compl (hI.union hP), probReal_univ, measureReal_union hIP hP] at hn
  refine ⟨hpart, ?_⟩
  change μ.real N ≤ 1 - μ.real I - μ.real P
  simpa only [sub_add_eq_sub_sub] using hn

end Erdos1017.CappedModel.SelectedHighLowStructure
