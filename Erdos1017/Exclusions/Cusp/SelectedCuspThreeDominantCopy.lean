module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeDominantPayment
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeNeighborhoodTrace
public import Erdos1017.Exclusions.Cusp.DominantCopyTrace

/-!
# Common-copy row for a dominant source atom

The designated source atom pays its two opposite body rectangles while the
remaining source set pays at most its mass once, the common-copy row keeps these
rectangles, and the same positive body pays the designated-atom tax `2bC` plus
one copy of the remainder mass `r`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The designated source atom pays only its two opposite body rectangles;
the entire remaining source set pays at most its mass once. -/
theorem missing_pair_integral_le_dominant (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (I D P N : Set Ω)
    (hI : MeasurableSet I) (hD : MeasurableSet D) (hP : MeasurableSet P)
    (hID : Disjoint I D) (hPsub : P ⊆ Iᶜ \ D)
    (hYB : ∀ x y, ‖Y x y‖ ≤ 3) (hY1 : ∀ x y, Y x y ≤ 1)
    (hzero : ∀ x y, G x y = false → Y x y = 0)
    (hsym : ∀ x y, Y x y = Y y x) (x y : Ω) (hx : x ∈ D) (hy : y ∈ D)
    (hcommon : ∀ᵐ z ∂μ, z ∈ I → G x z = true ∧ G y z = true)
    (hProw : ∀ᵐ z ∂μ, z ∈ P →
      (G x z = true ↔ x ∈ N) ∧ (G y z = true ↔ y ∈ N)) :
    (∫ z in missingSection G x, Y y z ∂μ) +
      (∫ z in missingSection G y, Y x z ∂μ) ≤
      KernelOperator.composedKernel (μ := μ) (missingBody G Dᶜ) (positiveBody Y Dᶜ) x y +
      KernelOperator.composedKernel (μ := μ) (missingBody G Dᶜ) (positiveBody Y Dᶜ) y x +
      μ.real P * (if (x ∈ N ∧ y ∉ N) ∨ (y ∈ N ∧ x ∉ N) then 1 else 0) +
      μ.real ((Iᶜ \ D) \ P) := by
  let K := positiveBody Y Dᶜ
  let J := missingBody G Dᶜ
  let mask : ℝ := if (x ∈ N ∧ y ∉ N) ∨ (y ∈ N ∧ x ∉ N) then 1 else 0
  let R := (Iᶜ \ D) \ P
  have hR : MeasurableSet R := (hI.compl.diff hD).diff hP
  have hK := measurable_positiveBody Y hY Dᶜ hD.compl
  have hJ := measurable_missingBody G hG Dᶜ hD.compl
  have hrow (u : Ω) : Integrable (Y u) μ := Integrable.of_bound
    (hY.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    (Eventually.of_forall (hYB u))
  have hprod (u v : Ω) : Integrable (fun z => J u z * K z v) μ :=
    Integrable.of_bound
      ((hJ.comp (measurable_const.prodMk measurable_id)).mul
        (hK.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable 1
      (Eventually.of_forall (fun z => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (missingBody_mem G Dᶜ u z).1,
          abs_of_nonneg (positiveBody_mem Y Dᶜ hY1 z v).1]
        exact (mul_le_mul (missingBody_mem G Dᶜ u z).2
          (positiveBody_mem Y Dᶜ hY1 z v).2
          (positiveBody_mem Y Dᶜ hY1 z v).1 zero_le_one).trans_eq (mul_one 1)))
  have htaxP := (integrable_const mask (μ := μ)).indicator hP
  have htaxR := (integrable_const (1 : ℝ) (μ := μ)).indicator hR
  have hprodAdd : Integrable (fun z => J x z * K z y + J y z * K z x) μ :=
    (hprod x y).add (hprod y x)
  have hbound : (∫ z, (missingSection G x).indicator (Y y) z +
      (missingSection G y).indicator (Y x) z ∂μ) ≤
      ∫ z, J x z * K z y + J y z * K z x +
        P.indicator (fun _ => mask) z + R.indicator (fun _ => (1 : ℝ)) z ∂μ := by
    apply integral_mono_ae ((hrow y).indicator (measurableSet_missingSection G hG x) |>.add
      ((hrow x).indicator (measurableSet_missingSection G hG y)))
      ((hprodAdd.add htaxP).add htaxR)
    filter_upwards [hcommon, hProw] with z hz hp
    by_cases hzi : z ∈ I
    · have hzd : z ∉ D := fun h => disjoint_left.mp hID hzi h
      have hzp : z ∉ P := fun h => (hPsub h).1 hzi
      obtain ⟨hGx, hGy⟩ := hz hzi
      simp [J, K, R, missingSection, missingBody, positiveBody, hzi, hzd, hzp, hGx, hGy]
    · by_cases hzd : z ∈ D
      · have hzp : z ∉ P := fun h => (hPsub h).2 hzd
        cases hGx : G x z <;> cases hGy : G y z <;>
          simp [J, K, R, missingSection, missingBody, positiveBody, hx, hy, hzi, hzd,
            hzp, hGx, hGy, hsym z x, hsym z y]
        exact add_le_add (le_max_left _ _) (le_max_left _ _)
      · by_cases hzp : z ∈ P
        · obtain ⟨hpx, hpy⟩ := hp hzp
          have htax : (missingSection G x).indicator (Y y) z +
              (missingSection G y).indicator (Y x) z ≤ mask := by
            cases hGx : G x z <;> cases hGy : G y z
            · have hxN : x ∉ N := fun hn => Bool.false_ne_true (hGx.symm.trans (hpx.mpr hn))
              have hyN : y ∉ N := fun hn => Bool.false_ne_true (hGy.symm.trans (hpy.mpr hn))
              simp [mask, missingSection, hGx, hGy, hxN, hyN, hzero x z hGx, hzero y z hGy]
            · have hxN : x ∉ N := fun hn => Bool.false_ne_true (hGx.symm.trans (hpx.mpr hn))
              have hyN : y ∈ N := hpy.mp hGy
              simpa [mask, missingSection, hGx, hGy, hxN, hyN] using hY1 y z
            · have hxN : x ∈ N := hpx.mp hGx
              have hyN : y ∉ N := fun hn => Bool.false_ne_true (hGy.symm.trans (hpy.mpr hn))
              simpa [mask, missingSection, hGx, hGy, hxN, hyN] using hY1 x z
            · have hxN : x ∈ N := hpx.mp hGx
              have hyN : y ∈ N := hpy.mp hGy
              simp [mask, missingSection, hGx, hGy, hxN, hyN]
          simpa [J, K, R, missingBody, positiveBody, hzi, hzd, hzp] using htax
        · simpa [J, K, R, missingBody, positiveBody, hzi, hzd, hzp] using
            missing_row_tax_le_one G Y hzero hY1 x y z
  have hleft := integral_add ((hrow y).indicator (measurableSet_missingSection G hG x))
    ((hrow x).indicator (measurableSet_missingSection G hG y))
  have hright₁ := integral_add (hprodAdd.add htaxP) htaxR
  have hright₂ := integral_add hprodAdd htaxP
  simp only [Pi.add_apply] at hleft hright₁ hright₂
  rw [hleft, integral_indicator (measurableSet_missingSection G hG x),
    integral_indicator (measurableSet_missingSection G hG y), hright₁, hright₂,
    integral_add (hprod x y) (hprod y x), integral_indicator hP, integral_indicator hR,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one] at hbound
  exact hbound

end Erdos1017.IndependentAtomCopy

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual common-copy row retains the designated source's opposite
rectangles and pays the entire remaining missing region only once. -/
theorem ae_cusp_three_dominant_copy_row (S : SelectedHighLowStructure W m) (i j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    let P := S.cuspThreeDominantAtom i j
    let D := S.rootNeighborhood i
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) Dᶜ
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) Dᶜ
    ∀ᵐ p ∂μ.prod μ, S.originalAtomMass i * (K p.1 p.2) ^ 2 +
      (2 * (c - m * d) + m - μ.real (S.cuspThreeMissingRegion i \ P)) * K p.1 p.2 ≤
      K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
        KernelOperator.composedKernel (μ := μ) J K p.2 p.1) +
      μ.real P * K p.1 p.2 *
        (if (p.1 ∈ S.rootNeighborhood j ∧ p.2 ∉ S.rootNeighborhood j) ∨
          (p.2 ∈ S.rootNeighborhood j ∧ p.1 ∉ S.rootNeighborhood j) then 1 else 0) := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = i.val}
  let D := S.rootNeighborhood i
  let P := S.cuspThreeDominantAtom i j
  let K := IndependentAtomCopy.positiveBody Y Dᶜ
  let J := IndependentAtomCopy.missingBody G Dᶜ
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hswapI := Measure.measurePreserving_swap.quasiMeasurePreserving.ae (S.ae_root_adjacency i hW hd hgap)
  have hrowsI : ∀ᵐ x ∂μ, x ∈ D → ∀ᵐ z ∂μ, z ∈ I → G x z = true := by
    filter_upwards [Measure.ae_ae_of_ae_prod hswapI] with x hx hxd
    filter_upwards [hx] with z hz hzi
    exact (PhysicalRepresentative.adjacency_symm W m x z).trans ((hz hzi).mpr hxd)
  have hswapP := Measure.measurePreserving_swap.quasiMeasurePreserving.ae (S.ae_root_adjacency j hW hd hgap)
  have hrowsP : ∀ᵐ x ∂μ, ∀ᵐ z ∂μ, z ∈ P → (G x z = true ↔ x ∈ S.rootNeighborhood j) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hswapP] with x hx
    filter_upwards [hx] with z hz hzp
    change PhysicalRepresentative.adjacency W m x z = true ↔ _
    rw [PhysicalRepresentative.adjacency_symm W m]
    exact hz hzp.1
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  filter_upwards [S.ae_common_neighborhood_copy_inequality i hW hd hgap,
    Measure.quasiMeasurePreserving_fst.ae hrowsI, Measure.quasiMeasurePreserving_snd.ae hrowsI,
    Measure.quasiMeasurePreserving_fst.ae hrowsP, Measure.quasiMeasurePreserving_snd.ae hrowsP]
    with p hp hx hy hpx hpy
  change μ.real I * (K p.1 p.2) ^ 2 +
    (2 * (c - m * d) + m - μ.real ((Iᶜ \ D) \ P)) * K p.1 p.2 ≤
      K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
        KernelOperator.composedKernel (μ := μ) J K p.2 p.1) + μ.real P * K p.1 p.2 *
        (if (p.1 ∈ S.rootNeighborhood j ∧ p.2 ∉ S.rootNeighborhood j) ∨
          (p.2 ∈ S.rootNeighborhood j ∧ p.1 ∉ S.rootNeighborhood j) then 1 else 0)
  by_cases hpos : 0 < K p.1 p.2
  · have hout : p.1 ∈ D ∧ p.2 ∈ D := by
      by_contra h
      simp [K, IndependentAtomCopy.positiveBody, h] at hpos
    have hKeq : K p.1 p.2 = Y p.1 p.2 := by
      have hmax : 0 < max (Y p.1 p.2) 0 := by
        simpa [K, IndependentAtomCopy.positiveBody, hout] using hpos
      have hypos : 0 < Y p.1 p.2 := by
        simpa only [lt_max_iff, lt_self_iff_false, or_false] using hmax
      simp [K, IndependentAtomCopy.positiveBody, hout, max_eq_left hypos.le]
    have hypos : 0 < Y p.1 p.2 := by rwa [hKeq] at hpos
    have hc := hp hout.1 hout.2 hypos
    have hcommon : ∀ᵐ z ∂μ, z ∈ I → G p.1 z = true ∧ G p.2 z = true := by
      filter_upwards [hx hout.1, hy hout.2] with z hx hy hi
      exact ⟨hx hi, hy hi⟩
    have hProw : ∀ᵐ z ∂μ, z ∈ P →
        (G p.1 z = true ↔ p.1 ∈ S.rootNeighborhood j) ∧
        (G p.2 z = true ↔ p.2 ∈ S.rootNeighborhood j) := by
      filter_upwards [hpx, hpy] with z hx hy hp
      exact ⟨hx hp, hy hp⟩
    have hpair := IndependentAtomCopy.missing_pair_integral_le_dominant G
      (PhysicalRepresentative.measurable_adjacency W m) Y
      (PhysicalRepresentative.measurable_charge W m) I D P (S.rootNeighborhood j)
      (S.hfibers i.val i.property).1 (S.measurableSet_rootNeighborhood i)
      (S.measurableSet_cuspThreeDominantAtom i j) (S.rootNeighborhood_disjoint i)
      (fun _ hp => hp.2) (PhysicalRepresentative.charge_bound W m) hY1
      (PhysicalRepresentative.charge_zero_of_nonedge W m) (PhysicalRepresentative.charge_symm W m)
      p.1 p.2 hout.1 hout.2 hcommon hProw
    have hmass : 0 ≤ μ.real (IndependentAtomCopy.missingSection G p.1 ∩
        IndependentAtomCopy.missingSection G p.2) := measureReal_nonneg
    have hbound : μ.real I * K p.1 p.2 + (2 * (c - m * d) + m - μ.real ((Iᶜ \ D) \ P)) ≤
        KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
          KernelOperator.composedKernel (μ := μ) J K p.2 p.1 +
            μ.real P * (if (p.1 ∈ S.rootNeighborhood j ∧ p.2 ∉ S.rootNeighborhood j) ∨
              (p.2 ∈ S.rootNeighborhood j ∧ p.1 ∉ S.rootNeighborhood j) then 1 else 0) := by
      change μ.real I * Y p.1 p.2 + _ - m * μ.real _ ≤ _ at hc
      rw [hKeq]
      dsimp only [J, K] at *
      nlinarith only [hc, hpair, mul_nonpos_of_nonpos_of_nonneg hm.le hmass]
    have h := mul_le_mul_of_nonneg_right hbound hpos.le
    nlinarith only [h]
  · have hzero : K p.1 p.2 = 0 := le_antisymm (le_of_not_gt hpos)
      (IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1 p.1 p.2).1
    rw [hzero]
    simp

/-- The same original positive body pays the refined designated-atom tax
2bC and one copy of the entire remainder mass r. -/
theorem cusp_three_dominant_positive_body_trace (S : SelectedHighLowStructure W m) (i j : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpositive : 0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) :
    let P := S.cuspThreeDominantAtom i j
    let U := S.cuspThreeDominantSource i j
    let D := S.rootNeighborhood i
    let N := D ∩ S.rootNeighborhood j
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) Dᶜ
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) Dᶜ
    (S.originalAtomMass i - Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ))) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
      (2 * (c - m * d) + m - μ.real (S.cuspThreeMissingRegion i \ P)) *
        (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) ≤
      2 * μ.real P * (∫ p in U ×ˢ N, max (PhysicalRepresentative.charge W m p.1 p.2) 0 ∂μ.prod μ) := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let P := S.cuspThreeDominantAtom i j
  let D := S.rootNeighborhood i
  let U := S.cuspThreeDominantSource i j
  let N := D ∩ S.rootNeighborhood j
  let K := IndependentAtomCopy.positiveBody Y Dᶜ
  let J := IndependentAtomCopy.missingBody G Dᶜ
  let T : Ω × Ω → ℝ := fun p => max (Y p.1 p.2) 0
  let Q : Set (Ω × Ω) := {p | (p.1 ∈ S.rootNeighborhood j ∧ p.2 ∉ S.rootNeighborhood j) ∨
    (p.2 ∈ S.rootNeighborhood j ∧ p.1 ∉ S.rootNeighborhood j)}
  let F : Ω × Ω → ℝ := fun p => μ.real P * Q.indicator (Function.uncurry K) p
  have hD : MeasurableSet D := S.measurableSet_rootNeighborhood i
  have hU : MeasurableSet U := S.measurableSet_cuspThreeDominantSource i j
  have hNj := S.measurableSet_rootNeighborhood j
  have hN : MeasurableSet N := hD.inter hNj
  have hQ : MeasurableSet Q := by
    convert (hNj.prod hNj.compl).union (hNj.compl.prod hNj) using 1
    ext p
    simp only [Q, mem_ofPred_eq, mem_union, mem_prod, mem_compl_iff]
    tauto
  have hY := PhysicalRepresentative.measurable_charge W m
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hK := IndependentAtomCopy.measurable_positiveBody Y hY Dᶜ hD.compl
  have hJ := IndependentAtomCopy.measurable_missingBody G
    (PhysicalRepresentative.measurable_adjacency W m) Dᶜ hD.compl
  have hKB : ∀ x y, ‖K x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1 x y).1]
    exact (IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1 x y).2
  have hKi : Integrable (Function.uncurry K) (μ.prod μ) :=
    Integrable.of_bound hK.aestronglyMeasurable 1 (Eventually.of_forall (fun p => hKB _ _))
  have hF : Integrable F (μ.prod μ) := (hKi.indicator hQ).const_mul (μ.real P)
  have hT : Measurable T := hY.max measurable_const
  have hTi : Integrable T (μ.prod μ) := Integrable.of_bound hT.aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (hY1 _ _) (by norm_num)))
  have hFint : (∫ p, F p ∂μ.prod μ) =
      2 * μ.real P * (∫ p in U ×ˢ N, T p ∂μ.prod μ) := by
    have he : Q.indicator (Function.uncurry K) =
        (U ×ˢ N).indicator T + (N ×ˢ U).indicator T := by
      funext p
      change Q.indicator (fun p : Ω × Ω => K p.1 p.2) p =
        ((D \ S.rootNeighborhood j) ×ˢ (D ∩ S.rootNeighborhood j)).indicator T p +
          ((D ∩ S.rootNeighborhood j) ×ˢ (D \ S.rootNeighborhood j)).indicator T p
      by_cases hxD : p.1 ∈ D <;> by_cases hyD : p.2 ∈ D <;>
        by_cases hxN : p.1 ∈ S.rootNeighborhood j <;> by_cases hyN : p.2 ∈ S.rootNeighborhood j <;>
        simp [Q, K, T, IndependentAtomCopy.positiveBody, Set.indicator, hxD, hyD, hxN, hyN]
    have hswap : (∫ p in N ×ˢ U, T p ∂μ.prod μ) = ∫ p in U ×ˢ N, T p ∂μ.prod μ := by
      rw [← integral_indicator (hN.prod hU), ← integral_indicator (hU.prod hN)]
      rw [← integral_prod_swap (fun p : Ω × Ω => (U ×ˢ N).indicator T p)]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        by_cases hx : p.1 ∈ N <;> by_cases hy : p.2 ∈ U <;>
          simp [Set.indicator, hx, hy, T, Y, PhysicalRepresentative.charge_symm W m])
    change (∫ p, μ.real P * Q.indicator (Function.uncurry K) p ∂μ.prod μ) = _
    rw [integral_const_mul, he]
    simp only [Pi.add_apply]
    rw [integral_add (hTi.indicator (hU.prod hN)) (hTi.indicator (hN.prod hU)),
      integral_indicator (hU.prod hN), integral_indicator (hN.prod hU), hswap]
    ring
  have horth : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0 := by
    calc
      _ = ∫ _p : Ω × Ω, (0 : ℝ) ∂μ.prod μ := integral_congr_ae (Eventually.of_forall (fun p =>
        IndependentAtomCopy.missingBody_positiveBody_mul G Y Dᶜ
          (PhysicalRepresentative.charge_zero_of_nonedge W m) p.1 p.2))
      _ = 0 := integral_zero _ _
  have hrow := S.ae_cusp_three_dominant_copy_row i j hW hd hgap
  have htrace := KernelOperator.signed_copy_row_trace_bound_with_tax K J hK hJ
    (IndependentAtomCopy.positiveBody_mem Y Dᶜ hY1)
    (fun x y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.missingBody_mem G Dᶜ x y).1]
      exact (IndependentAtomCopy.missingBody_mem G Dᶜ x y).2)
    (IndependentAtomCopy.positiveBody_symm Y Dᶜ (PhysicalRepresentative.charge_symm W m))
    (S.originalAtomMass i) (2 * (c - m * d) + m - μ.real (S.cuspThreeMissingRegion i \ P))
    F hF hpositive horth (by
      filter_upwards [hrow] with p hp
      change S.originalAtomMass i * (K p.1 p.2) ^ 2 +
        (2 * (c - m * d) + m - μ.real (S.cuspThreeMissingRegion i \ P)) * K p.1 p.2 ≤
        K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
          KernelOperator.composedKernel (μ := μ) J K p.2 p.1) + μ.real P * K p.1 p.2 *
          (if (p.1 ∈ S.rootNeighborhood j ∧ p.2 ∉ S.rootNeighborhood j) ∨
            (p.2 ∈ S.rootNeighborhood j ∧ p.1 ∉ S.rootNeighborhood j) then 1 else 0) at hp
      simpa [F, Q, Set.indicator, Function.uncurry, mul_assoc] using hp)
  rw [hFint] at htrace
  exact htrace

end Erdos1017.CappedModel.SelectedHighLowStructure
