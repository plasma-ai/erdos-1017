module

public import Erdos1017.Exclusions.Common.Universal.UniversalCopyBody
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateBodyInventory

/-!
# Cubic trace of a private positive body

The copied row retains the private missing atom's signed charge on one
product-almost-everywhere event, and the private inventory makes the
positive-body trace strict, with the zero-body case left to a separate argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.IndependentAtomCopy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem missing_integral_le_private_body_composed (G : Ω → Ω → Bool)
    (hG : Measurable (Function.uncurry G)) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (I P U : Set Ω)
    (hI : MeasurableSet I) (hP : MeasurableSet P) (hIP : Disjoint I P)
    (hYB : ∀ x y, ‖Y x y‖ ≤ 3) (hY1 : ∀ x y, Y x y ≤ 1)
    (hsym : ∀ x y, Y x y = Y y x) (β : Ω → ℝ) (x y : Ω)
    (hx : x ∉ I ∪ P) (hy : y ∉ I ∪ P)
    (hcommon : ∀ᵐ z ∂μ, z ∈ I → G x z = true)
    (hmissing : ∀ᵐ z ∂μ, z ∈ P → (G x z = false ↔ x ∈ U))
    (hcharge : ∀ᵐ z ∂μ, z ∈ P → Y y z = β y) :
    (∫ z in missingSection G x, Y y z ∂μ) ≤
      KernelOperator.composedKernel (μ := μ) (missingBody G (I ∪ P))
        (positiveBody Y (I ∪ P)) x y +
          μ.real P * (U.indicator (fun _ => (1 : ℝ)) x * β y) := by
  have hE := hI.union hP
  have hms := measurableSet_missingSection G hG x
  have hiY : Integrable (Y y) μ := Integrable.of_bound
    (hY.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 3
    (Eventually.of_forall (hYB y))
  have hiK : Integrable (fun z => missingBody G (I ∪ P) x z *
      positiveBody Y (I ∪ P) z y) μ := Integrable.of_bound
    (((measurable_missingBody G hG (I ∪ P) hE).comp
      (measurable_const.prodMk measurable_id)).mul
      ((measurable_positiveBody Y hY (I ∪ P) hE).comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (missingBody_mem G (I ∪ P) x z).1,
        abs_of_nonneg (positiveBody_mem Y (I ∪ P) hY1 z y).1]
      exact (mul_le_mul (missingBody_mem G (I ∪ P) x z).2
        (positiveBody_mem Y (I ∪ P) hY1 z y).2
        (positiveBody_mem Y (I ∪ P) hY1 z y).1 zero_le_one).trans_eq (mul_one 1)))
  have hiP : Integrable (P.indicator
      (fun _ => U.indicator (fun _ => (1 : ℝ)) x * β y)) μ :=
    (integrable_const _).indicator hP
  have hbound : (missingSection G x).indicator (Y y) ≤ᵐ[μ]
      fun z => missingBody G (I ∪ P) x z * positiveBody Y (I ∪ P) z y +
        P.indicator (fun _ => U.indicator (fun _ => (1 : ℝ)) x * β y) z := by
    filter_upwards [hcommon, hmissing, hcharge] with z hzI hzP hzY
    by_cases hzI' : z ∈ I
    · have hzP' : z ∉ P := fun hp => Set.disjoint_left.mp hIP hzI' hp
      simp [missingSection, missingBody, positiveBody, hzI hzI', hzI', hzP']
    · by_cases hzP' : z ∈ P
      · have hmem := hzP hzP'
        have heq := hzY hzP'
        by_cases hxU : x ∈ U
        · simp [missingSection, missingBody, positiveBody, hzP',
            hmem.mpr hxU, hxU, heq]
        · have hGfalse : G x z ≠ false := fun hg => hxU (hmem.mp hg)
          simp [missingSection, missingBody, positiveBody, hzP', hGfalse, hxU]
      · have hzE : z ∉ I ∪ P := by simp [hzI', hzP']
        by_cases hg : G x z = false
        · simp [missingSection, missingBody, positiveBody, hx, hy, hzE, hg,
            hzP', hsym z y]
        · simp [missingSection, missingBody, hg, hzP']
  have hi := integral_mono_ae (hiY.indicator hms) (hiK.add hiP) hbound
  change (∫ z, (missingSection G x).indicator (Y y) z ∂μ) ≤
    ∫ z, missingBody G (I ∪ P) x z * positiveBody Y (I ∪ P) z y +
      P.indicator (fun _ => U.indicator (fun _ => (1 : ℝ)) x * β y) z ∂μ at hi
  rw [integral_add hiK hiP, integral_indicator hms, integral_indicator hP,
    setIntegral_const, smul_eq_mul] at hi
  exact hi

end Erdos1017.IndependentAtomCopy

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual old copied row retains the private missing atom's signed
charge. All source sections come from the same original product-AE event. -/
theorem ae_private_positive_body_row (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) :
    let I := {x | S.ρ x = r.val}
    let P := {x | S.ρ x = u.val}
    let E := I ∪ P
    let U := Eᶜ \ S.rootNeighborhood u
    let β := S.rootChargeRow u
    let K := IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) E
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) E
    ∀ᵐ p ∂μ.prod μ, μ.real I * (K p.1 p.2) ^ 2 +
      (2 * (c - m * d) + m) * K p.1 p.2 ≤
      K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
        KernelOperator.composedKernel (μ := μ) J K p.2 p.1 + μ.real P *
          (U.indicator (fun _ => (1 : ℝ)) p.1 * β p.2 +
            β p.1 * U.indicator (fun _ => (1 : ℝ)) p.2)) := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = u.val}
  let E := I ∪ P
  let U := Eᶜ \ S.rootNeighborhood u
  let β := S.rootChargeRow u
  let K := IndependentAtomCopy.positiveBody Y E
  let J := IndependentAtomCopy.missingBody G E
  have hG := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hI := (S.hfibers r.val r.property).1
  have hP := (S.hfibers u.val u.property).1
  have hIP : Disjoint I P := Set.disjoint_left.mpr (fun _ hx hy =>
    hru (Subtype.ext (hx.symm.trans hy)))
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y =>
    (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hphysical : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → (G p.1 p.2 = true ↔ p.2 ∉ E) := by
    filter_upwards [hprivate, PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with p hp ha hi
    have heq := ha.symm.trans (hp hi)
    change (if G p.1 p.2 = true then (1 : ℝ) else 0) =
      (if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) at heq
    by_cases he : S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val <;>
      cases hg : G p.1 p.2 <;> simp_all [E, I, P]
  have hreverse :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hphysical
  have hrows : ∀ᵐ x ∂μ, x ∉ E → ∀ᵐ z ∂μ, z ∈ I → G x z = true := by
    filter_upwards [Measure.ae_ae_of_ae_prod hreverse] with x hx hxe
    filter_upwards [hx] with z hz hzi
    change PhysicalRepresentative.adjacency W m x z = true
    rw [PhysicalRepresentative.adjacency_symm W m]
    exact (hz hzi).mpr hxe
  have hpAdj := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency u hW hd hgap)
  have hpCharge :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_root_charge u hW hd hgap)
  have hmissing : ∀ᵐ x ∂μ, x ∉ E →
      ∀ᵐ z ∂μ, z ∈ P → (G x z = false ↔ x ∈ U) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hpAdj] with x hx hxe
    filter_upwards [hx] with z hz hzp
    have he := hz hzp
    change PhysicalRepresentative.adjacency W m z x = true ↔ x ∈ S.rootNeighborhood u at he
    rw [← PhysicalRepresentative.adjacency_symm W m x z] at he
    constructor
    · intro hg
      refine ⟨hxe, ?_⟩
      intro hn
      have ht := he.mpr hn
      change G x z = true at ht
      rw [hg] at ht
      contradiction
    · intro hu
      exact Bool.eq_false_iff.mpr (fun ht => hu.2 (he.mp ht))
  have hcharge : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, z ∈ P → Y y z = β y := by
    filter_upwards [Measure.ae_ae_of_ae_prod hpCharge] with y hy
    filter_upwards [hy] with z hz hzp
    change PhysicalRepresentative.charge W m y z = S.rootChargeRow u y
    rw [PhysicalRepresentative.charge_symm W m y z]
    exact hz hzp
  have hflat := S.ae_physical_shifted_stationary hW hd hgap
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  filter_upwards [S.ae_atom_copy_shifted_row_le_stationary r hW hd hgap,
    Measure.quasiMeasurePreserving_fst.ae hrows, Measure.quasiMeasurePreserving_snd.ae hrows,
    Measure.quasiMeasurePreserving_fst.ae hmissing,
    Measure.quasiMeasurePreserving_snd.ae hmissing,
    Measure.quasiMeasurePreserving_fst.ae hcharge, Measure.quasiMeasurePreserving_snd.ae hcharge,
    Measure.quasiMeasurePreserving_fst.ae hflat, Measure.quasiMeasurePreserving_snd.ae hflat]
    with p hp hx hy hmx hmy hcx hcy hfx hfy
  change μ.real I * (K p.1 p.2) ^ 2 + (2 * (c - m * d) + m) * K p.1 p.2 ≤
    K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
      KernelOperator.composedKernel (μ := μ) J K p.2 p.1 + μ.real P *
        (U.indicator (fun _ => (1 : ℝ)) p.1 * β p.2 +
          β p.1 * U.indicator (fun _ => (1 : ℝ)) p.2))
  by_cases hpos : 0 < K p.1 p.2
  · have hout : p.1 ∉ E ∧ p.2 ∉ E := by
      by_contra h
      simp [K, IndependentAtomCopy.positiveBody, h] at hpos
    have hKeq : K p.1 p.2 = Y p.1 p.2 := by
      have hmax : 0 < max (Y p.1 p.2) 0 := by
        simpa [K, IndependentAtomCopy.positiveBody, hout] using hpos
      have hypos : 0 < Y p.1 p.2 := by
        simpa only [lt_max_iff, lt_self_iff_false, or_false] using hmax
      simp [K, IndependentAtomCopy.positiveBody, hout, max_eq_left hypos.le]
    have hypos : 0 < Y p.1 p.2 := by rwa [hKeq] at hpos
    have hg : G p.1 p.2 = true := by
      by_contra hn
      have hz := PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2
        (Bool.eq_false_iff.mpr hn)
      linarith
    have hcommon : ∀ᵐ z ∂μ, z ∈ I → G p.1 z = true ∧ G p.2 z = true := by
      filter_upwards [hx hout.1, hy hout.2] with z hx hy hi
      exact ⟨hx hi, hy hi⟩
    have he := IndependentAtomCopy.integrated_row_inventory G hG Y hY I hI
      3 (by norm_num) (PhysicalRepresentative.charge_bound W m)
      (PhysicalRepresentative.charge_zero_of_nonedge W m) m p.1 p.2 hcommon
    have hc := hp hg hypos.le
    rw [hfx, hfy] at he
    have h₁ := IndependentAtomCopy.missing_integral_le_private_body_composed G hG Y hY
      I P U hI hP hIP (PhysicalRepresentative.charge_bound W m) hY1
      (PhysicalRepresentative.charge_symm W m) β p.1 p.2 hout.1 hout.2
      (hx hout.1) (hmx hout.1) hcy
    have h₂ := IndependentAtomCopy.missing_integral_le_private_body_composed G hG Y hY
      I P U hI hP hIP (PhysicalRepresentative.charge_bound W m) hY1
      (PhysicalRepresentative.charge_symm W m) β p.2 p.1 hout.2 hout.1
      (hy hout.2) (hmy hout.2) hcx
    have hmass : 0 ≤ μ.real (IndependentAtomCopy.missingSection G p.1 ∩
        IndependentAtomCopy.missingSection G p.2) := measureReal_nonneg
    have hbound : μ.real I * K p.1 p.2 + (2 * (c - m * d) + m) ≤
        KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
          KernelOperator.composedKernel (μ := μ) J K p.2 p.1 + μ.real P *
            (U.indicator (fun _ => (1 : ℝ)) p.1 * β p.2 +
              β p.1 * U.indicator (fun _ => (1 : ℝ)) p.2) := by
      rw [hKeq]
      dsimp only [J, K] at *
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hm.le hmass]
    have h := mul_le_mul_of_nonneg_right hbound hpos.le
    nlinarith
  · have hzero : K p.1 p.2 = 0 := le_antisymm (le_of_not_gt hpos)
      (IndependentAtomCopy.positiveBody_mem Y E hY1 p.1 p.2).1
    rw [hzero]
    simp

/-- The retained private charge is absorbed only after its actual bounded
row and zero neighborhood section have been derived from the old model. -/
theorem private_positive_body_trace (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1)
    (hb : μ.real {x | S.ρ x = u.val} ≤ 2 * (c - m * d) + m)
    (hpositive : 0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val}) p.1 p.2) ^ 2 ∂μ.prod μ) :
    (μ.real {x | S.ρ x = r.val} + (2 * (c - m * d) + m) -
      μ.real {x | S.ρ x = u.val}) ^ 2 ≤
        2 * (∫ p : Ω × Ω,
          (IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
            ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val}) p.1 p.2) ^ 2 ∂μ.prod μ) := by
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = u.val}
  let E := I ∪ P
  let U := Eᶜ \ S.rootNeighborhood u
  let β := S.rootChargeRow u
  let K := IndependentAtomCopy.positiveBody Y E
  let J := IndependentAtomCopy.missingBody G E
  have hE : MeasurableSet E :=
    (S.hfibers r.val r.property).1.union (S.hfibers u.val u.property).1
  have hY1 : ∀ x y, Y x y ≤ 1 := fun x y =>
    (PhysicalRepresentative.charge_mem_Icc W m x y).2
  have hbonus : ∀ᵐ p ∂μ.prod μ,
      U.indicator (fun _ => (1 : ℝ)) p.1 * β p.2 +
        β p.1 * U.indicator (fun _ => (1 : ℝ)) p.2 ≤ 1 := by
    have hz := S.rootChargeRow_zero_off_neighborhood u hW hd hgap
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hz,
      Measure.quasiMeasurePreserving_snd.ae hz] with p hx hy
    by_cases hxu : p.1 ∈ U <;> by_cases hyu : p.2 ∈ U
    · simp [hxu, hyu, show β p.1 = 0 from hx hxu.2, show β p.2 = 0 from hy hyu.2]
    · simpa [hxu, hyu] using (S.rootChargeRow_mem_Icc u p.2).2
    · simpa [hxu, hyu] using (S.rootChargeRow_mem_Icc u p.1).2
    · simp [hxu, hyu]
  have hrow : ∀ᵐ p ∂μ.prod μ,
      μ.real I * (K p.1 p.2) ^ 2 +
        ((2 * (c - m * d) + m) - μ.real P) * K p.1 p.2 ≤
      K p.1 p.2 * (KernelOperator.composedKernel (μ := μ) J K p.1 p.2 +
        KernelOperator.composedKernel (μ := μ) J K p.2 p.1) := by
    filter_upwards [S.ae_private_positive_body_row r u hru hW hd hgap hprivate, hbonus]
      with p hp hb
    have hK0 := (IndependentAtomCopy.positiveBody_mem Y E hY1 p.1 p.2).1
    have hmul := mul_le_mul_of_nonneg_left hb (measureReal_nonneg (μ := μ) (s := P))
    have hmulK := mul_le_mul_of_nonneg_left hmul hK0
    dsimp only [I, P, E, U, β, K, J, Y, G] at *
    nlinarith
  have horth : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0 := by
    calc
      _ = ∫ _p : Ω × Ω, (0 : ℝ) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => IndependentAtomCopy.missingBody_positiveBody_mul
          G Y E (PhysicalRepresentative.charge_zero_of_nonedge W m) p.1 p.2)
      _ = 0 := integral_zero _ _
  have htrace := KernelOperator.copy_row_trace_bound K J
    (IndependentAtomCopy.measurable_positiveBody Y (PhysicalRepresentative.measurable_charge W m)
      E hE)
    (IndependentAtomCopy.measurable_missingBody G (PhysicalRepresentative.measurable_adjacency W m)
      E hE)
    (IndependentAtomCopy.positiveBody_mem Y E hY1)
    (fun x y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (IndependentAtomCopy.missingBody_mem G E x y).1]
      exact (IndependentAtomCopy.missingBody_mem G E x y).2)
    (IndependentAtomCopy.positiveBody_symm Y E (PhysicalRepresentative.charge_symm W m))
    (μ.real I) ((2 * (c - m * d) + m) - μ.real P) (sub_nonneg.mpr hb)
    (add_nonneg measureReal_nonneg (sub_nonneg.mpr hb)) hpositive horth hrow
  convert htrace using 1
  ring

/-- The original private inventory makes the positive-body trace strict.
Positive body energy remains explicit; zero body is a separate argument. -/
theorem private_positive_body_strict_trace (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1)
    (hb : μ.real {x | S.ρ x = u.val} ≤ 2 * (c - m * d) + m)
    (hgamma : 2 * (c - m * d) + m < μ.real {x | S.ρ x = r.val})
    (hpositive : 0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val}) p.1 p.2) ^ 2 ∂μ.prod μ) :
    3 * (μ.real {x | S.ρ x = r.val}) ^ 2 +
      2 * μ.real {x | S.ρ x = r.val} * (2 * (c - m * d) + m) +
      (2 * (c - m * d) + m) ^ 2 < 2 * (1 - 2 * d) := by
  have htrace := S.private_positive_body_trace r u hru hW hd hgap hprivate hb hpositive
  have hinventory := S.private_body_missing_inventory r u hru hW hd hgap hprivate
  have hbpos : 0 < μ.real {x | S.ρ x = u.val} :=
    ENNReal.toReal_pos (S.hfibers u.val u.property).2.1.ne' (measure_ne_top μ _)
  have hpos := mul_pos hbpos (sub_pos.mpr hgamma)
  have hτ : 0 ≤ μ.real {x | S.ρ x = u.val} *
      μ.real (({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val})ᶜ \ S.rootNeighborhood u) :=
    mul_nonneg hbpos.le measureReal_nonneg
  nlinarith [sq_nonneg (μ.real {x | S.ρ x = u.val})]

end Erdos1017.CappedModel.SelectedHighLowStructure
