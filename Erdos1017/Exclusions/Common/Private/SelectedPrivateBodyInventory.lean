module

public import Erdos1017.Exclusions.Common.SelectedRootRows
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyBody

/-!
# Missing-density inventory of a private body

The averaged root charge row vanishes off its neighborhood, and a whole atom
with exactly one outside missing whole atom has an exact missing-density
inventory whose remaining energy is the squared missing-body kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

attribute [local instance] Classical.propDecidable

/-- The actual averaged charge row vanishes off its original neighborhood.
The common good section is selected from the positive whole fiber. -/
theorem rootChargeRow_zero_off_neighborhood (S : SelectedHighLowStructure W m) (u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ z ∂μ, z ∉ S.rootNeighborhood u → S.rootChargeRow u z = 0 := by
  have hcharge := Measure.ae_ae_of_ae_prod (S.ae_root_charge u hW hd hgap)
  have hadj := Measure.ae_ae_of_ae_prod (S.ae_root_adjacency u hW hd hgap)
  obtain ⟨x, hx, hc, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne'
    ((ae_restrict_of_ae hcharge).and (ae_restrict_of_ae hadj))
  filter_upwards [hc, ha] with z hc ha hz
  have hfalse : PhysicalRepresentative.adjacency W m x z = false :=
    Bool.eq_false_iff.mpr (fun h => hz ((ha hx).mp h))
  exact (hc hx).symm.trans (PhysicalRepresentative.charge_zero_of_nonedge W m x z hfalse)

/-- A whole atom with exactly one outside missing whole atom has this
exact original missing-density inventory. The remaining energy is the
squared physical missing-body kernel on the original product law. -/
theorem private_body_missing_inventory (S : SelectedHighLowStructure W m)
    (r u : S.I) (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) :
    let E := {x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val}
    let U := Eᶜ \ S.rootNeighborhood u
    let J := IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m) E
    1 - 2 * d =
      (μ.real {x | S.ρ x = r.val} + μ.real {x | S.ρ x = u.val}) ^ 2 +
        (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) +
        2 * μ.real {x | S.ρ x = u.val} * μ.real U := by
  classical
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = u.val}
  let E := I ∪ P
  let U := Eᶜ \ S.rootNeighborhood u
  let A := PhysicalRepresentative.adjacency W m
  let J := IndependentAtomCopy.missingBody A E
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers u.val u.property).1
  have hE : MeasurableSet E := hI.union hP
  have hU : MeasurableSet U := hE.compl.diff (S.measurableSet_rootNeighborhood u)
  have hdis : Disjoint I P := Set.disjoint_left.mpr (fun _ hx hy =>
    hru (Subtype.ext (hx.symm.trans hy)))
  have hrowI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → (A p.1 p.2 = true ↔ p.2 ∉ E) := by
    filter_upwards [hprivate, PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with p hp ha hx
    have he := ha.symm.trans (hp hx)
    change (if A p.1 p.2 = true then (1 : ℝ) else 0) =
      (if p.2 ∈ E then 0 else 1) at he
    by_cases hy : p.2 ∈ E <;> cases hA : A p.1 p.2 <;> simp_all
  have hrowP := S.ae_root_adjacency u hW hd hgap
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have he : ∀ᵐ p ∂μ.prod μ, (J p.1 p.2) ^ 2 =
      1 - (if A p.1 p.2 = true then (1 : ℝ) else 0) -
        E.indicator (fun _ => (1 : ℝ)) p.1 * E.indicator (fun _ => (1 : ℝ)) p.2 -
        P.indicator (fun _ => (1 : ℝ)) p.1 * U.indicator (fun _ => (1 : ℝ)) p.2 -
        U.indicator (fun _ => (1 : ℝ)) p.1 * P.indicator (fun _ => (1 : ℝ)) p.2 := by
    filter_upwards [hrowI, hswap.ae hrowI, hrowP, hswap.ae hrowP]
      with p hi hir hp hpr
    change (p.2 ∈ I → (A p.2 p.1 = true ↔ p.1 ∉ E)) at hir
    change (p.1 ∈ P → (A p.1 p.2 = true ↔ p.2 ∈ S.rootNeighborhood u)) at hp
    change (p.2 ∈ P → (A p.2 p.1 = true ↔ p.1 ∈ S.rootNeighborhood u)) at hpr
    have hsym : A p.2 p.1 = A p.1 p.2 :=
      PhysicalRepresentative.adjacency_symm W m p.2 p.1
    rw [hsym] at hir hpr
    have hPN (x : Ω) (hx : x ∈ P) : x ∉ S.rootNeighborhood u := fun hn => hn.1 hx
    by_cases hx : p.1 ∈ E <;> by_cases hy : p.2 ∈ E
    · have hxU : p.1 ∉ U := fun h => h.1 hx
      have hyU : p.2 ∉ U := fun h => h.1 hy
      have ha : A p.1 p.2 = false := by
        apply Bool.eq_false_iff.mpr
        intro ha
        rcases hx with hx | hx
        · exact ((hi hx).mp ha) hy
        · rcases hy with hy | hy
          · exact ((hir hy).mp ha) (Or.inr hx)
          · exact hPN p.2 hy ((hp hx).mp ha)
      simp [J, IndependentAtomCopy.missingBody, hx, hy, hxU, hyU, ha]
    · have hxU : p.1 ∉ U := fun h => h.1 hx
      have hyP : p.2 ∉ P := fun h => hy (Or.inr h)
      rcases hx with hxi | hxp
      · have hxP : p.1 ∉ P := fun h => Set.disjoint_left.mp hdis hxi h
        have hx : p.1 ∈ E := Or.inl hxi
        have ha := (hi hxi).mpr hy
        simp [J, IndependentAtomCopy.missingBody, hx, hy, hxP, hyP, hxU, ha]
      · have hx : p.1 ∈ E := Or.inr hxp
        by_cases hyn : p.2 ∈ S.rootNeighborhood u
        · have ha := (hp hxp).mpr hyn
          have hyU : p.2 ∉ U := fun h => h.2 hyn
          simp [J, IndependentAtomCopy.missingBody, hx, hy, hxp, hyP, hxU, hyU, ha]
        · have ha : A p.1 p.2 = false :=
            Bool.eq_false_iff.mpr (fun h => hyn ((hp hxp).mp h))
          have hyU : p.2 ∈ U := ⟨hy, hyn⟩
          simp [J, IndependentAtomCopy.missingBody, hx, hy, hxp, hyP, hxU, hyU, ha]
    · have hyU : p.2 ∉ U := fun h => h.1 hy
      have hxP : p.1 ∉ P := fun h => hx (Or.inr h)
      rcases hy with hyi | hyp
      · have hyP : p.2 ∉ P := fun h => Set.disjoint_left.mp hdis hyi h
        have hy : p.2 ∈ E := Or.inl hyi
        have ha := (hir hyi).mpr hx
        simp [J, IndependentAtomCopy.missingBody, hx, hy, hxP, hyP, hyU, ha]
      · have hy : p.2 ∈ E := Or.inr hyp
        by_cases hxn : p.1 ∈ S.rootNeighborhood u
        · have ha := (hpr hyp).mpr hxn
          have hxU : p.1 ∉ U := fun h => h.2 hxn
          simp [J, IndependentAtomCopy.missingBody, hx, hy, hxP, hyp, hxU, hyU, ha]
        · have ha : A p.1 p.2 = false :=
            Bool.eq_false_iff.mpr (fun h => hxn ((hpr hyp).mp h))
          have hxU : p.1 ∈ U := ⟨hx, hxn⟩
          simp [J, IndependentAtomCopy.missingBody, hx, hy, hxP, hyp, hxU, hyU, ha]
    · have hxP : p.1 ∉ P := fun h => hx (Or.inr h)
      have hyP : p.2 ∉ P := fun h => hy (Or.inr h)
      cases ha : A p.1 p.2 <;>
        simp [J, IndependentAtomCopy.missingBody, hx, hy, hxP, hyP, ha]
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hiA : Integrable (fun p : Ω × Ω => if A p.1 p.2 = true then (1 : ℝ) else 0)
      (μ.prod μ) := Integrable.of_bound
    (Measurable.ite (hA (measurableSet_singleton true)) measurable_const
      measurable_const).aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by split_ifs <;> norm_num))
  have hiE : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hE
  have hiP : Integrable (P.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hP
  have hiU : Integrable (U.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hU
  have hi1 : Integrable (fun p : Ω × Ω => 1 -
      (if A p.1 p.2 = true then (1 : ℝ) else 0)) (μ.prod μ) :=
    (integrable_const 1).sub hiA
  have hiEE : Integrable (fun p : Ω × Ω => E.indicator (fun _ => (1 : ℝ)) p.1 *
      E.indicator (fun _ => (1 : ℝ)) p.2) (μ.prod μ) := hiE.mul_prod hiE
  have hiPU : Integrable (fun p : Ω × Ω => P.indicator (fun _ => (1 : ℝ)) p.1 *
      U.indicator (fun _ => (1 : ℝ)) p.2) (μ.prod μ) := hiP.mul_prod hiU
  have hiUP : Integrable (fun p : Ω × Ω => U.indicator (fun _ => (1 : ℝ)) p.1 *
      P.indicator (fun _ => (1 : ℝ)) p.2) (μ.prod μ) := hiU.mul_prod hiP
  have hi2 : Integrable (fun p : Ω × Ω =>
      1 - (if A p.1 p.2 = true then (1 : ℝ) else 0) -
        E.indicator (fun _ => (1 : ℝ)) p.1 * E.indicator (fun _ => (1 : ℝ)) p.2)
      (μ.prod μ) := hi1.sub hiEE
  have hi3 : Integrable (fun p : Ω × Ω =>
      1 - (if A p.1 p.2 = true then (1 : ℝ) else 0) -
        E.indicator (fun _ => (1 : ℝ)) p.1 * E.indicator (fun _ => (1 : ℝ)) p.2 -
        P.indicator (fun _ => (1 : ℝ)) p.1 * U.indicator (fun _ => (1 : ℝ)) p.2)
      (μ.prod μ) := hi2.sub hiPU
  have henergy : (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) =
      1 - (∫ p : Ω × Ω, (if A p.1 p.2 = true then (1 : ℝ) else 0) ∂μ.prod μ) -
        (μ.real E) ^ 2 - 2 * μ.real P * μ.real U := by
    rw [integral_congr_ae he, integral_sub hi3 hiUP,
      integral_sub hi2 hiPU, integral_sub hi1 hiEE, integral_sub (integrable_const 1) hiA,
      integral_const, probReal_univ, smul_eq_mul, mul_one, integral_prod_mul,
      integral_prod_mul, integral_prod_mul, integral_indicator hE,
      integral_indicator hP, integral_indicator hU, setIntegral_const,
      setIntegral_const, setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    ring
  have hdensity := (PhysicalRepresentative.density_eq W m
    (hW.strict_gap_structure hd hgap).strict_support).trans hW.density_eq
  change (∫ p : Ω × Ω, (if A p.1 p.2 = true then (1 : ℝ) else 0) ∂μ.prod μ) / 2 = d
    at hdensity
  have hmass : μ.real E = μ.real I + μ.real P := measureReal_union hdis hP
  change 1 - 2 * d = (μ.real I + μ.real P) ^ 2 +
    (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) + 2 * μ.real P * μ.real U
  rw [hmass] at henergy
  linarith only [henergy, hdensity]

end Erdos1017.CappedModel.SelectedHighLowStructure
