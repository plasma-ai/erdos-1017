module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPositiveStars

/-!
# Exclusion of rootless parents for an unsaturated universal root

An independent universal root augments every rootless tight parent by positive
charge, so every parent has a root, the two-point law vanishes, and with two
exterior leaves per parent the root quota pays twice the cost.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem measurableSet_no_root {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (I : Set Ω) (hI : MeasurableSet I) :
    MeasurableSet {v : Fin n → Ω | ∀ i, v i ∉ I} := by
  have h := MeasurableSet.iInter (fun i : Fin n => (hI.preimage (measurable_pi_apply i)).compl)
  convert h using 1
  ext v
  simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

namespace UniversalPhysicalPrimal

/-- A genuinely independent universal root augments every hypothetical
rootless tight parent by positive old charge. Original pair balance and
fresh-sample licenses justify this even for singular parent laws. -/
theorem noRootLaw_eq_zero (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m))
    (n : ℕ) : PhysicalRootReplacement.noRootLaw (P.laws n) {x | S.ρ x = r.val} = 0 := by
  classical
  by_cases hn : 2 ≤ n
  · have : IsFiniteMeasure (P.laws n) := P.finite n
    let I := {x | S.ρ x = r.val}
    have hI : MeasurableSet I := (S.hfibers r.val r.property).1
    let ρ := PhysicalRootReplacement.noRootLaw (P.laws n) I
    have : IsFiniteMeasure ρ := by dsimp [ρ]; infer_instance
    let ν : Measure Ω := PhysicalRootReplacement.rootLaw μ I (S.hfibers r.val r.property).2.1.ne'
    have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    have hν : ν ≪ μ := PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous μ I
    have hνI : ∀ᵐ z ∂ν, z ∈ I := by
      change ∀ᵐ z ∂(μ I)⁻¹ • μ.restrict I, z ∈ I
      exact Measure.ae_smul_measure (ae_restrict_mem hI) _
    have hρ : ρ ≪ P.laws n := Measure.absolutelyContinuous_restrict
    have hdemand : PhysicalPrimal.graphDemand μ
        {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true} ≪ μ.prod μ :=
      Measure.absolutelyContinuous_restrict
    have hpairs : ∀ i j : Fin n, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ := by
      intro i j hij
      exact (hρ.map ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).trans
        ((PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
          P.feasible.2.2.2 n ⟨(i, j), hij⟩).trans hdemand)
    let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
    let Y := Function.uncurry (PhysicalRepresentative.charge W m)
    have hs := hW.strict_gap_structure hd hgap
    have htest : ∀ k, 2 ≤ k → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
        PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
      intro k _
      filter_upwards [PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
        hW.deterministic k] with v hv hc
      change PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v ≤ 1
      rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
      exact hv hc
    have hfresh := PhysicalCliqueRepresentative.freshLaw_pairs_absolutelyContinuous μ hn
      ρ hpairs ν hν
    have hlicense := PhysicalCliqueRepresentative.ae_charge_le_of_pair_marginals μ
      (PhysicalRepresentative.measurable_adjacency W m) (PhysicalRepresentative.measurable_charge W m)
      3 (by norm_num) (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
      htest (PhysicalCliqueRepresentative.freshLaw ν ρ) hfresh
    have hlicenseProd := ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hlicense
    have hrow : ∀ᵐ p ∂μ.prod μ,
        (S.ρ p.1 = r.val → (G p = true ↔ S.ρ p.2 ≠ r.val)) ∧
        (S.ρ p.1 = r.val → Y p = S.rootChargeRow r p.2) :=
      (S.neutral_atom_physical_adjacency r hW hd hgap hN).and (S.ae_root_charge r hW hd hgap)
    have hfacts : ∀ᵐ w ∂PhysicalCliqueRepresentative.freshLaw ν ρ,
        ∀ i j : Fin (n + 1), i ≠ j →
          (S.ρ (w i) = r.val → (G (w i, w j) = true ↔ S.ρ (w j) ≠ r.val)) ∧
          (S.ρ (w i) = r.val → Y (w i, w j) = S.rootChargeRow r (w j)) := by
      simp only [ae_all_iff]
      intro i j hij
      exact ae_of_ae_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
        ((hfresh i j hij).ae_le hrow)
    have hfactsProd := ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hfacts
    have hnone : ∀ᵐ v ∂ρ, ∀ i, v i ∉ I :=
      ae_restrict_mem (measurableSet_no_root I hI)
    have hpositive := hρ.ae_le (P.ae_original_vertices _
      (P.ae_positive_exterior_rootChargeRow hW hd hgap hN hstar hA hell hmargin) n)
    have hfalse : ∀ᵐ p ∂ν.prod ρ, False := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hνI,
        Measure.quasiMeasurePreserving_snd.ae hnone,
        Measure.quasiMeasurePreserving_snd.ae hpositive,
        Measure.quasiMeasurePreserving_snd.ae (hρ.ae_le (P.feasible.2.2.1 n)),
        Measure.quasiMeasurePreserving_snd.ae (hρ.ae_le (P.tight_physical n)),
        hlicenseProd, hfactsProd] with p hp hnoro hpstar hc ht hlic hfact
      have hnew (i : Fin n) : G (p.1, p.2 i) = true := by
        have h := hfact 0 i.succ (Fin.succ_ne_zero i).symm
        change (S.ρ p.1 = r.val → (G (p.1, p.2 i) = true ↔ S.ρ (p.2 i) ≠ r.val)) ∧ _ at h
        exact (h.1 hp).mpr (hnoro i)
      have hnewstar (i : Fin n) : 0 < Y (p.1, p.2 i) := by
        have h := hfact 0 i.succ (Fin.succ_ne_zero i).symm
        change _ ∧ (S.ρ p.1 = r.val → Y (p.1, p.2 i) = S.rootChargeRow r (p.2 i)) at h
        rw [h.2 hp]
        exact hpstar i (hnoro i)
      have hcl : PhysicalCliqueRepresentative.Clique G (Fin.cons p.1 p.2) := by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => exact hnew j
        | succ i =>
          cases j using Fin.cases with
          | zero =>
            change PhysicalRepresentative.adjacency W m (p.2 i) p.1 = true
            rw [PhysicalRepresentative.adjacency_symm W m (p.2 i) p.1]
            exact hnew i
          | succ j => exact hc i j (fun h => hij (congrArg Fin.succ h))
      have hsum : 0 < ∑ i : Fin n, Y (p.1, p.2 i) := by
        let i : Fin n := ⟨0, by omega⟩
        exact (hnewstar i).trans_le (Finset.single_le_sum
          (fun j _ => (hnewstar j).le) (Finset.mem_univ i))
      have hcap := hlic hcl
      have he := PhysicalTriangleExposure.charge_cons Y
        (PhysicalRepresentative.charge_symm W m) p.2 p.1
      have hgt : 1 < PhysicalPrimal.charge Y (Fin.cons p.1 p.2) := by
        rw [he, ht]
        linarith
      exact (not_lt_of_ge hcap) hgt
    have hz : (ν.prod ρ) univ = 0 := by simpa only [ae_iff, not_false_eq_true, ofPred_true] using hfalse
    have hmass : (ν.prod ρ) univ = ρ univ := by
      rw [← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul]
    have hρzero : ρ = 0 := Measure.measure_univ_eq_zero.mp (hmass.symm.trans hz)
    exact hρzero
  · have hn' : n ≤ 1 := by omega
    interval_cases n <;> simp [P.feasible.1, P.feasible.2.1, PhysicalRootReplacement.noRootLaw]

/-- The derived zero rootless restrictions give actual root existence in
every original parent, including zero laws at orders zero and one. -/
theorem ae_has_root (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m))
    (n : ℕ) : ∀ᵐ v ∂P.laws n, ∃ i, S.ρ (v i) = r.val := by
  have hz := congrArg (fun ν : Measure (Fin n → Ω) => ν univ)
    (P.noRootLaw_eq_zero hW hd hgap hN hstar hA hell hmargin n)
  simp only [PhysicalRootReplacement.noRootLaw, Measure.restrict_apply_univ,
    Measure.coe_zero, Pi.zero_apply] at hz
  have hn := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hn] with v hv
  simpa only [mem_ofPred_eq, not_forall, not_not] using hv

/-- Actual root existence and unsaturation remove the entire original
two-point law, after rootless parents have been excluded. -/
theorem law_two_eq_zero (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m)) :
    P.laws 2 = 0 := by
  let I := {x | S.ρ x = r.val}
  have hle := PhysicalPrimal.mass_le_orderFirstOccupation_of_has_root 2 (P.laws 2) I
    (S.hfibers r.val r.property).1 (P.ae_has_root hW hd hgap hN hstar hA hell hmargin 2)
  have hz := P.orderRootLeaves_two_eq_zero hW hd hgap hstar univ MeasurableSet.univ
  rw [PhysicalPrimal.orderRootLeaves_mass 2 (P.laws 2) I (S.hfibers r.val r.property).1] at hz
  norm_num only [Nat.reduceSub, Nat.cast_one, one_mul] at hz
  rw [hz] at hle
  exact Measure.measure_univ_eq_zero.mp (le_antisymm hle zero_le)

/-- The same actual physical primal has at least two exterior leaves per
parent, so its exact original root quota pays twice its cost. -/
theorem objective_le_half_root_quota (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m)) :
    c ≤ μ.real {x | S.ρ x = r.val} * (1 - μ.real {x | S.ρ x = r.val}) / 2 := by
  have : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  have hsmall : ∀ n, n < 3 → P.laws n = 0 := by
    intro n hn
    interval_cases n
    · exact P.feasible.1
    · exact P.feasible.2.1
    · exact P.law_two_eq_zero hW hd hgap hN hstar hA hell hmargin
  have hE : MeasurableSet {p : Ω × Ω | PhysicalRepresentative.adjacency W m p.1 p.2 = true} :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have h := PhysicalPrimal.cost_le_universal_root_quota P.laws μ _ hE P.feasible.2.2.2
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
    (S.neutral_atom_physical_blocks r hW hd hgap hN).1 hsmall
    (P.ae_has_root hW hd hgap hN hstar hA hell hmargin)
  rwa [P.cost] at h

end UniversalPhysicalPrimal

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The original selected model derives its own primal, triangle and
exterior exposure, rootless-parent exclusion and physical count. Only the
stated original unsaturated-universal scalar gate is an input. -/
theorem unsaturated_universal_objective_le_half_root_quota
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m)) :
    c ≤ μ.real {x | S.ρ x = r.val} * (1 - μ.real {x | S.ρ x = r.val}) / 2 := by
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  exact P.objective_le_half_root_quota hW hd hgap hN hstar hA hell hmargin

end Erdos1017.CappedModel.SelectedHighLowStructure
