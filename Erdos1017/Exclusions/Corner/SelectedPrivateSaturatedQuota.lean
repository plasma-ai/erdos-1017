module

public import Erdos1017.Exclusions.Common.Private.SelectedPrivateRootless
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairCapacity
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateSaturatedBill
public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedAtomDegree

/-!
# Saturated quota of the private primal

The private primal's two root quotas and its unique saturated stock pay its
complete cost, accounting for rootless parents, the order-two reserve and the
saturated partner's mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical ENNReal

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem twice_cost_le_rootLeaves_add_two
    (η : PhysicalPrimal.Laws Ω) [∀ n, IsFiniteMeasure (η n)]
    (I : Set Ω) (hI : MeasurableSet I) [IsFiniteMeasure (PhysicalPrimal.rootLeaves η I)]
    (hsmall : ∀ n, n < 2 → η n = 0)
    (hroot : ∀ n, ∀ᵐ v ∂η n, ∃ i : Fin n, v i ∈ I) :
    2 * PhysicalPrimal.cost η ≤
      (PhysicalPrimal.rootLeaves η I).real univ + (η 2).real univ := by
  have hord (n : ℕ) : 2 * η n univ ≤
      PhysicalPrimal.orderRootLeaves n (η n) I univ + if n = 2 then η 2 univ else 0 := by
    by_cases hn : 3 ≤ n
    · exact (PhysicalPrimal.twice_mass_le_orderRootLeaves n hn (η n) I hI
        (hroot n)).trans (le_add_right le_rfl)
    · have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hn' with rfl | rfl | rfl
      · simp [hsmall 0 (by omega)]
      · simp [hsmall 1 (by omega)]
      · have h := add_le_add_right
          (PhysicalPrimal.mass_le_orderFirstOccupation_of_has_root 2 (η 2) I hI
            (hroot 2)) (η 2 univ)
        simpa [PhysicalPrimal.orderRootLeaves_mass 2 (η 2) I hI, two_mul] using h
  have htotal : 2 * (∑' n, η n univ) ≤
      PhysicalPrimal.rootLeaves η I univ + η 2 univ := by
    calc
      2 * (∑' n, η n univ) = ∑' n, 2 * η n univ := (ENNReal.tsum_mul_left).symm
      _ ≤ ∑' n, (PhysicalPrimal.orderRootLeaves n (η n) I univ +
          if n = 2 then η 2 univ else 0) := ENNReal.tsum_le_tsum hord
      _ = PhysicalPrimal.rootLeaves η I univ + η 2 univ := by
        rw [ENNReal.tsum_add]
        simp [PhysicalPrimal.rootLeaves]
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) htotal
  have hcost : (∑' n, η n univ).toReal = PhysicalPrimal.cost η := by
    simpa only [PhysicalPrimal.cost, measureReal_def] using
      ENNReal.tsum_toReal_eq (fun n => measure_ne_top (η n) univ)
  rw [ENNReal.toReal_mul, hcost, ENNReal.toReal_add
    (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
  simpa only [ENNReal.toReal_ofNat, measureReal_def] using hreal

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  {i p q : S.I} {c : ℝ}

namespace PrivatePhysicalPrimal

private theorem two_mass_le_saturated_stock (P : S.PrivatePhysicalPrimal i p c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hsat : S.IsSaturatedAtomPair p q) :
    (P.laws 2).real univ ≤
      μ.real {x | S.ρ x = p.val} * μ.real {x | S.ρ x = q.val} := by
  have : IsFiniteMeasure (P.laws 2) := P.finite 2
  let Y : Ω × Ω → ℝ := W.moment CappedColor.charge
  let T : Set (Ω × Ω) := {z | Y z = 1}
  let ρ := PhysicalPrimal.orderOccupation 2 (P.laws 2)
  have hρdom : ρ ≤ μ.prod μ := by
    calc
      ρ ≤ PhysicalPrimal.occupation P.laws :=
        Measure.le_sum (fun n => PhysicalPrimal.orderOccupation n (P.laws n)) 2
      _ = PhysicalPrimal.graphDemand μ
          {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true} := P.feasible.2.2.2
      _ ≤ μ.prod μ := Measure.restrict_le_self
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le (μ.prod μ) hρdom
  have hρmass : ρ.real univ = 2 * (P.laws 2).real univ := by
    rw [show ρ = PhysicalPrimal.orderOccupation 2 (P.laws 2) from rfl,
      PhysicalPrimal.orderOccupation_mass]
    norm_num [show Fintype.card (PhysicalPrimal.PairIndex 2) = 2 by decide]
  have hYi : Integrable Y (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable W) 3 (chargeKernel_bound W)
  have hYρ : Integrable Y ρ := hYi.mono_measure hρdom
  have hcharge := (PhysicalPrimal.integral_charge 2 (P.laws 2) Y hYρ).2
  have ht : (∫ v, PhysicalPrimal.charge Y v ∂P.laws 2) = (P.laws 2).real univ := by
    have hYeq : Function.uncurry (chargeKernel W) = Y := rfl
    have htight : ∀ᵐ v ∂P.laws 2, PhysicalPrimal.charge Y v = 1 := by
      simpa only [hYeq] using P.tight_original 2
    rw [integral_congr_ae htight]
    simp only [integral_const, smul_eq_mul, mul_one]
  have hslack : (∫ z, 1 - Y z ∂ρ) = 0 := by
    rw [integral_sub (integrable_const 1) hYρ, integral_const, smul_eq_mul, mul_one,
      hρmass]
    change (∫ v, PhysicalPrimal.charge Y v ∂P.laws 2) = (∫ z, Y z ∂ρ) / 2 at hcharge
    linarith
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun z => sub_nonneg.mpr
      ((charge_moment_le_adjacency W z).trans (adjacency_moment_mem W z).2)))
    ((integrable_const 1).sub hYρ)).mp hslack
  have hconull : T =ᵐ[ρ] univ := by
    filter_upwards [hzero] with z hz
    change 1 - Y z = 0 at hz
    exact propext ⟨fun _ => mem_univ z, fun _ => by change Y z = 1; linarith⟩
  have hρsat : ρ.real univ ≤ (μ.prod μ).real T := by
    rw [measureReal_def, ← measure_congr hconull, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (hρdom T)
  have hsatmass := hsat.saturated_mass_eq hW hd hgap hell
  change (μ.prod μ).real T =
    2 * μ.real {x | S.ρ x = p.val} * μ.real {x | S.ρ x = q.val} at hsatmass
  rw [hρmass, hsatmass] at hρsat
  linarith

/-- The same private primal's two original root quotas and unique saturated-pair
stock pay its complete cost. Rootless parents, the order-two reserve and
the saturated partner's mass bound are derived internally. -/
theorem saturated_objective_le_private_quota (P : S.PrivatePhysicalPrimal i p c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = i.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = i.val} <
      3 * (2 * (c - m * d) + m)) (hsat : S.IsSaturatedAtomPair p q) :
    let A := μ.real {x | S.ρ x = i.val}
    let b := μ.real {x | S.ρ x = p.val}
    let k := μ.real (({x | S.ρ x = i.val} ∪
      {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p)
    2 * c ≤ A - A ^ 2 + 2 * b - 4 * A * b - 2 * b ^ 2 - b * k := by
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  let Q := {x | S.ρ x = q.val}
  let E := I ∪ Pset
  let K := Eᶜ \ S.rootNeighborhood p
  let A := μ.real I
  let b := μ.real Pset
  let k := μ.real K
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet Pset := (S.hfibers p.val p.property).1
  have hE : MeasurableSet E := hI.union hP
  have hdis : Disjoint I Pset := Set.disjoint_left.mpr (by
    intro x hx hy
    exact P.distinct_roots (Subtype.ext (hx.symm.trans hy)))
  have hleaves : PhysicalPrimal.rootLeaves P.laws E =
      PhysicalPrimal.rootLeaves P.laws I + PhysicalPrimal.rootLeaves P.laws Pset := by
    unfold PhysicalPrimal.rootLeaves
    calc
      Measure.sum (fun n => PhysicalPrimal.orderRootLeaves n (P.laws n) E) =
          Measure.sum (fun n => PhysicalPrimal.orderRootLeaves n (P.laws n) I +
            PhysicalPrimal.orderRootLeaves n (P.laws n) Pset) := by
              congr 1
              funext n
              exact PhysicalPrimal.orderRootLeaves_union n (P.laws n) I Pset hP hdis
      _ = _ := (Measure.sum_add_sum _ _).symm
  have hquota : PhysicalPrimal.rootLeaves P.laws E =
      μ I • μ.restrict Eᶜ + μ Pset • μ.restrict (S.rootNeighborhood p) := by
    rw [hleaves, P.leaves_first, P.leaves_second]
  have : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  have hfirstfinite : IsFiniteMeasure (μ I • μ.restrict Eᶜ) := by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top (measure_ne_top μ I) (measure_ne_top μ Eᶜ))
  have hsecondfinite : IsFiniteMeasure
      (μ Pset • μ.restrict (S.rootNeighborhood p)) := by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
      (measure_ne_top μ Pset) (measure_ne_top μ (S.rootNeighborhood p)))
  have : IsFiniteMeasure (PhysicalPrimal.rootLeaves P.laws E) := by
    constructor
    rw [hquota, Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hfirstfinite.1, hsecondfinite.1⟩
  have hsmall : ∀ n, n < 2 → P.laws n = 0 := by
    intro n hn
    interval_cases n
    · exact P.feasible.1
    · exact P.feasible.2.1
  have hroot (n : ℕ) : ∀ᵐ v ∂P.laws n, ∃ j : Fin n, v j ∈ E := by
    simpa only [E, I, Pset, Set.mem_union, Set.mem_ofPred_eq] using
      P.ae_has_combined_root hW hd hgap hpeak hhigh hprivate hA hell hmargin n
  have hcost := twice_cost_le_rootLeaves_add_two P.laws E hE hsmall hroot
  rw [P.cost] at hcost
  have hstock := P.two_mass_le_saturated_stock hW hd hgap hell.2 hsat
  have hquotaReal : (PhysicalPrimal.rootLeaves P.laws E).real univ =
      A * μ.real Eᶜ + b * μ.real (S.rootNeighborhood p) := by
    rw [hquota, measureReal_add_apply hfirstfinite.1.ne hsecondfinite.1.ne]
    simp only [measureReal_def, Measure.smul_apply, Measure.restrict_apply_univ,
      smul_eq_mul, ENNReal.toReal_mul, A, b]
  have hEreal : μ.real Eᶜ = 1 - A - b := by
    rw [measureReal_compl hE, probReal_univ, measureReal_union hdis hP]
    dsimp only [A, b]
    ring
  obtain ⟨_, _, _, hhinge, hdegree, _⟩ :=
    S.private_saturated_bill_geometry i p q P.distinct_roots hW hd hgap hell.2
      hsat hhigh hprivate
  have hN : μ.real (S.rootNeighborhood p) = 1 - A - b - k := by
    rw [← S.wholeRowDegree_eq_neighborhood_mass p]
    exact hdegree
  have hQsub : Q ⊆ (S.rootNeighborhood q)ᶜ := by
    intro x hx
    exact Set.disjoint_left.mp (S.rootNeighborhood_disjoint q) hx
  have hQmass : μ.real Q ≤ 1 - wholeRowDegree q.val := by
    rw [S.wholeRowDegree_eq_neighborhood_mass q]
    have h := measureReal_mono (μ := μ) hQsub
    rwa [measureReal_compl (S.measurableSet_rootNeighborhood q), probReal_univ] at h
  have hRN : μ.real Q ≤ 1 - 2 * A - b := by linarith only [hQmass, hhinge]
  have hbound := mul_le_mul_of_nonneg_left hRN (show 0 ≤ b from measureReal_nonneg)
  rw [hquotaReal, hEreal, hN] at hcost
  change (P.laws 2).real univ ≤ b * μ.real Q at hstock
  change 2 * c ≤ A - A ^ 2 + 2 * b - 4 * A * b - 2 * b ^ 2 - b * k
  nlinarith only [hcost, hstock, hbound]

end PrivatePhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure
