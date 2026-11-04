module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2PrivateExposure

/-!
# Positive private stars in the large sector

In the large private sector `3A + b > 1`, the private physical primal and its
exact root incidence force positive first-root charge on the exterior
(`ae_positive_private_stars_sector`), and the private hole has more shifted-row
exposure than its mass, `E_M > k` (`private_hole_exposure_gt_mass_sector`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  {i p : S.I} {c d : ℝ}

private theorem PrivatePhysicalPrimal.ae_triangle_exposure_sector
    (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hsector : 1 < 3 * μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = i.val} <
      3 * (2 * (c - m * d) + m))
    (hNNmargin : (1 + m) * (1 - μ.real {x | S.ρ x = i.val}) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ v ∂P.laws 3, ∀ e : Equiv.Perm (Fin 3), S.ρ (v (e 0)) = i.val →
      0 < S.rootChargeRow i (v (e 1)) ∧
      (v (e 1) ∈ (({x | S.ρ x = i.val} ∪
        {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) →
        1 + m < S.rootChargeRow i (v (e 1))) := by
  have : IsFiniteMeasure (P.laws 3) := P.finite 3
  have hdemand : PhysicalPrimal.graphDemand μ
      {q | PhysicalRepresentative.adjacency W m q.1 q.2 = true} ≪ μ.prod μ :=
    Measure.absolutelyContinuous_restrict
  have hpairs : ∀ a b : Fin 3, a ≠ b →
      (P.laws 3).map (fun v => (v a, v b)) ≪ μ.prod μ := by
    intro a b hab
    exact (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
      P.feasible.2.2.2 3 ⟨(a, b), hab⟩).trans hdemand
  exact S.ae_permuted_private_triangle_exposure_sector i p P.distinct_roots hW hd hgap
    hpeak hhigh hprivate hsector hell hmargin hNNmargin (P.laws 3) hpairs
    (P.feasible.2.2.1 3) (P.tight_physical 3)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem orderRootLeaves_three_eq_zero_of_private_exposure
    (P : S.PrivatePhysicalPrimal i p c) (B : Set Ω) (hB : MeasurableSet B)
    (hbad : ∀ x ∈ B, S.rootChargeRow i x ≤ 0 ∨
      (x ∈ (({x | S.ρ x = i.val} ∪
        {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) ∧
        S.rootChargeRow i x ≤ 1 + m))
    (htriangle : ∀ᵐ v ∂P.laws 3, ∀ e : Equiv.Perm (Fin 3),
      S.ρ (v (e 0)) = i.val →
      0 < S.rootChargeRow i (v (e 1)) ∧
      (v (e 1) ∈ (({x | S.ρ x = i.val} ∪
        {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) →
        1 + m < S.rootChargeRow i (v (e 1)))) :
    PhysicalPrimal.orderRootLeaves 3 (P.laws 3)
      {x | S.ρ x = i.val} B = 0 := by
  rw [PhysicalPrimal.orderRootLeaves, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro ab _
  rw [Measure.map_apply (measurable_pi_apply _) hB,
    Measure.restrict_apply (hB.preimage (measurable_pi_apply _))]
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hperm : ∀ a b : Fin 3, a ≠ b →
      ∃ e : Equiv.Perm (Fin 3), e 0 = a ∧ e 1 = b := by decide
  filter_upwards [htriangle] with v hv hab
  obtain ⟨e, he0, he1⟩ := hperm ab.val.1 ab.val.2 ab.property
  have hs := hv e (by simpa only [he0, Set.mem_ofPred_eq] using hab.2)
  simp only [he1] at hs
  rcases hbad (v ab.val.2) hab.1 with hb | ⟨hk, hb⟩
  · exact (not_lt_of_ge hb) hs.1
  · exact (not_lt_of_ge hb) (hs.2 hk)

/-- In the large private sector `3A + b > 1`, the original private physical
primal and its exact root incidence force positive first-root charge on the
exterior, with the stronger bound in the second root's exterior hole. -/
theorem PrivatePhysicalPrimal.ae_positive_private_stars_sector
    (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hsector : 1 < 3 * μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = i.val} <
      3 * (2 * (c - m * d) + m))
    (hNNmargin : (1 + m) * (1 - μ.real {x | S.ρ x = i.val}) <
      3 * (2 * (c - m * d) + m)) :
    (∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ),
      0 < S.rootChargeRow i x) ∧
    (∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪
      {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p),
      1 + m < S.rootChargeRow i x) := by
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  let V := (I ∪ Pset)ᶜ
  let K := V \ S.rootNeighborhood p
  let B := V ∩ {x | S.rootChargeRow i x ≤ 0}
  let C := K ∩ {x | S.rootChargeRow i x ≤ 1 + m}
  have hV : MeasurableSet V :=
    ((S.hfibers i.val i.property).1.union (S.hfibers p.val p.property).1).compl
  have hK : MeasurableSet K := hV.diff (S.measurableSet_rootNeighborhood p)
  have hB : MeasurableSet B := hV.inter
    (measurableSet_le (S.measurable_rootChargeRow i) measurable_const)
  have hC : MeasurableSet C := hK.inter
    (measurableSet_le (S.measurable_rootChargeRow i) measurable_const)
  have htriangle := P.ae_triangle_exposure_sector hW hd hgap hpeak hhigh hprivate
    hsector hell hmargin hNNmargin
  have hcoef : 0 < 3 * μ.real I + μ.real Pset - 1 := by
    linarith only [hsector]
  have hnull (E : Set Ω) (hE : MeasurableSet E) (hEV : E ⊆ V)
      (hbad : ∀ x ∈ E, S.rootChargeRow i x ≤ 0 ∨
        (x ∈ K ∧ S.rootChargeRow i x ≤ 1 + m)) : μ E = 0 := by
    have hroot : PhysicalPrimal.orderRootLeaves 3 (P.laws 3) I E = 0 :=
      orderRootLeaves_three_eq_zero_of_private_exposure P E hE hbad htriangle
    have hinc := P.private_root_incidence_bound hW hd hgap hell.2 hhigh E hE hEV
    have hroot' : PhysicalPrimal.orderRootLeaves 3 (P.laws 3)
        {x | S.ρ x = i.val} E = 0 := by simpa only [I] using hroot
    have hrootReal : (PhysicalPrimal.orderRootLeaves 3 (P.laws 3)
        {x | S.ρ x = i.val}).real E = 0 := by
      simp only [Measure.real_def, hroot', ENNReal.toReal_zero]
    rw [hrootReal] at hinc
    have hnonneg : 0 ≤ μ.real E := measureReal_nonneg
    have hzero : μ.real E = 0 := by
      have hle : μ.real E ≤ 0 := by nlinarith only [hinc, hcoef, hnonneg]
      exact le_antisymm hle hnonneg
    exact (measureReal_eq_zero_iff (measure_ne_top μ E)).mp hzero
  have hBzero : μ B = 0 := hnull B hB inter_subset_left (by
    intro x hx
    exact Or.inl hx.2)
  have hCzero : μ C = 0 := hnull C hC (Set.Subset.trans inter_subset_left sdiff_subset) (by
    intro x hx
    exact Or.inr ⟨hx.1, hx.2⟩)
  constructor
  · apply (ae_restrict_iff' hV).mpr
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBzero] with x hx hVx
    exact lt_of_not_ge (fun h => hx ⟨hVx, h⟩)
  · apply (ae_restrict_iff' hK).mpr
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hCzero] with x hx hKx
    exact lt_of_not_ge (fun h => hx ⟨hKx, h⟩)

private theorem ae_rootChargeRow_eq_shifted_row_plus
    (S : SelectedHighLowStructure W m) (r : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ, S.rootChargeRow r y =
      r.val y + m * (if 0 < r.val y then 1 else 0) := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hrows : ∀ᵐ x ∂μ.restrict Ir,
      chargeKernel W x =ᵐ[μ]
        fun y => r.val y + m * (if 0 < r.val y then 1 else 0) :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hs := hW.strict_gap_structure hd hgap
  have hpair : ∀ᵐ q ∂μ.prod μ, q.1 ∈ Ir →
      PhysicalRepresentative.charge W m q.1 q.2 = S.rootChargeRow r q.2 ∧
      PhysicalRepresentative.charge W m q.1 q.2 = chargeKernel W q.1 q.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with q hroot hp hIr
    exact ⟨hroot hIr, hp⟩
  have hsections := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨x, hxIr, hxrows, hxsection⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIrpos.ne'
      (hrows.and (ae_restrict_of_ae hsections))
  filter_upwards [hxrows, hxsection] with y hy hp
  exact (hp hxIr).1.symm.trans ((hp hxIr).2.trans hy)

/-- In the large private sector the private hole has strictly more original
shifted-row exposure than its own mass, `E_M > k`. The positive stars come
from the same original physical primal. -/
theorem PrivatePhysicalPrimal.private_hole_exposure_gt_mass_sector
    (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hsector : 1 < 3 * μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = i.val} <
      3 * (2 * (c - m * d) + m))
    (hNNmargin : (1 + m) * (1 - μ.real {x | S.ρ x = i.val}) <
      3 * (2 * (c - m * d) + m)) :
    μ.real (({x | S.ρ x = i.val} ∪
      {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) <
      ∫ x in (({x | S.ρ x = i.val} ∪
        {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p),
          (i.val : Ω → ℝ) x ∂μ := by
  let I := {x | S.ρ x = i.val}
  let Pset := {x | S.ρ x = p.val}
  let V := (I ∪ Pset)ᶜ
  let K := V \ S.rootNeighborhood p
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union
      (S.hfibers p.val p.property).1).compl.diff
        (S.measurableSet_rootNeighborhood p)
  have hKpos : 0 < μ K := S.private_hole_measure_pos i p P.distinct_roots
    hW hd hgap hprivate
  have hstars := P.ae_positive_private_stars_sector hW hd hgap hpeak hhigh
    hprivate hsector hell hmargin hNNmargin
  have hV : ∀ᵐ x ∂μ, x ∈ V ↔ x ∈ S.rootNeighborhood i := by
    filter_upwards [S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate]
      with x hx
    simpa only [V, I, Pset, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq,
      not_or] using hx.symm
  have hrow : ∀ᵐ x ∂μ.restrict K,
      S.rootChargeRow i x = i.val x + m := by
    filter_upwards [ae_restrict_of_ae (ae_rootChargeRow_eq_shifted_row_plus S i hW hd hgap),
      ae_restrict_of_ae hV,
      ae_restrict_of_ae (S.ae_rootNeighborhood_iff i), ae_restrict_mem hK]
      with x hr hVx hN hx
    have hpos : 0 < i.val x := hN.mp (hVx.mp hx.1)
    simpa only [ite_eq_left hpos, mul_one] using hr
  have hgt : ∀ᵐ x ∂μ.restrict K, 1 < i.val x := by
    filter_upwards [hstars.2, hrow] with x hs hr
    linarith only [hs, hr]
  have hmem : Integrable (fun x => i.val x - 1) (μ.restrict K) := by
    exact ((Lp.memLp i.val).integrable (by norm_num)).restrict.sub (integrable_const _)
  have hpos : 0 < ∫ x in K, (i.val x - 1) ∂μ := by
    have hnonneg : ∀ᵐ x ∂μ.restrict K, 0 ≤ i.val x - 1 :=
      hgt.mono (fun _ hx => le_of_lt (by linarith only [hx]))
    rw [integral_pos_iff_support_of_nonneg_ae hnonneg hmem]
    have hsupport : Function.support (fun x => i.val x - 1) =ᵐ[μ.restrict K] Set.univ :=
      hgt.mono (fun x hx => by
        change (i.val x - 1 ≠ 0) = True
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          linarith only [hx])
    rw [measure_congr hsupport]
    simpa [Measure.restrict_apply hK] using hKpos
  have hfi : Integrable (fun x => i.val x) (μ.restrict K) :=
    ((Lp.memLp i.val).integrable (by norm_num)).restrict
  rw [integral_sub hfi (integrable_const _), setIntegral_const, smul_eq_mul,
    mul_one] at hpos
  simpa only [sub_pos, K, V, I, Pset] using hpos

end Erdos1017.CappedModel.SelectedHighLowStructure
