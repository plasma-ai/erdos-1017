module

public import Erdos1017.Exclusions.Common.E2.EmptySatE2Scalar
public import Erdos1017.Exclusions.Common.Physical.IndependentHeadSupport
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPrimal
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyInequality
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitMass
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalDeficitAtoms

/-!
# Inventory and restriction prices for the empty-source saturated `E₂` case

Integrating the small-part row floor gives the square and weighted-cost deficit
bounds on the hole region, deleting a measurable region keeps the signed kernel
inventory, and restrictions outside the neutral whole head, the deleted partner
and the exceptional atom receive support prices.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.EmptySatE2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Integrating the actual original small-part row floor pays both the
square bound and the stronger weighted cost bound on the same hole region.
The input is the pointwise old-row inventory; no integrated bound is assumed. -/
theorem integrated_deficit_bounds (H : Set Ω) (d a k : Ω → ℝ)
    {δ L E y D : ℝ} (hδ : 0 < δ) (hL : 0 < L) (hE : 0 ≤ E) (hEL : E < L)
    (hdint : IntegrableOn d H μ)
    (hparts : ∀ᵐ x ∂μ.restrict H,
      0 ≤ a x ∧ a x < L ∧ 0 ≤ k x ∧ 0 ≤ d x ∧
        δ * (L - a x) ≤ (L + E - 2 * a x - k x) * d x)
    (hbudget : (∫ x in H, d x ∂μ) ≤ δ * y)
    (hmass : μ.real H = L + y) (hyD : y ≤ D) :
    L ^ 2 ≤ E * y ∧ E * L + L ^ 2 ≤ E * μ.real H ∧ L ^ 2 ≤ E * D := by
  have hfloor : ∀ᵐ x ∂μ.restrict H, δ * L ≤ (L + E) * d x := by
    filter_upwards [hparts] with x hx
    exact small_atom_deficit_floor hδ hL hE hEL hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
      hx.2.2.2.2
  have hbound := integral_mono_ae (integrable_const (δ * L))
    (hdint.const_mul (L + E)) hfloor
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hbound
  rw [integral_const_mul] at hbound
  have hupper := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ L + E by linarith)
  have hprod : δ * (L ^ 2 - E * y) ≤ 0 := by
    rw [hmass] at hbound
    nlinarith only [hbound, hupper]
  have hsquare : L ^ 2 ≤ E * y :=
    sub_nonpos.mp (nonpos_of_mul_nonpos_right hprod hδ)
  have hstrong : E * L + L ^ 2 ≤ E * μ.real H := by rw [hmass]; nlinarith only [hsquare]
  exact ⟨hsquare, hstrong, hsquare.trans (mul_le_mul_of_nonneg_left hyD hE)⟩

/-- Deleting a measurable region retains the exact original signed
kernel inventory. Symmetry is needed only on the original product law. -/
theorem bounded_symmetric_complement_inventory (K : Ω × Ω → ℝ)
    (hK : Measurable K) (B : ℝ) (hB : ∀ p, ‖K p‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p = K p.swap)
    (I : Set Ω) (hI : MeasurableSet I) :
    (∫ p, K p ∂(μ.restrict Iᶜ).prod (μ.restrict Iᶜ)) =
      (∫ p, K p ∂μ.prod μ) - 2 * (∫ p, K p ∂(μ.restrict I).prod μ) +
        ∫ p, K p ∂(μ.restrict I).prod (μ.restrict I) := by
  have hi (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable K ν :=
    Integrable.of_bound hK.aestronglyMeasurable B (Eventually.of_forall hB)
  have hm : μ = μ.restrict I + μ.restrict Iᶜ :=
    (Measure.restrict_add_restrict_compl hI).symm
  have hfirst : (∫ p, K p ∂(μ.restrict I).prod μ) =
      (∫ p, K p ∂(μ.restrict I).prod (μ.restrict I)) +
        ∫ p, K p ∂(μ.restrict I).prod (μ.restrict Iᶜ) := by
    calc
      _ = ∫ p, K p ∂(μ.restrict I).prod (μ.restrict I + μ.restrict Iᶜ) := by
        rw [← hm]
      _ = _ := by rw [Measure.prod_add, integral_add_measure (hi _) (hi _)]
  have hsecond : (∫ p, K p ∂(μ.restrict Iᶜ).prod μ) =
      (∫ p, K p ∂(μ.restrict Iᶜ).prod (μ.restrict I)) +
        ∫ p, K p ∂(μ.restrict Iᶜ).prod (μ.restrict Iᶜ) := by
    calc
      _ = ∫ p, K p ∂(μ.restrict Iᶜ).prod (μ.restrict I + μ.restrict Iᶜ) := by
        rw [← hm]
      _ = _ := by rw [Measure.prod_add, integral_add_measure (hi _) (hi _)]
  have htotal : (∫ p, K p ∂μ.prod μ) =
      (∫ p, K p ∂(μ.restrict I).prod μ) + ∫ p, K p ∂(μ.restrict Iᶜ).prod μ := by
    calc
      _ = ∫ p, K p ∂(μ.restrict I + μ.restrict Iᶜ).prod μ := by rw [← hm]
      _ = _ := by rw [Measure.add_prod, integral_add_measure (hi _) (hi _)]
  have hcross : (∫ p, K p ∂(μ.restrict Iᶜ).prod (μ.restrict I)) =
      ∫ p, K p ∂(μ.restrict I).prod (μ.restrict Iᶜ) := by
    calc
      _ = ∫ p, K p.swap ∂(μ.restrict Iᶜ).prod (μ.restrict I) :=
        integral_congr_ae ((Measure.absolutelyContinuous_restrict.prod
          Measure.absolutelyContinuous_restrict).ae_le hsym)
      _ = _ := integral_prod_swap K
  rw [hcross] at hsecond
  linarith only [hfirst, hsecond, htotal]

private theorem integral_union_fst (K : Ω × Ω → ℝ)
    (I J : Set Ω) (hJ : MeasurableSet J) (hdis : Disjoint I J)
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (hIint : Integrable K ((μ.restrict I).prod ρ))
    (hJint : Integrable K ((μ.restrict J).prod ρ)) :
    (∫ p, K p ∂(μ.restrict (I ∪ J)).prod ρ) =
      (∫ p, K p ∂(μ.restrict I).prod ρ) + ∫ p, K p ∂(μ.restrict J).prod ρ := by
  rw [Measure.restrict_union hdis hJ, Measure.add_prod, integral_add_measure hIint hJint]

private theorem integral_union_snd (K : Ω × Ω → ℝ)
    (I J : Set Ω) (hJ : MeasurableSet J) (hdis : Disjoint I J)
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (hIint : Integrable K (ρ.prod (μ.restrict I)))
    (hJint : Integrable K (ρ.prod (μ.restrict J))) :
    (∫ p, K p ∂ρ.prod (μ.restrict (I ∪ J))) =
      (∫ p, K p ∂ρ.prod (μ.restrict I)) + ∫ p, K p ∂ρ.prod (μ.restrict J) := by
  rw [Measure.restrict_union hdis hJ, Measure.prod_add, integral_add_measure hIint hJint]

private theorem square_union_integral (K : Ω × Ω → ℝ) (hK : Measurable K)
    (B : ℝ) (hB : ∀ p, ‖K p‖ ≤ B) (hsym : ∀ p, K p = K p.swap)
    (I J : Set Ω) (_hI : MeasurableSet I) (hJ : MeasurableSet J) (hdis : Disjoint I J) :
    (∫ p, K p ∂(μ.restrict (I ∪ J)).prod (μ.restrict (I ∪ J))) =
      (∫ p, K p ∂(μ.restrict I).prod (μ.restrict I)) +
        2 * (∫ p, K p ∂(μ.restrict I).prod (μ.restrict J)) +
          ∫ p, K p ∂(μ.restrict J).prod (μ.restrict J) := by
  have hi (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable K ν :=
    Integrable.of_bound hK.aestronglyMeasurable B (Eventually.of_forall hB)
  rw [integral_union_fst K I J hJ hdis _ (hi _) (hi _),
    integral_union_snd K I J hJ hdis _ (hi _) (hi _),
    integral_union_snd K I J hJ hdis _ (hi _) (hi _)]
  have hswap : (∫ p, K p ∂(μ.restrict J).prod (μ.restrict I)) =
      ∫ p, K p ∂(μ.restrict I).prod (μ.restrict J) := by
    calc
      _ = ∫ p, K p.swap ∂(μ.restrict J).prod (μ.restrict I) :=
        integral_congr_ae (Eventually.of_forall hsym)
      _ = _ := integral_prod_swap K
  rw [hswap]
  ring

private theorem integral_const_block (K : Ω × Ω → ℝ) (I J : Set Ω) (c : ℝ)
    (hblock : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict J), K p = c) :
    (∫ p, K p ∂(μ.restrict I).prod (μ.restrict J)) = μ.real I * μ.real J * c := by
  rw [integral_congr_ae hblock, integral_const]
  simp only [smul_eq_mul]
  rw [← Set.univ_prod_univ, measureReal_prod_prod,
    measureReal_restrict_apply_univ, measureReal_restrict_apply_univ]

end Erdos1017.EmptySatE2

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Integrating the original flat rows over a real restricted set gives
its exact signed star mean. This uses original stationarity, without
assigning a stationary equation to the restricted dual. -/
theorem physical_restricted_row_mean (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (E : Set Ω) :
    (∫ p, PhysicalRepresentative.charge W m p.1 p.2 ∂(μ.restrict E).prod μ) =
      μ.real E * (2 * (c - m * d)) + m *
        ∫ p, (if PhysicalRepresentative.adjacency W m p.1 p.2 = true
          then (1 : ℝ) else 0) ∂(μ.restrict E).prod μ := by
  let Y : Ω × Ω → ℝ := fun p => PhysicalRepresentative.charge W m p.1 p.2
  let G : Ω × Ω → ℝ := fun p =>
    if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0
  have hY : Integrable Y ((μ.restrict E).prod μ) := Integrable.of_bound
    (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
    (Eventually.of_forall (fun p => by simpa only [Y, Real.norm_eq_abs] using
      PhysicalRepresentative.charge_bound W m p.1 p.2))
  have hG : Integrable G ((μ.restrict E).prod μ) := Integrable.of_bound
    ((measurable_of_countable (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
      (PhysicalRepresentative.measurable_adjacency W m)).aestronglyMeasurable 1
    (Eventually.of_forall (fun p => by dsimp only [G]; split_ifs <;> norm_num))
  have hflat : (∫ p, Y p - m * G p ∂(μ.restrict E).prod μ) =
      μ.real E * (2 * (c - m * d)) := by
    rw [integral_prod (fun p => Y p - m * G p) (hY.sub (hG.const_mul m))]
    have heq : (fun x => ∫ z, Y (x, z) - m * G (x, z) ∂μ) =ᵐ[μ.restrict E]
        fun _ => 2 * (c - m * d) :=
      ae_restrict_of_ae (S.ae_physical_shifted_stationary hW hd hgap)
    rw [integral_congr_ae heq, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  rw [integral_sub hY (hG.const_mul m), integral_const_mul] at hflat
  change (∫ p, Y p ∂(μ.restrict E).prod μ) = _
  linarith only [hflat]

/-- The original whole-fiber adjacency row pays its exact missing-star
integral on the original probability law. -/
theorem physical_whole_fiber_missing_star (S : SelectedHighLowStructure W m)
    (r : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    (∫ p, (1 - if PhysicalRepresentative.adjacency W m p.1 p.2 = true
      then (1 : ℝ) else 0) ∂(μ.restrict {x | S.ρ x = r.val}).prod μ) =
      μ.real {x | S.ρ x = r.val} * (1 - μ.real (S.rootNeighborhood r)) := by
  let I := {x | S.ρ x = r.val}
  let N := S.rootNeighborhood r
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood r
  have hpoint : ∀ᵐ p ∂(μ.restrict I).prod μ,
      (1 - if PhysicalRepresentative.adjacency W m p.1 p.2 = true then (1 : ℝ) else 0) =
        1 - N.indicator (fun _ => 1) p.2 := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl)
        (S.ae_root_adjacency r hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI)] with p hp hx
    have he := hp hx
    by_cases hy : p.2 ∈ N
    · have ha : PhysicalRepresentative.adjacency W m p.1 p.2 = true := he.mpr hy
      simp only [ha, ite_true, indicator_of_mem hy]
    · have ha : PhysicalRepresentative.adjacency W m p.1 p.2 = false :=
        Bool.eq_false_iff.mpr (fun ha => hy (he.mp ha))
      simp only [ha, Bool.false_eq_true, ite_false, indicator_of_notMem hy]
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) (μ.restrict I) := integrable_const 1
  have hind : Integrable (N.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hN
  have hindprod : Integrable (fun p : Ω × Ω => N.indicator (fun _ => (1 : ℝ)) p.2)
      ((μ.restrict I).prod μ) := by simpa only [one_mul] using hone.mul_prod hind
  have hfi : Integrable (fun p : Ω × Ω => 1 - N.indicator (fun _ => (1 : ℝ)) p.2)
      ((μ.restrict I).prod μ) := (integrable_const 1).sub hindprod
  rw [integral_congr_ae hpoint, integral_prod _ hfi]
  have hinner : (∫ z, 1 - N.indicator (fun _ => (1 : ℝ)) z ∂μ) = 1 - μ.real N := by
    rw [integral_sub (integrable_const 1) ((integrable_const 1).indicator hN),
      integral_indicator hN, integral_const, setIntegral_const]
    simp only [probReal_univ, smul_eq_mul, mul_one]
  simp only [hinner, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  rfl

/-- The partner's entire outside hole gives its exact original
neighborhood mass. The saturated first head is included almost everywhere. -/
theorem universal_partner_neighborhood_mass (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    μ.real (S.rootNeighborhood p) = 1 - S.originalAtomMass p -
      μ.real (S.universalPartnerHoleRegion r p) := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let N := S.rootNeighborhood p
  let H := S.universalPartnerHoleRegion r p
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood p
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hIin : ∀ᵐ x ∂μ, x ∈ I → x ∈ N := by
    filter_upwards [(ae_restrict_iff' hI).mp hpair.symm.row_on_other] with x hx hxi
    refine ⟨?_, ?_⟩
    · intro he
      exact hpair.1 (Subtype.ext (hxi.symm.trans he))
    · change 0 < p.val x
      rw [hx hxi]
      linarith
  have heq : H =ᵐ[μ] (P ∪ N)ᶜ := by
    filter_upwards [hIin] with x hx
    apply propext
    change (x ∉ I ∪ P ∪ N) ↔ x ∉ P ∪ N
    constructor
    · intro h hp
      exact h (hp.elim (fun h => Or.inl (Or.inr h)) Or.inr)
    · intro h hp
      rcases hp with (hi | hp) | hn
      · exact h (Or.inr (hx hi))
      · exact h (Or.inl hp)
      · exact h (Or.inr hn)
  have hmass : μ.real H = 1 - μ.real P - μ.real N := by
    rw [measureReal_congr heq, measureReal_compl (hP.union hN), probReal_univ,
      measureReal_union (S.rootNeighborhood_disjoint p) hN]
    ring
  change μ.real N = 1 - μ.real P - μ.real H
  linarith only [hmass]

/-- A neutral original whole head sees exactly its measurable complement. -/
theorem neutral_rootNeighborhood_mass (S : SelectedHighLowStructure W m)
    (r : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    μ.real (S.rootNeighborhood r) = 1 - S.originalAtomMass r := by
  have heq : S.rootNeighborhood r =ᵐ[μ] {x | S.ρ x = r.val}ᶜ :=
    (S.ae_universal_rootNeighborhood_iff r hW hd hgap hN).mono (fun _ h => propext h)
  rw [measureReal_congr heq, measureReal_compl (S.hfibers r.val r.property).1, probReal_univ]
  rfl

/-- The two actual saturated original heads have their literal charge
and missing-square inventories, before any outside region is priced. -/
theorem physical_saturated_two_head_squares (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    let E := {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}
    (∫ q, PhysicalRepresentative.charge W m q.1 q.2
      ∂(μ.restrict E).prod (μ.restrict E)) =
        2 * μ.real {x | S.ρ x = r.val} * μ.real {x | S.ρ x = p.val} ∧
    (∫ q, (1 - if PhysicalRepresentative.adjacency W m q.1 q.2 = true then (1 : ℝ) else 0)
      ∂(μ.restrict E).prod (μ.restrict E)) =
        (μ.real {x | S.ρ x = r.val}) ^ 2 + (μ.real {x | S.ρ x = p.val}) ^ 2 := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let Y : Ω × Ω → ℝ := fun q => PhysicalRepresentative.charge W m q.1 q.2
  let M : Ω × Ω → ℝ := fun q =>
    1 - if PhysicalRepresentative.adjacency W m q.1 q.2 = true then 1 else 0
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hdis : Disjoint I P := Set.disjoint_left.mpr (fun _ hx hy =>
    hpair.1 (Subtype.ext (hx.symm.trans hy)))
  have hY : Measurable Y := PhysicalRepresentative.measurable_charge W m
  have hYb (q : Ω × Ω) : ‖Y q‖ ≤ 3 := by
    simpa only [Y, Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m q.1 q.2
  have hM : Measurable M := measurable_const.sub
    ((measurable_of_countable (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
      (PhysicalRepresentative.measurable_adjacency W m))
  have hMb (q : Ω × Ω) : ‖M q‖ ≤ 1 := by dsimp only [M]; split_ifs <;> norm_num
  have hYY := EmptySatE2.square_union_integral (μ := μ) Y hY 3 hYb
    (fun q => PhysicalRepresentative.charge_symm W m q.1 q.2) I P hI hP hdis
  have hMM := EmptySatE2.square_union_integral (μ := μ) M hM 1 hMb
    (fun q => by dsimp only [M]; rw [PhysicalRepresentative.adjacency_symm W m q.1 q.2]; rfl)
    I P hI hP hdis
  have hself (u : S.I) :
      (∀ᵐ q ∂(μ.restrict {x | S.ρ x = u.val}).prod (μ.restrict {x | S.ρ x = u.val}),
        Y q = 0) ∧
      (∀ᵐ q ∂(μ.restrict {x | S.ρ x = u.val}).prod (μ.restrict {x | S.ρ x = u.val}),
        M q = 1) := by
    have hu : MeasurableSet {x | S.ρ x = u.val} := (S.hfibers u.val u.property).1
    have heq : ∀ᵐ q ∂(μ.restrict {x | S.ρ x = u.val}).prod
        (μ.restrict {x | S.ρ x = u.val}), Y q = 0 ∧ M q = 1 := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) (S.ae_root_adjacency u hW hd hgap),
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hu),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hu)] with q hq hx hy
      have hf : PhysicalRepresentative.adjacency W m q.1 q.2 = false :=
        Bool.eq_false_iff.mpr (fun he => ((hq hx).mp he).1 hy)
      constructor
      · exact PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2 hf
      · simp only [M, hf, Bool.false_eq_true, ite_false, sub_zero]
    exact ⟨heq.mono (fun _ h => h.1), heq.mono (fun _ h => h.2)⟩
  have hcross : ∀ᵐ q ∂(μ.restrict I).prod (μ.restrict P), Y q = 1 ∧ M q = 0 := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) hpair.2,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
        (PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with q hq hy hx hp
    have hYone : Y q = 1 := hy.trans (hq hx hp)
    have hA : PhysicalRepresentative.adjacency W m q.1 q.2 = true := by
      cases he : PhysicalRepresentative.adjacency W m q.1 q.2
      · have hz := PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2 he
        change Y q = 0 at hz
        linarith only [hYone, hz]
      · rfl
    exact ⟨hYone, by simp only [M, hA, ite_true, sub_self]⟩
  have hIIY := EmptySatE2.integral_const_block (μ := μ) Y I I 0 (hself r).1
  have hPPY := EmptySatE2.integral_const_block (μ := μ) Y P P 0 (hself p).1
  have hIPY := EmptySatE2.integral_const_block (μ := μ) Y I P 1
    (hcross.mono (fun _ h => h.1))
  have hIIM := EmptySatE2.integral_const_block (μ := μ) M I I 1 (hself r).2
  have hPPM := EmptySatE2.integral_const_block (μ := μ) M P P 1 (hself p).2
  have hIPM := EmptySatE2.integral_const_block (μ := μ) M I P 0
    (hcross.mono (fun _ h => h.2))
  rw [hIIY, hPPY, hIPY] at hYY
  rw [hIIM, hPPM, hIPM] at hMM
  constructor
  · change (∫ q, Y q ∂(μ.restrict (I ∪ P)).prod (μ.restrict (I ∪ P))) = _
    linarith only [hYY]
  · change (∫ q, M q ∂(μ.restrict (I ∪ P)).prod (μ.restrict (I ∪ P))) = _
    nlinarith only [hMM]

/-- The original optimum pays the exact charge inventory on every
measurable physical complement, including arbitrary missing cross pairs. -/
theorem physical_complement_cost_balance (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (E : Set Ω) (hE : MeasurableSet E) :
    FiniteCappedSamplingCost.physicalObjective (μ.restrict Eᶜ)
      (PhysicalRepresentative.charge W m) = c - μ.real E * (2 * (c - m * d)) -
        m * (∫ p, (if PhysicalRepresentative.adjacency W m p.1 p.2 = true
          then (1 : ℝ) else 0) ∂(μ.restrict E).prod μ) +
        (∫ p, PhysicalRepresentative.charge W m p.1 p.2
          ∂(μ.restrict E).prod (μ.restrict E)) / 2 := by
  have hcomp := EmptySatE2.bounded_symmetric_complement_inventory (μ := μ)
    (fun p : Ω × Ω => PhysicalRepresentative.charge W m p.1 p.2)
    (PhysicalRepresentative.measurable_charge W m) 3
    (fun p => by simpa only [Real.norm_eq_abs] using
      PhysicalRepresentative.charge_bound W m p.1 p.2)
    (Eventually.of_forall (fun p => PhysicalRepresentative.charge_symm W m p.1 p.2)) E hE
  have hrow := S.physical_restricted_row_mean hW hd hgap E
  have htotal := (PhysicalRepresentative.objective_eq W m
    (hW.strict_gap_structure hd hgap).strict_support).trans hW.objective_eq
  unfold FiniteCappedSamplingCost.physicalObjective at htotal ⊢
  linarith only [hcomp, hrow, htotal]

/-- The same original complement keeps its exact missing-pair inventory;
no missing cross rectangle is discarded. -/
theorem physical_complement_missing_balance (_S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (E : Set Ω) (hE : MeasurableSet E) :
    (∫ p, (1 - if PhysicalRepresentative.adjacency W m p.1 p.2 = true
      then (1 : ℝ) else 0) ∂(μ.restrict Eᶜ).prod (μ.restrict Eᶜ)) =
      1 - 2 * d - 2 * (∫ p, (1 - if PhysicalRepresentative.adjacency W m p.1 p.2 = true
        then (1 : ℝ) else 0) ∂(μ.restrict E).prod μ) +
        ∫ p, (1 - if PhysicalRepresentative.adjacency W m p.1 p.2 = true
          then (1 : ℝ) else 0) ∂(μ.restrict E).prod (μ.restrict E) := by
  let G : Ω × Ω → ℝ := fun p =>
    if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0
  have hGm : Measurable G :=
    (measurable_of_countable (fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
      (PhysicalRepresentative.measurable_adjacency W m)
  have hGb (p : Ω × Ω) : ‖G p‖ ≤ 1 := by dsimp only [G]; split_ifs <;> norm_num
  have hMb (p : Ω × Ω) : ‖1 - G p‖ ≤ 1 := by dsimp only [G]; split_ifs <;> norm_num
  have hMi : Integrable G (μ.prod μ) := Integrable.of_bound hGm.aestronglyMeasurable 1
    (Eventually.of_forall hGb)
  have htotal : (∫ p, 1 - G p ∂μ.prod μ) = 1 - 2 * d := by
    have hdensity := (PhysicalRepresentative.density_eq W m
      (hW.strict_gap_structure hd hgap).strict_support).trans hW.density_eq
    change (∫ p, G p ∂μ.prod μ) / 2 = d at hdensity
    rw [integral_sub (integrable_const 1) hMi, integral_const]
    simp only [probReal_univ, smul_eq_mul, mul_one]
    linarith only [hdensity]
  have hcomp := EmptySatE2.bounded_symmetric_complement_inventory (μ := μ)
    (fun p => 1 - G p) (measurable_const.sub hGm) 1 hMb
    (Eventually.of_forall (fun p => by
      dsimp only [G]
      rw [PhysicalRepresentative.adjacency_symm W m p.1 p.2]
      rfl)) E hE
  rw [htotal] at hcomp
  exact hcomp

/-- Delete the actual saturated partner and retain the complete signed
charge and missing-square inventory of the real outside region. -/
theorem empty_sat_deleted_partner_inventory (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let s := μ.real (S.universalPartnerHoleRegion r p)
    let O := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ
    let HI := (∫ q, PhysicalRepresentative.charge W m q.1 q.2
      ∂(μ.restrict {x | S.ρ x = r.val}).prod (μ.restrict O)) / A
    let CO := FiniteCappedSamplingCost.physicalObjective (μ.restrict O)
      (PhysicalRepresentative.charge W m)
    let QO := ∫ q, (1 - if PhysicalRepresentative.adjacency W m q.1 q.2 = true
      then (1 : ℝ) else 0) ∂(μ.restrict O).prod (μ.restrict O)
    HI = 2 * (c - m * d) + m - b - m * A ∧
      CO = c - (A + b) * (2 * (c - m * d)) -
        m * (A + b - A ^ 2 - b ^ 2 - b * s) + A * b ∧
      QO = 1 - 2 * d - A ^ 2 - b ^ 2 - 2 * b * s ∧ μ.real O = 1 - A - b := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let E := I ∪ P
  let O := Eᶜ
  let A := μ.real I
  let b := μ.real P
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let Y : Ω × Ω → ℝ := fun q => PhysicalRepresentative.charge W m q.1 q.2
  let G : Ω × Ω → ℝ := fun q =>
    if PhysicalRepresentative.adjacency W m q.1 q.2 = true then 1 else 0
  let M : Ω × Ω → ℝ := fun q => 1 - G q
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hE : MeasurableSet E := hI.union hP
  have hdis : Disjoint I P := Set.disjoint_left.mpr (fun _ hx hy =>
    hpair.1 (Subtype.ext (hx.symm.trans hy)))
  have hEmass : μ.real E = A + b := measureReal_union hdis hP
  have hOmass : μ.real O = 1 - A - b := by
    rw [measureReal_compl hE, probReal_univ, hEmass]
    ring
  have hYm : Measurable Y := PhysicalRepresentative.measurable_charge W m
  have hGm : Measurable G :=
    (measurable_of_countable (fun v : Bool => if v = true then (1 : ℝ) else 0)).comp
      (PhysicalRepresentative.measurable_adjacency W m)
  have hYint (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable Y ν :=
    Integrable.of_bound hYm.aestronglyMeasurable 3 (Eventually.of_forall (fun q => by
      simpa only [Y, Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m q.1 q.2))
  have hGint (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable G ν :=
    Integrable.of_bound hGm.aestronglyMeasurable 1
      (Eventually.of_forall (fun q => by dsimp only [G]; split_ifs <;> norm_num))
  have hMint (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable M ν :=
    (integrable_const 1).sub (hGint ν)
  have hMrel (C : Set Ω) : (∫ q, M q ∂(μ.restrict C).prod μ) =
      μ.real C - ∫ q, G q ∂(μ.restrict C).prod μ := by
    have hone := EmptySatE2.integral_const_block (μ := μ)
      (fun _ : Ω × Ω => (1 : ℝ)) C univ 1 (Eventually.of_forall (fun _ => rfl))
    simp only [Measure.restrict_univ, probReal_univ, mul_one] at hone
    dsimp only [M]
    rw [integral_sub (integrable_const 1) (hGint _), hone]
  have hMI := S.physical_whole_fiber_missing_star r hW hd hgap
  rw [S.neutral_rootNeighborhood_mass r hW hd hgap hN] at hMI
  have hMP := S.physical_whole_fiber_missing_star p hW hd hgap
  rw [S.universal_partner_neighborhood_mass r p hpair hW hd hgap] at hMP
  change (∫ q, M q ∂(μ.restrict I).prod μ) = A * (1 - (1 - A)) at hMI
  change (∫ q, M q ∂(μ.restrict P).prod μ) = b * (1 - (1 - b - s)) at hMP
  have hME : (∫ q, M q ∂(μ.restrict E).prod μ) = A ^ 2 + b ^ 2 + b * s := by
    rw [EmptySatE2.integral_union_fst M I P hP hdis μ (hMint _) (hMint _), hMI, hMP]
    ring
  have hGI : (∫ q, G q ∂(μ.restrict I).prod μ) = A - A ^ 2 := by
    have h := hMrel I
    nlinarith only [h, hMI]
  have hGE : (∫ q, G q ∂(μ.restrict E).prod μ) = A + b - A ^ 2 - b ^ 2 - b * s := by
    have h := hMrel E
    rw [hEmass, hME] at h
    linarith only [h]
  obtain ⟨hYE, hMM⟩ := S.physical_saturated_two_head_squares r p hpair hW hd hgap
  change (∫ q, Y q ∂(μ.restrict E).prod (μ.restrict E)) = 2 * A * b at hYE
  change (∫ q, M q ∂(μ.restrict E).prod (μ.restrict E)) = A ^ 2 + b ^ 2 at hMM
  have hCO := S.physical_complement_cost_balance hW hd hgap E hE
  have hQO := S.physical_complement_missing_balance hW hd hgap E hE
  change FiniteCappedSamplingCost.physicalObjective (μ.restrict O)
    (PhysicalRepresentative.charge W m) = c - μ.real E * (2 * (c - m * d)) -
      m * (∫ q, G q ∂(μ.restrict E).prod μ) +
        (∫ q, Y q ∂(μ.restrict E).prod (μ.restrict E)) / 2 at hCO
  change (∫ q, M q ∂(μ.restrict O).prod (μ.restrict O)) =
    1 - 2 * d - 2 * (∫ q, M q ∂(μ.restrict E).prod μ) +
      ∫ q, M q ∂(μ.restrict E).prod (μ.restrict E) at hQO
  rw [hEmass, hGE, hYE] at hCO
  rw [hME, hMM] at hQO
  have hII : (∫ q, Y q ∂(μ.restrict I).prod (μ.restrict I)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) (S.ae_root_fiber_physical_independent r hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hI)] with q hq hx hy
    exact PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2 (hq hx hy)
  have hIP : (∫ q, Y q ∂(μ.restrict I).prod (μ.restrict P)) = A * b := by
    have hc : ∀ᵐ q ∂(μ.restrict I).prod (μ.restrict P), Y q = 1 := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) hpair.2,
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
          (PhysicalRepresentative.charge_ae_eq W m
            (hW.strict_gap_structure hd hgap).strict_support),
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with q hq hy hx hp
      exact hy.trans (hq hx hp)
    simpa only [mul_one] using EmptySatE2.integral_const_block (μ := μ) Y I P 1 hc
  have hIsplit : (∫ q, Y q ∂(μ.restrict I).prod μ) =
      A * b + ∫ q, Y q ∂(μ.restrict I).prod (μ.restrict O) := by
    have hm : μ = μ.restrict E + μ.restrict O :=
      (Measure.restrict_add_restrict_compl hE).symm
    calc
      _ = ∫ q, Y q ∂(μ.restrict I).prod (μ.restrict E + μ.restrict O) := by rw [← hm]
      _ = _ := by
        rw [Measure.prod_add, integral_add_measure (hYint _) (hYint _),
          EmptySatE2.integral_union_snd Y I P hP hdis _ (hYint _) (hYint _), hII, hIP]
        ring
  have hImean := S.physical_restricted_row_mean hW hd hgap I
  change (∫ q, Y q ∂(μ.restrict I).prod μ) = A * (2 * (c - m * d)) +
    m * (∫ q, G q ∂(μ.restrict I).prod μ) at hImean
  rw [hGI] at hImean
  have hApos : 0 < A := ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne'
    (measure_ne_top μ I)
  have hHI : (∫ q, Y q ∂(μ.restrict I).prod (μ.restrict O)) / A =
      2 * (c - m * d) + m - b - m * A := by
    apply (div_eq_iff hApos.ne').mpr
    nlinarith only [hIsplit, hImean]
  refine ⟨hHI, ?_, ?_, hOmass⟩
  · change FiniteCappedSamplingCost.physicalObjective (μ.restrict O)
      (PhysicalRepresentative.charge W m) = c - (A + b) * (2 * (c - m * d)) -
        m * (A + b - A ^ 2 - b ^ 2 - b * s) + A * b
    nlinarith only [hCO]
  · change (∫ q, M q ∂(μ.restrict O).prod (μ.restrict O)) =
      1 - 2 * d - A ^ 2 - b ^ 2 - 2 * b * s
    nlinarith only [hQO]

/-- Price the actual restriction after the exceptional original atom
is also removed. Its current outside cost is computed from original rows;
no stationary equation is assigned to either restricted measure. -/
theorem empty_sat_exceptional_inventory (S : SelectedHighLowStructure W m)
    (r p i : S.I) (hpair : S.IsSaturatedAtomPair r p) (hir : i ≠ r) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (di : ℝ) (hdef : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      S.universalRootDeficit r x = di)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val → adjacencyKernel W q.1 q.2 =
      if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let a := S.originalAtomMass i
    let s := μ.real (S.universalPartnerHoleRegion r p)
    let K := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val} ∪ {x | S.ρ x = i.val})ᶜ
    let HI := (∫ q, PhysicalRepresentative.charge W m q.1 q.2
      ∂(μ.restrict {x | S.ρ x = r.val}).prod (μ.restrict K)) / A
    let CK := FiniteCappedSamplingCost.physicalObjective (μ.restrict K)
      (PhysicalRepresentative.charge W m)
    let QK := ∫ q, (1 - if PhysicalRepresentative.adjacency W m q.1 q.2 = true
      then (1 : ℝ) else 0) ∂(μ.restrict K).prod (μ.restrict K)
    HI = 2 * (c - m * d) + m - a - b - m * A + a * di ∧
      CK = c - (A + b + a) * (2 * (c - m * d)) -
        m * (A + b + a - A ^ 2 - b ^ 2 - b * s - a * (a + b)) +
          A * b + A * a * (1 - di) ∧
      QK = 1 - 2 * d - A ^ 2 - b ^ 2 - a ^ 2 - 2 * b * s ∧
        μ.real K = 1 - A - b - a := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let C := {x | S.ρ x = i.val}
  let F := I ∪ P
  let O := Fᶜ
  let K := (F ∪ C)ᶜ
  let ν := μ.restrict O
  let A := μ.real I
  let b := μ.real P
  let a := μ.real C
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let Y : Ω × Ω → ℝ := fun q => PhysicalRepresentative.charge W m q.1 q.2
  let G : Ω × Ω → ℝ := fun q =>
    if PhysicalRepresentative.adjacency W m q.1 q.2 = true then 1 else 0
  let M : Ω × Ω → ℝ := fun q => 1 - G q
  let CO := FiniteCappedSamplingCost.physicalObjective ν (PhysicalRepresentative.charge W m)
  let QO := ∫ q, M q ∂ν.prod ν
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hC : MeasurableSet C := (S.hfibers i.val i.property).1
  have hF : MeasurableSet F := hI.union hP
  have hIP : Disjoint I P := disjoint_left.mpr (fun _ hx hy =>
    hpair.1 (Subtype.ext (hx.symm.trans hy)))
  have hCP : Disjoint C P := disjoint_left.mpr (fun _ hx hy => hip (Subtype.ext (hx.symm.trans hy)))
  have hFC : Disjoint F C := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases hx with hr | hp
    · exact hir (Subtype.ext (hy.symm.trans hr))
    · exact hip (Subtype.ext (hy.symm.trans hp))
  have hCsub : C ⊆ O := fun _ hc hf => Set.disjoint_left.mp hFC hf hc
  have hνC : ν.restrict C = μ.restrict C := by
    rw [Measure.restrict_restrict hC, inter_eq_left.mpr hCsub]
  have hνK : ν.restrict Cᶜ = μ.restrict K := by
    rw [Measure.restrict_restrict hC.compl]
    congr 1
    ext x
    simp only [K, O, mem_inter_iff, mem_compl_iff, mem_union]
    tauto
  have hνmassC : ν.real C = a := by
    calc
      _ = (ν.restrict C).real univ := (measureReal_restrict_apply_univ C).symm
      _ = a := by rw [hνC, measureReal_restrict_apply_univ]
  have hmassK : μ.real K = 1 - A - b - a := by
    rw [measureReal_compl (hF.union hC), probReal_univ, measureReal_union hFC hC,
      measureReal_union hIP hP]
    ring
  have hYm : Measurable Y := PhysicalRepresentative.measurable_charge W m
  have hYb (q : Ω × Ω) : ‖Y q‖ ≤ 3 := by
    simpa only [Y, Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m q.1 q.2
  have hGm : Measurable G :=
    (measurable_of_countable (fun v : Bool => if v = true then (1 : ℝ) else 0)).comp
      (PhysicalRepresentative.measurable_adjacency W m)
  have hMm : Measurable M := measurable_const.sub hGm
  have hMb (q : Ω × Ω) : ‖M q‖ ≤ 1 := by dsimp only [M, G]; split_ifs <;> norm_num
  have hYint (ρ : Measure (Ω × Ω)) [IsFiniteMeasure ρ] : Integrable Y ρ :=
    Integrable.of_bound hYm.aestronglyMeasurable 3 (Eventually.of_forall hYb)
  have hGint (ρ : Measure (Ω × Ω)) [IsFiniteMeasure ρ] : Integrable G ρ :=
    Integrable.of_bound hGm.aestronglyMeasurable 1
      (Eventually.of_forall (fun q => by dsimp only [G]; split_ifs <;> norm_num))
  have hpoint : ∀ᵐ q ∂(μ.restrict C).prod μ, M q = (C ∪ P).indicator (fun _ => 1) q.2 := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl) hprivate,
      ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl)
        (PhysicalRepresentative.adjacency_moment_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hC)] with q hq hm hx
    have hr := hq hx
    change adjacencyKernel W q.1 q.2 = (if q.2 ∈ C ∪ P then 0 else 1) at hr
    change adjacencyKernel W q.1 q.2 = G q at hm
    have he := hm.symm.trans hr
    by_cases hz : q.2 ∈ C ∪ P
    · have hf : PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
        cases ha : PhysicalRepresentative.adjacency W m q.1 q.2 <;> simp_all [G]
      simp only [M, G, hf, Bool.false_eq_true, ite_false, sub_zero, indicator_of_mem hz]
    · have ht : PhysicalRepresentative.adjacency W m q.1 q.2 = true := by
        cases ha : PhysicalRepresentative.adjacency W m q.1 q.2 <;> simp_all [G]
      simp only [M, G, ht, ite_true, sub_self, indicator_of_notMem hz]
  have hMC : (∫ q, M q ∂(μ.restrict C).prod μ) = a * (a + b) := by
    rw [integral_congr_ae hpoint, integral_fun_snd, integral_indicator (hC.union hP),
      setIntegral_const, measureReal_restrict_apply_univ, measureReal_union hCP hP]
    simp only [smul_eq_mul, mul_one, a, b]
  have hMCν : (∫ q, M q ∂(μ.restrict C).prod ν) = a ^ 2 := by
    have hp : ∀ᵐ q ∂(μ.restrict C).prod ν, M q = C.indicator (fun _ => 1) q.2 := by
      filter_upwards [ae_mono (Measure.prod_mono le_rfl Measure.restrict_le_self) hpoint,
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hF.compl)] with q hq hz
      have hnP : q.2 ∉ P := fun hp => hz (Or.inr hp)
      have he : (C ∪ P).indicator (fun _ : Ω => (1 : ℝ)) q.2 =
          C.indicator (fun _ => 1) q.2 := by
        by_cases hc : q.2 ∈ C <;> simp [hc, hnP]
      exact hq.trans he
    rw [integral_congr_ae hp, integral_fun_snd, integral_indicator hC, setIntegral_const,
      measureReal_restrict_apply_univ, hνmassC]
    simp only [smul_eq_mul, mul_one]
    change a * a = a ^ 2
    ring
  have hCC : ∀ᵐ q ∂(μ.restrict C).prod (μ.restrict C), Y q = 0 ∧ M q = 1 := by
    filter_upwards [ae_mono (Measure.prod_mono le_rfl Measure.restrict_le_self) hpoint,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hC)] with q hq hz
    have hMone : M q = 1 := by
      have hm : q.2 ∈ C ∪ P := Or.inl hz
      rwa [indicator_of_mem hm] at hq
    have hf : PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
      cases ha : PhysicalRepresentative.adjacency W m q.1 q.2 <;> simp_all [M, G]
    exact ⟨PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2 hf, hMone⟩
  have hCCY := EmptySatE2.integral_const_block (μ := μ) Y C C 0 (hCC.mono (fun _ h => h.1))
  have hCCM := EmptySatE2.integral_const_block (μ := μ) M C C 1 (hCC.mono (fun _ h => h.2))
  have hCPY : (∫ q, Y q ∂(μ.restrict C).prod (μ.restrict P)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_mono (Measure.prod_mono le_rfl Measure.restrict_le_self) hpoint,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with q hq hz
    have hMone : M q = 1 := by
      have hm : q.2 ∈ C ∪ P := Or.inr hz
      rwa [indicator_of_mem hm] at hq
    have hf : PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
      cases ha : PhysicalRepresentative.adjacency W m q.1 q.2 <;> simp_all [M, G]
    exact PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2 hf
  have hIC : (∫ q, Y q ∂(μ.restrict I).prod (μ.restrict C)) = A * a * (1 - di) := by
    have hc : ∀ᵐ q ∂(μ.restrict I).prod (μ.restrict C), Y q = 1 - di := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) (S.ae_root_charge r hW hd hgap),
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
        Measure.quasiMeasurePreserving_snd.ae hdef] with q hq hx hdq
      have he := hq hx
      change 1 - S.rootChargeRow r q.2 = di at hdq
      change Y q = _ at he
      linarith only [he, hdq]
    exact EmptySatE2.integral_const_block (μ := μ) Y I C (1 - di) hc
  have hCI : (∫ q, Y q ∂(μ.restrict C).prod (μ.restrict I)) = A * a * (1 - di) := by
    calc
      _ = ∫ q, Y q.swap ∂(μ.restrict C).prod (μ.restrict I) :=
        integral_congr_ae (Eventually.of_forall (fun q =>
          PhysicalRepresentative.charge_symm W m q.1 q.2))
      _ = ∫ q, Y q ∂(μ.restrict I).prod (μ.restrict C) := integral_prod_swap Y
      _ = _ := hIC
  have hGC : (∫ q, G q ∂(μ.restrict C).prod μ) = a - a * (a + b) := by
    have hMrel : (∫ q, M q ∂(μ.restrict C).prod μ) =
        a - ∫ q, G q ∂(μ.restrict C).prod μ := by
      dsimp only [M]
      rw [integral_sub (integrable_const 1) (hGint _), integral_const]
      rw [← Set.univ_prod_univ, measureReal_prod_prod,
        measureReal_restrict_apply_univ, probReal_univ, smul_eq_mul, mul_one]
      simp only [mul_one, a]
    linarith only [hMC, hMrel]
  have hCmean := S.physical_restricted_row_mean hW hd hgap C
  change (∫ q, Y q ∂(μ.restrict C).prod μ) = a * (2 * (c - m * d)) +
    m * (∫ q, G q ∂(μ.restrict C).prod μ) at hCmean
  rw [hGC] at hCmean
  have hCν : (∫ q, Y q ∂(μ.restrict C).prod ν) =
      a * (2 * (c - m * d)) + m * (a - a * (a + b)) - A * a * (1 - di) := by
    have hm : μ = μ.restrict F + ν := (Measure.restrict_add_restrict_compl hF).symm
    have hsplit : (∫ q, Y q ∂(μ.restrict C).prod μ) =
        (∫ q, Y q ∂(μ.restrict C).prod (μ.restrict F)) +
          ∫ q, Y q ∂(μ.restrict C).prod ν := by
      calc
        _ = ∫ q, Y q ∂(μ.restrict C).prod (μ.restrict F + ν) := by rw [← hm]
        _ = _ := by rw [Measure.prod_add, integral_add_measure (hYint _) (hYint _)]
    rw [EmptySatE2.integral_union_snd Y I P hP hIP _ (hYint _) (hYint _), hCI, hCPY] at hsplit
    linarith only [hsplit, hCmean]
  obtain ⟨hHI0, hCO0, hQO0, _⟩ := S.empty_sat_deleted_partner_inventory r p hpair hW hd hgap hN
  change (∫ q, Y q ∂(μ.restrict I).prod ν) / A =
    2 * (c - m * d) + m - b - m * A at hHI0
  change CO = c - (A + b) * (2 * (c - m * d)) -
    m * (A + b - A ^ 2 - b ^ 2 - b * s) + A * b at hCO0
  change QO = 1 - 2 * d - A ^ 2 - b ^ 2 - 2 * b * s at hQO0
  have hYs := EmptySatE2.bounded_symmetric_complement_inventory (μ := ν) Y hYm 3 hYb
    (Eventually.of_forall (fun q => PhysicalRepresentative.charge_symm W m q.1 q.2)) C hC
  have hMs := EmptySatE2.bounded_symmetric_complement_inventory (μ := ν) M hMm 1 hMb
    (Eventually.of_forall (fun q => by
      dsimp only [M, G]
      rw [PhysicalRepresentative.adjacency_symm W m q.1 q.2]
      rfl)) C hC
  rw [hνK, hνC, hCν, hCCY] at hYs
  rw [hνK, hνC, hMCν, hCCM] at hMs
  have hApos : 0 < A := ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne'
    (measure_ne_top μ I)
  have hHI0' := (div_eq_iff hApos.ne').mp hHI0
  have hIK : (∫ q, Y q ∂(μ.restrict I).prod (μ.restrict K)) / A =
      2 * (c - m * d) + m - a - b - m * A + a * di := by
    have hm : ν = μ.restrict C + μ.restrict K := by
      rw [← hνC, ← hνK]
      exact (Measure.restrict_add_restrict_compl hC).symm
    have hsplit : (∫ q, Y q ∂(μ.restrict I).prod ν) =
        (∫ q, Y q ∂(μ.restrict I).prod (μ.restrict C)) +
          ∫ q, Y q ∂(μ.restrict I).prod (μ.restrict K) := by
      calc
        _ = ∫ q, Y q ∂(μ.restrict I).prod (μ.restrict C + μ.restrict K) := by rw [← hm]
        _ = _ := by rw [Measure.prod_add, integral_add_measure (hYint _) (hYint _)]
    rw [hIC] at hsplit
    apply (div_eq_iff hApos.ne').mpr
    nlinarith only [hsplit, hHI0']
  refine ⟨hIK, ?_, ?_, hmassK⟩
  · change FiniteCappedSamplingCost.physicalObjective (μ.restrict K)
      (PhysicalRepresentative.charge W m) = c - (A + b + a) * (2 * (c - m * d)) -
        m * (A + b + a - A ^ 2 - b ^ 2 - b * s - a * (a + b)) +
          A * b + A * a * (1 - di)
    change (∫ q, Y q ∂(μ.restrict K).prod (μ.restrict K)) / 2 = _
    change (∫ q, Y q ∂ν.prod ν) / 2 = c - (A + b) * (2 * (c - m * d)) -
      m * (A + b - A ^ 2 - b ^ 2 - b * s) + A * b at hCO0
    nlinarith only [hYs, hCO0]
  · change (∫ q, M q ∂(μ.restrict K).prod (μ.restrict K)) =
      1 - 2 * d - A ^ 2 - b ^ 2 - a ^ 2 - 2 * b * s
    change (∫ q, M q ∂(μ.restrict K).prod (μ.restrict K)) = QO - 2 * a ^ 2 + a * a * 1
      at hMs
    nlinarith only [hMs, hQO0]

/-- With no large original H-part, the same actual hole rows and deficit
cap give both integrated prices. All row, capacity and mass-ratio facts
come from the original selected model. The small-part premise is only
this branch's literal original missing-H section inequality. -/
theorem empty_sat_small_parts_integrated_bounds (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hholes : 0 < μ (S.universalPartnerHoleRegion r p)) :
    let H := S.universalPartnerHoleRegion r p
    let U := S.universalPartnerCommonRegion r p
    let D := (1 - m - 4 * (c - m * d)) / (1 + m)
    let L := μ.real H + μ.real U - D
    let E := D - S.originalAtomMass r
    0 < L → E < L →
      (∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L) →
      L ^ 2 ≤ E * (D - μ.real U) ∧ E * L + L ^ 2 ≤ E * μ.real H ∧ L ^ 2 ≤ E * D := by
  dsimp only
  intro hL hEL hsmall
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let D := (1 - m - 4 * (c - m * d)) / (1 + m)
  let L := μ.real H + μ.real U - D
  let E := D - S.originalAtomMass r
  have hδ : 0 < 1 + m := by linarith only [hell]
  have hratio : (1 + m) * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D]
    exact mul_div_cancel₀ _ hδ.ne'
  have hAD := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap hell hN hholes
  have hE : 0 ≤ E := sub_nonneg.mpr hAD
  have hbudget : (∫ x in H, S.universalRootDeficit r x ∂μ) ≤
      (1 + m) * (D - μ.real U) := by
    have hcap := S.universalPartnerHole_deficit_cap r p hpair hW hd hgap hN
    change (∫ x in H, S.universalRootDeficit r x ∂μ) ≤
      1 - m - 4 * (c - m * d) - (1 + m) * μ.real U at hcap
    nlinarith only [hcap, hratio]
  have hparts : ∀ᵐ x ∂μ.restrict H,
      0 ≤ S.universalPartnerHoleMissingMass r p x ∧
        S.universalPartnerHoleMissingMass r p x < L ∧
        0 ≤ S.universalPartnerCommonMissingMass r p x ∧
        0 ≤ S.universalRootDeficit r x ∧
        (1 + m) * (L - S.universalPartnerHoleMissingMass r p x) ≤
          (L + E - 2 * S.universalPartnerHoleMissingMass r p x -
            S.universalPartnerCommonMissingMass r p x) * S.universalRootDeficit r x := by
    filter_upwards [S.ae_universalPartnerHole_deficit_row r p hpair hW hd hgap hell hN,
      hsmall] with x hx hs
    refine ⟨S.universalPartnerHoleMissingMass_nonneg r p x, hs,
      S.universalPartnerCommonMissingMass_nonneg r p x,
      (S.universalRootDeficit_mem_Icc r x).1, ?_⟩
    have hBx := S.universalPartnerCommonMissingDeficit_ge_floor r p hpair hW hd hgap hell hN x
    dsimp only [L, E, H, U]
    nlinarith only [hx, hBx, hratio]
  have hmass : μ.real H = L + (D - μ.real U) := by dsimp only [L]; ring
  exact EmptySatE2.integrated_deficit_bounds H (S.universalRootDeficit r)
    (S.universalPartnerHoleMissingMass r p) (S.universalPartnerCommonMissingMass r p)
    hδ hL hE hEL (S.integrable_universalRootDeficit r).integrableOn hparts hbudget hmass
    (by linarith only [measureReal_nonneg (μ := μ) (s := U)])

/-- A genuinely large missing-H section yields an original whole atom
with its entire fiber in H, the exact old mass, constant deficit and no
common-region holes. All pointwise data are selected on one common AE event. -/
theorem empty_sat_exceptional_atom (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hholes : 0 < μ (S.universalPartnerHoleRegion r p)) :
    let H := S.universalPartnerHoleRegion r p
    let D := (1 - m - 4 * (c - m * d)) / (1 + m)
    let L := μ.real H + μ.real (S.universalPartnerCommonRegion r p) - D
    let E := D - S.originalAtomMass r
    E < L → (¬∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L) →
      ∃ (i : S.I) (di : ℝ), i ≠ r ∧ i ≠ p ∧
        (∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val}, z ∈ H) ∧
        L ≤ S.originalAtomMass i ∧ S.originalAtomMass i ≤ L + E ∧
        0 ≤ di ∧ di < (1 + m) / 2 ∧
        (∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val}, S.universalRootDeficit r z = di) ∧
        (∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val},
          S.universalPartnerCommonMissingMass r p z = 0) ∧
        S.originalAtomMass i * di ≤ (1 + m) * (E + (S.originalAtomMass i - L)) / 2 := by
  dsimp only
  intro hEL hlarge
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let D := (1 - m - 4 * (c - m * d)) / (1 + m)
  let L := μ.real H + μ.real U - D
  let E := D - S.originalAtomMass r
  let a := S.universalPartnerHoleMissingMass r p
  let k := S.universalPartnerCommonMissingMass r p
  let f := S.universalRootDeficit r
  let δ := 1 + m
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hell]
  have hratio : δ * D = 1 - m - 4 * (c - m * d) := by
    dsimp only [D, δ]
    exact mul_div_cancel₀ _ hδ.ne'
  have hAD := S.universal_atom_mass_le_saturated_deficit_ratio
    r p hpair hW hd hgap hell hN hholes
  have hE : 0 ≤ E := sub_nonneg.mpr hAD
  have hL : 0 < L := lt_of_le_of_lt hE hEL
  let : Countable S.I := S.hI.to_subtype
  have hrows : ∀ᵐ x ∂μ, ∀ i : S.I, S.ρ x = i.val →
      adjacencyKernel W x =ᵐ[μ] fun z => if 0 < i.val z then 1 else 0 := by
    apply ae_all_iff.mpr
    intro i
    exact (ae_restrict_iff' (S.hfibers i.val i.property).1).mp
      ((S.hfibers i.val i.property).2.2.2.rows.mono (fun _ hx => hx.2.1))
  have hex : ∃ x, L ≤ a x ∧ a x + k x ≤ L + E ∧
      δ * (L - a x) ≤ (L + E - 2 * a x - k x) * f x ∧
      (0 < k x → δ < f x) ∧
      (∀ i : S.I, S.ρ x = i.val → adjacencyKernel W x =ᵐ[μ]
        fun z => if 0 < i.val z then 1 else 0) ∧
      ∃ i : S.I, S.ρ x = i.val ∧
        (∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val}, z ∈ H) ∧ a x = S.originalAtomMass i ∧
        (∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val}, f z = f x) := by
    by_contra hn
    apply hlarge
    filter_upwards [S.ae_universalPartnerHole_missing_capacity r p hpair hW hd hgap hell hN,
      S.ae_universalPartnerHole_deficit_row r p hpair hW hd hgap hell hN,
      S.ae_universalPartnerHole_commonMissing_pos_deficit_gt r p hpair hW hd hgap hell hN,
      S.ae_universalPartnerHole_atom_of_missing_mass_pos r p hpair hW hd hgap hell,
      ae_restrict_of_ae hrows] with x hc hr hf ha hxrows
    by_contra hnot
    have hxL : L ≤ a x := le_of_not_gt hnot
    have hapos : 0 < a x := lt_of_lt_of_le hL hxL
    have hcap : a x + k x ≤ L + E := by
      dsimp only [L, E, H, U, a, k]
      nlinarith only [hc]
    have hrow : δ * (L - a x) ≤ (L + E - 2 * a x - k x) * f x := by
      have hBx := S.universalPartnerCommonMissingDeficit_ge_floor
        r p hpair hW hd hgap hell hN x
      dsimp only [L, E, H, U, a, k, f, δ]
      nlinarith only [hr, hBx, hratio]
    exact hn ⟨x, hxL, hcap, hrow, hf, hxrows, ha hapos⟩
  obtain ⟨x, hxL, hcap, hrow, hfloor, hxrows, i, hxi, hwhole, hmass, hconst⟩ := hex
  let di := f x
  let e := S.originalAtomMass i - L
  have he : 0 ≤ e := by dsimp only [e]; linarith only [hxL, hmass]
  have heE : e ≤ E := by
    have hk := S.universalPartnerCommonMissingMass_nonneg r p x
    dsimp only [e]
    change 0 ≤ k x at hk
    linarith only [hcap, hmass, hk]
  have hdi : 0 ≤ di := (S.universalRootDeficit_mem_Icc r x).1
  have hk : 0 ≤ k x := S.universalPartnerCommonMissingMass_nonneg r p x
  have hrow' : δ * (L - (L + e)) ≤ (L + E - 2 * (L + e) - k x) * di := by
    dsimp only [e, di]
    rw [hmass] at hrow
    nlinarith only [hrow]
  obtain ⟨hdiHalf, hkzero, hcredit⟩ :=
    EmptySatE2.exceptional_deficit_bounds hδ hEL he heE hk hdi hrow' hfloor
  have hki : ∀ᵐ z ∂μ.restrict {z | S.ρ z = i.val}, k z = 0 := by
    have hrowx := hxrows i hxi
    filter_upwards [(S.hfibers i.val i.property).2.2.2.rows] with z hz
    have heq : k z = k x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hz.2.1, ae_restrict_of_ae hrowx] with y hy hx
      rw [hy, hx]
    exact heq.trans hkzero
  obtain ⟨z, hz, hzH⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers i.val i.property).2.1.ne' hwhole
  have hir : i ≠ r := by
    intro hi
    exact hzH (Or.inl (Or.inl (hz.trans (congrArg Subtype.val hi))))
  have hip : i ≠ p := by
    intro hi
    exact hzH (Or.inl (Or.inr (hz.trans (congrArg Subtype.val hi))))
  refine ⟨i, di, hir, hip, hwhole, ?_, ?_, hdi, hdiHalf, hconst, hki, ?_⟩
  · linarith only [hxL, hmass]
  · dsimp only [e] at heE
    linarith only [heE]
  · dsimp only [e] at hcredit
    nlinarith only [hcredit]

/-- An original whole atom in H with no missing U mass has exactly its
own fiber and the saturated partner as its missing classes. This follows
from the product-AE geometry of the original graph. -/
theorem empty_sat_exceptional_private_row (S : SelectedHighLowStructure W m)
    (r p i : S.I) (hpair : S.IsSaturatedAtomPair r p) (hir : i ≠ r)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hwhole : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.universalPartnerHoleRegion r p)
    (hkzero : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      S.universalPartnerCommonMissingMass r p x = 0) :
    ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val → adjacencyKernel W q.1 q.2 =
      if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1 := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let C := {x | S.ρ x = i.val}
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  have hC : MeasurableSet C := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hU : MeasurableSet U := S.measurableSet_universalPartnerCommonRegion r p
  have hGm : Measurable (Function.uncurry (adjacencyKernel W)) :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable
  have hUrows : ∀ᵐ x ∂μ.restrict C, ∀ᵐ z ∂μ.restrict U, adjacencyKernel W x z = 1 := by
    filter_upwards [hkzero] with x hx
    have hmeas : Measurable (fun z => 1 - adjacencyKernel W x z) :=
      measurable_const.sub (hGm.comp (measurable_const.prodMk measurable_id))
    have hnonneg : ∀ z, 0 ≤ 1 - adjacencyKernel W x z := by
      intro z
      exact sub_nonneg.mpr (adjacency_moment_mem W (x, z)).2
    have hi : IntegrableOn (fun z => 1 - adjacencyKernel W x z) U μ := by
      apply Integrable.of_bound hmeas.aestronglyMeasurable 1
      exact Eventually.of_forall (fun z => by
        have hg := adjacency_moment_mem W (x, z)
        change 0 ≤ adjacencyKernel W x z ∧ adjacencyKernel W x z ≤ 1 at hg
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
        linarith only [hg.1])
    change (∫ z in U, 1 - adjacencyKernel W x z ∂μ) = 0 at hx
    have heq := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall hnonneg) hi).mp hx
    filter_upwards [heq] with z hz
    change 1 - adjacencyKernel W x z = 0 at hz
    linarith only [hz]
  have hUglobal : ∀ᵐ x ∂μ.restrict C, ∀ᵐ z ∂μ,
      z ∈ U → adjacencyKernel W x z = 1 :=
    hUrows.mono (fun _ hx => (ae_restrict_iff' hU).mp hx)
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have hroot : ∀ᵐ q ∂μ.prod μ, q.1 ∉ I → q.2 ∈ I → adjacencyKernel W q.1 q.2 = 1 := by
    filter_upwards [hswap.ae (S.neutral_atom_adjacency r hW hd hgap hN),
      adjacencyKernel_symm W] with q hq hs hx hz
    have he := hq hz
    change adjacencyKernel W q.2 q.1 = (if S.ρ q.1 = r.val then 0 else 1) at he
    rw [hs, he]
    simp only [show S.ρ q.1 ≠ r.val from hx, ite_false]
  have hpartner : ∀ᵐ q ∂μ.prod μ, q.1 ∈ H → q.2 ∈ P →
      adjacencyKernel W q.1 q.2 = 0 := by
    filter_upwards [hswap.ae (S.ae_root_adjacency p hW hd hgap),
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support] with q hq hmoment hx hz
    have hn : q.1 ∉ S.rootNeighborhood p := fun hn => hx (Or.inr hn)
    have hf : PhysicalRepresentative.adjacency W m q.2 q.1 = false :=
      Bool.eq_false_iff.mpr (fun ha => hn ((hq hz).mp ha))
    change adjacencyKernel W q.1 q.2 =
      (if PhysicalRepresentative.adjacency W m q.1 q.2 = true then (1 : ℝ) else 0) at hmoment
    rw [PhysicalRepresentative.adjacency_symm W m q.1 q.2, hf] at hmoment
    simpa only [Bool.false_eq_true, ite_false] using hmoment
  have hwholeGlobal : ∀ᵐ z ∂μ, z ∈ C → z ∈ H := (ae_restrict_iff' hC).mp hwhole
  have hsections : ∀ᵐ x ∂μ.restrict C, ∀ᵐ z ∂μ,
      adjacencyKernel W x z = if S.ρ z = i.val ∨ S.ρ z = p.val then 0 else 1 := by
    filter_upwards [hwhole, ae_restrict_mem hC, hUglobal,
      ae_restrict_of_ae (Measure.ae_ae_of_ae_prod
        (S.ae_universalPartnerHole_missing_iff_sameAtom r p hpair hW hd hgap hell)),
      ae_restrict_of_ae (Measure.ae_ae_of_ae_prod
        (hW.strict_gap_structure hd hgap).strict_support),
      ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hroot),
      ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpartner)]
      with x hxH hxi hxU hxmissing hxsupport hxroot hxpartner
    have hxnotr : x ∉ I := fun hx => hir (Subtype.ext (hxi.symm.trans hx))
    filter_upwards [hxU, hxmissing, hxsupport, hxroot, hxpartner, hwholeGlobal]
      with z hzU hzmissing hzsupport hzroot hzpartner hzwhole
    by_cases hzp : S.ρ z = p.val
    · rw [ite_eq_left (Or.inr hzp)]
      exact hzpartner hxH hzp
    by_cases hzi : S.ρ z = i.val
    · rw [ite_eq_left (Or.inl hzi)]
      apply (hzmissing hxH (hzwhole hzi)).mpr
      exact ⟨hxi.trans hzi.symm, by rw [hxi]; exact i.property⟩
    rw [ite_eq_right (not_or.mpr ⟨hzi, hzp⟩)]
    by_cases hzI : z ∈ I
    · exact hzroot hxnotr hzI
    by_cases hzH : z ∈ H
    · have hnzero : adjacencyKernel W x z ≠ 0 := by
        intro hz
        have hsame := (hzmissing hxH hzH).mp hz
        exact hzi (hsame.1.symm.trans hxi)
      change adjacencyKernel W x z = if 0 < shiftedKernel W m x z then 1 else 0 at hzsupport
      by_cases hp : 0 < shiftedKernel W m x z
      · simpa only [ite_eq_left hp] using hzsupport
      · have hz : adjacencyKernel W x z = 0 := by simpa only [ite_eq_right hp] using hzsupport
        exact False.elim (hnzero hz)
    · have hzUmem : z ∈ U := by
        intro h
        rcases h with (hr | hp) | hh
        · exact hzI hr
        · exact hzp hp
        · exact hzH hh
      exact hzU hzUmem
  have htarget : Measurable (fun q : Ω × Ω =>
      if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then (0 : ℝ) else 1) :=
    Measurable.ite ((hC.union hP).preimage measurable_snd) measurable_const measurable_const
  have hprod : ∀ᵐ q ∂(μ.restrict C).prod μ, adjacencyKernel W q.1 q.2 =
      if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hGm htarget)).mpr hsections
  have hrestrict : (μ.restrict C).prod μ = (μ.prod μ).restrict (C ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hrestrict] at hprod
  have hglobal := (ae_restrict_iff' (hC.prod MeasurableSet.univ)).mp hprod
  exact hglobal.mono (fun q hq hx => hq ⟨hx, mem_univ _⟩)

/-- Every actual restriction outside the same neutral original whole head
has the optimized rescaled-head support price. Its scalar tests and joined
head are derived from the original model; no restriction stationarity is used. -/
theorem universal_restriction_support_price (S : SelectedHighLowStructure W m)
    (r : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (O : Set Ω) (hO : MeasurableSet O) (hdis : Disjoint {x | S.ρ x = r.val} O) :
    let HI := (∫ p, PhysicalRepresentative.charge W m p.1 p.2
      ∂(μ.restrict {x | S.ρ x = r.val}).prod (μ.restrict O)) / μ.real {x | S.ρ x = r.val}
    let Q := ∫ p, (1 - if PhysicalRepresentative.adjacency W m p.1 p.2 = true
      then (1 : ℝ) else 0) ∂(μ.restrict O).prod (μ.restrict O)
    FiniteCappedSamplingCost.physicalObjective (μ.restrict O)
      (PhysicalRepresentative.charge W m) ≤
      (μ.real O) ^ 2 / 48 + Q / 2 - (12 / 25) * max (HI - μ.real O / 24) 0 ^ 2 := by
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hphysical := S.neutral_atom_physical_adjacency r hW hd hgap hN
  have hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I),
      PhysicalRepresentative.adjacency W m p.1 p.2 = false := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) hphysical,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hI)] with p hp hx hy
    exact Bool.eq_false_iff.mpr (fun he => (hp hx).mp he hy)
  have hjoin : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict O),
      PhysicalRepresentative.adjacency W m p.1 p.2 = true := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) hphysical,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hO)] with p hp hx hy
    exact (hp hx).mpr (fun he => Set.disjoint_left.mp hdis he hy)
  exact FiniteCappedSamplingCost.independent_head_support_optimized
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.adjacency_symm W m)
    (PhysicalRepresentative.measurable_adjacency W m) (PhysicalRepresentative.charge W m)
    (PhysicalRepresentative.measurable_charge W m) 3
    (fun p => by simpa only [Real.norm_eq_abs] using
      PhysicalRepresentative.charge_bound W m p.1 p.2)
    (Eventually.of_forall (fun p => PhysicalRepresentative.charge_symm W m p.1 p.2))
    (Eventually.of_forall (fun p hp =>
      PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 hp))
    (PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic)
    I O hI hO (S.hfibers r.val r.property).2.1 hdis hind hjoin

/-- The actual deleted-partner support price retains the full original
hole debit. Neither partner universality nor restriction stationarity is assumed. -/
theorem empty_sat_deleted_partner_support (S : SelectedHighLowStructure W m)
    (r p : S.I) (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let s := μ.real (S.universalPartnerHoleRegion r p)
    let U := A + b
    let v := A - b
    let T := (1 + m) * U - 2 * (2 * (c - m * d) + m)
    (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T -
      (1 - U) ^ 2 / 12 + (12 / 25) * max ((1 - m) * v - T - (1 - U) / 12) 0 ^ 2 +
        4 * (1 + m) * b * s ≤ 0 := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let O := (I ∪ P)ᶜ
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let U := A + b
  let v := A - b
  let T := (1 + m) * U - 2 * (2 * (c - m * d) + m)
  let HI := (∫ q, PhysicalRepresentative.charge W m q.1 q.2
    ∂(μ.restrict I).prod (μ.restrict O)) / A
  let CO := FiniteCappedSamplingCost.physicalObjective (μ.restrict O)
    (PhysicalRepresentative.charge W m)
  let Q := ∫ q, (1 - if PhysicalRepresentative.adjacency W m q.1 q.2 = true
    then (1 : ℝ) else 0) ∂(μ.restrict O).prod (μ.restrict O)
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hO : MeasurableSet O := (hI.union hP).compl
  obtain ⟨hHI, hCO, hQ, hmass⟩ := S.empty_sat_deleted_partner_inventory r p hpair hW hd hgap hN
  change HI = 2 * (c - m * d) + m - b - m * A at hHI
  change CO = c - (A + b) * (2 * (c - m * d)) -
    m * (A + b - A ^ 2 - b ^ 2 - b * s) + A * b at hCO
  change Q = 1 - 2 * d - A ^ 2 - b ^ 2 - 2 * b * s at hQ
  change μ.real O = 1 - A - b at hmass
  have hdis : Disjoint I O := disjoint_left.mpr (fun _ hx hy => hy (Or.inl hx))
  have hsupport := S.universal_restriction_support_price r hW hd hgap hN O hO hdis
  change CO ≤ (μ.real O) ^ 2 / 48 + Q / 2 - (12 / 25) *
    max (HI - μ.real O / 24) 0 ^ 2 at hsupport
  have hmass' : μ.real O = 1 - U := by dsimp only [U]; linarith only [hmass]
  rw [hmass'] at hsupport
  have henergy : 4 * (CO - Q / 2) =
      (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T +
        4 * (1 + m) * b * s := by
    rw [hCO, hQ]
    dsimp only [U, v, T]
    ring
  have harg : (1 - m) * v - T - (1 - U) / 12 = 2 * (HI - (1 - U) / 24) := by
    rw [hHI]
    dsimp only [U, v, T]
    ring
  have hmax : max ((1 - m) * v - T - (1 - U) / 12) 0 =
      2 * max (HI - (1 - U) / 24) 0 := by
    rw [harg]
    by_cases hx : 0 ≤ HI - (1 - U) / 24
    · rw [max_eq_left hx, max_eq_left (mul_nonneg (by norm_num) hx)]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_right (by linarith only [le_of_not_ge hx])]
      ring
  change (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T -
    (1 - U) ^ 2 / 12 + (12 / 25) * max ((1 - m) * v - T - (1 - U) / 12) 0 ^ 2 +
      4 * (1 + m) * b * s ≤ 0
  rw [hmax]
  nlinarith only [hsupport, henergy]

/-- The exceptional atom is priced by the actual three-head restriction.
The favorable original hole debit is dropped only after whole-fiber
containment proves its sign. All remaining signed terms are retained. -/
theorem empty_sat_exceptional_support (S : SelectedHighLowStructure W m)
    (r p i : S.I) (hpair : S.IsSaturatedAtomPair r p) (hir : i ≠ r) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hwhole : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.universalPartnerHoleRegion r p)
    (di : ℝ) (hdef : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      S.universalRootDeficit r x = di)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val → adjacencyKernel W q.1 q.2 =
      if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    let A := S.originalAtomMass r
    let b := S.originalAtomMass p
    let a := S.originalAtomMass i
    let U := A + a + b
    let v := A - a - b
    let T := (1 + m) * U - 2 * (2 * (c - m * d) + m)
    let Z := a * di
    (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T -
      (1 - U) ^ 2 / 12 + (12 / 25) * max ((1 - m) * v - T - (1 - U) / 12 + 2 * Z) 0 ^ 2 -
        4 * A * Z ≤ 0 := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = p.val}
  let C := {x | S.ρ x = i.val}
  let K := (I ∪ P ∪ C)ᶜ
  let A := S.originalAtomMass r
  let b := S.originalAtomMass p
  let a := S.originalAtomMass i
  let s := μ.real (S.universalPartnerHoleRegion r p)
  let U := A + a + b
  let v := A - a - b
  let T := (1 + m) * U - 2 * (2 * (c - m * d) + m)
  let Z := a * di
  let HI := (∫ q, PhysicalRepresentative.charge W m q.1 q.2
    ∂(μ.restrict I).prod (μ.restrict K)) / A
  let CK := FiniteCappedSamplingCost.physicalObjective (μ.restrict K)
    (PhysicalRepresentative.charge W m)
  let Q := ∫ q, (1 - if PhysicalRepresentative.adjacency W m q.1 q.2 = true
    then (1 : ℝ) else 0) ∂(μ.restrict K).prod (μ.restrict K)
  obtain ⟨hHI, hCK, hQ, hmass⟩ :=
    S.empty_sat_exceptional_inventory r p i hpair hir hip hW hd hgap hN di hdef hprivate
  change HI = 2 * (c - m * d) + m - a - b - m * A + a * di at hHI
  change CK = c - (A + b + a) * (2 * (c - m * d)) -
    m * (A + b + a - A ^ 2 - b ^ 2 - b * s - a * (a + b)) +
      A * b + A * a * (1 - di) at hCK
  change Q = 1 - 2 * d - A ^ 2 - b ^ 2 - a ^ 2 - 2 * b * s at hQ
  change μ.real K = 1 - A - b - a at hmass
  have hK : MeasurableSet K :=
    (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).union
      (S.hfibers i.val i.property).1).compl
  have hdis : Disjoint I K := disjoint_left.mpr (fun _ hx hy => hy (Or.inl (Or.inl hx)))
  have hsupport := S.universal_restriction_support_price r hW hd hgap hN K hK hdis
  change CK ≤ (μ.real K) ^ 2 / 48 + Q / 2 - (12 / 25) *
    max (HI - μ.real K / 24) 0 ^ 2 at hsupport
  have hmass' : μ.real K = 1 - U := by dsimp only [U]; linarith only [hmass]
  rw [hmass'] at hsupport
  have henergy : 4 * (CK - Q / 2) =
      (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T +
        4 * (1 + m) * b * (s - a) - 4 * A * Z := by
    rw [hCK, hQ]
    dsimp only [U, v, T, Z]
    ring
  have harg : (1 - m) * v - T - (1 - U) / 12 + 2 * Z =
      2 * (HI - (1 - U) / 24) := by
    rw [hHI]
    dsimp only [U, v, T, Z]
    ring
  have hmax : max ((1 - m) * v - T - (1 - U) / 12 + 2 * Z) 0 =
      2 * max (HI - (1 - U) / 24) 0 := by
    rw [harg]
    by_cases hx : 0 ≤ HI - (1 - U) / 24
    · rw [max_eq_left hx, max_eq_left (mul_nonneg (by norm_num) hx)]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_right (by linarith only [le_of_not_ge hx])]
      ring
  have has : a ≤ s := ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono_ae ((ae_restrict_iff' (S.hfibers i.val i.property).1).mp hwhole))
  have hdebit : 0 ≤ 4 * (1 + m) * b * (s - a) := by
    have hδ : 0 ≤ 1 + m := by linarith only [hell]
    have hb : 0 ≤ b := ENNReal.toReal_nonneg
    have hsa : 0 ≤ s - a := sub_nonneg.mpr has
    positivity
  change (1 + m) * (U - 2 * (1 - 2 * d)) + 2 * m * v ^ 2 + (2 * U - 1) * T -
    (1 - U) ^ 2 / 12 + (12 / 25) * max ((1 - m) * v - T - (1 - U) / 12 + 2 * Z) 0 ^ 2 -
      4 * A * Z ≤ 0
  rw [hmax]
  nlinarith only [hsupport, henergy, hdebit]

end Erdos1017.CappedModel.SelectedHighLowStructure
