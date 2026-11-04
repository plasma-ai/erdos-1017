module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PeakThird
public import Erdos1017.SelectedModel.SelectedBodyEnergy
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyCubic
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards
public import Erdos1017.Exclusions.E2.Upper.UpperE2ParameterGuards
public import Erdos1017.Exclusions.Common.Physical.PhysicalTriangleExposure
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2UniversalPrimal

/-!
# Bad region of the universal root

`universalUpperE2BadRegion` is the two-head exterior where the universal-root
physical star falls below the upper-`E₂` signed insertion threshold; the bad set
lies in the partner's common region, and the high partner hole joins every bad
vertex.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

attribute [local instance] Classical.propDecidable

private theorem universal_star_capacity_at_delta {A ell u v : ℝ}
    (hA : 1 / 3 ≤ A) (hell : 0 ≤ ell) (hu : u ≤ 1 - ell) (hv : v ≤ 1) :
    A * (u + v - ell) + (1 - 2 * A) *
      (max (1 - ell - v) 0 + (1 - ell - u)) ≤ 2 * A * (1 - ell) := by
  have hcoef : 0 ≤ 3 * A - 1 := by linarith
  have hA0 : 0 ≤ A := by linarith
  by_cases h : 0 ≤ 1 - ell - v
  · rw [max_eq_left h]
    have ht := mul_nonneg hcoef (show 0 ≤ 2 * (1 - ell) - u - v by linarith)
    nlinarith [mul_nonneg hA0 hell]
  · rw [max_eq_right (le_of_not_ge h)]
    have ht := mul_nonneg hcoef (show 0 ≤ 1 - ell - u by linarith)
    have hv' := mul_nonneg hA0 (show 0 ≤ 1 - v by linarith)
    nlinarith

private theorem universal_star_capacity_above_delta {A ell u v : ℝ}
    (hA : 1 / 3 ≤ A) (hAhalf : A ≤ 1 / 2) (hell : 0 ≤ ell)
    (hu : 1 - ell ≤ u) (hv : v ≤ 1) :
    A * (u + v - ell) + (1 - 2 * A) *
      (max (1 - ell - v) 0 + max (1 - ell - u) 0) ≤
        A * (u + 1 - ell) := by
  rw [max_eq_right (by linarith : 1 - ell - u ≤ 0)]
  have hcoef : 0 ≤ 3 * A - 1 := by linarith
  have hcoef' : 0 ≤ 1 - 2 * A := by linarith
  have hA0 : 0 ≤ A := by linarith
  by_cases h : 0 ≤ 1 - ell - v
  · rw [max_eq_left h]
    have ht := mul_nonneg hcoef (show 0 ≤ 1 - ell - v by linarith)
    have ht' := mul_nonneg hcoef' (show 0 ≤ u - (1 - ell) by linarith)
    nlinarith [mul_nonneg hA0 hell]
  · rw [max_eq_right (le_of_not_ge h)]
    have ht := mul_nonneg hcoef' (show 0 ≤ u - (1 - ell) by linarith)
    have hv' := mul_nonneg hA0 (show 0 ≤ 1 - v by linarith)
    nlinarith

private theorem universal_majorant_cover (ell u v : ℝ)
    (b0 b1 b2 : Bool) (i : Prop) [Decidable i]
    (h0 : b0 = false ↔ i) (h1 : i → b1 = true) (h2 : i → b2 = true)
    (hell : 1 / 2 ≤ ell) :
    TriangleInsertion.majorant ell (u + v) (1 - v) (1 - u) b0 b1 b2 ≤
      (if i then u + v - ell else 0) +
        (if b1 = false then max (1 - ell - v) 0 else 0) +
        (if b2 = false then max (1 - ell - u) 0 else 0) := by
  by_cases hi : i
  · have hb0 := h0.mpr hi
    simp [TriangleInsertion.majorant, hi, hb0, h1 hi, h2 hi]
  · have hb0 : b0 = true := by cases b0 <;> simp_all
    cases b1 <;> cases b2 <;>
      simp only [TriangleInsertion.majorant, hb0, hi, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte, zero_add, add_zero]
    all_goals linarith [le_max_left (1 - ell - v) 0,
      le_max_right (1 - ell - v) 0,
      le_max_left (1 - ell - u) 0, le_max_right (1 - ell - u) 0]

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m c : ℝ}

/-- The two-head exterior on which the universal-root physical star
falls below the upper-E2 signed insertion threshold. -/
def universalUpperE2BadRegion (S : SelectedHighLowStructure W m) (r p : S.I)
    (d c : ℝ) : Set Ω :=
  (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ) ∩
    {x | S.rootChargeRow r x <
      3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
theorem measurableSet_universalUpperE2BadRegion (S : SelectedHighLowStructure W m)
    (r p : S.I) (d c : ℝ) : MeasurableSet (S.universalUpperE2BadRegion r p d c) :=
  (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl).inter
    (measurableSet_lt (S.measurable_rootChargeRow r) measurable_const)

/-- The actual universal common peak has the upper-E2 mass and shifted-row
margin required by the original signed triangle argument. -/
theorem universal_upperE2_initial_guards
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (huniv : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = r.val then 0 else 1)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = r.val}) :
    1 / 3 < S.originalAtomMass r ∧ S.originalAtomMass r < 2 / 5 ∧
      2 * S.originalAtomMass r * (1 + m) < 3 * (2 * (c - m * d) + m) := by
  let A := S.originalAtomMass r
  let γ := 2 * (c - m * d) + m
  have hmass := UpperE2Parameter.missingMass_mem hq
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    constructor <;> linarith [hmass.1, hmass.2]
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) :=
    ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨hm, hell, hfloor⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  obtain ⟨hΔ, i, hi, _, hpi, _, _, _⟩ :=
    S.exists_original_upper_e2_peak_gt_third hW hq hdq hvalue hderiv hgap hglobal
  have hir : i = r := (hpi S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst i
  have hA : 1 / 3 < A := hi
  have hN := S.universal_atom_neutral r hW hd hgap huniv
  have hbody := hW.bodyPositiveEnergy_eq_physicalBody hd hgap
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1
  have hphysical : 0 < ∫ z : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        {x | S.ρ x = r.val} z.1 z.2) ^ 2 ∂μ.prod μ := by
    rw [hbody] at hpositive
    exact hpositive
  have htrace := S.universal_positive_body_trace r hW hd hgap hN hphysical
  have hAlt : A < 2 / 5 := by
    have hγpos : 0 < γ := (LowerE2Scalar.contact_gapFloor_pos hq'.1).trans hfloor
    have hmissing : 1 - 2 * d = LowerE2Scalar.missingMass q := by rw [hdq]; ring
    have hγnonneg : 0 ≤ 2 * A * γ := mul_nonneg (by linarith [hA]) (by linarith)
    have hγsq : 0 ≤ γ ^ 2 := sq_nonneg γ
    change 3 * A ^ 2 + 2 * A * γ + γ ^ 2 ≤ 2 * (1 - 2 * d) at htrace
    rw [hmissing] at htrace
    by_contra hn
    have hAge : 2 / 5 ≤ A := le_of_not_gt hn
    have hAsq : (2 / 5 : ℝ) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hAge 2
    nlinarith [hmass.2]
  have hδpos : 0 < 1 + m := by linarith [hell.2]
  have hδbound : 1 + m < 1 / 5 := by
    rw [hm]
    linarith [UpperE2Parameter.multiplier_mem hq |>.1]
  have hprod : A * (1 + m) < (2 / 5 : ℝ) * (1 / 5) := by
    calc
      A * (1 + m) < (2 / 5 : ℝ) * (1 + m) :=
        mul_lt_mul_of_pos_right hAlt hδpos
      _ < (2 / 5 : ℝ) * (1 / 5) :=
        mul_lt_mul_of_pos_left hδbound (by norm_num)
  have hγ : (7 / 122 : ℝ) < γ :=
    (UpperE2Parameter.gapFloor_ge hq).trans_lt hfloor
  exact ⟨hA, hAlt, by dsimp [A, γ] at *; linarith⟩

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Integrating the genuine insertion inequality against flat shifted
rows forces the first universal-root star above the missing-price delta.
The signed root-region term is retained exactly. -/
private theorem first_star_gt_delta_of_insertion_and_capacity
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (B : ℝ) (hbound : ∀ p, |Y p| ≤ B)
    (hcap : ∀ p, Y p ≤ 1) (ell ν : ℝ) (hell : ell ∈ Icc (1 / 2 : ℝ) 1)
    (v : Fin 3 → Ω) (I : Set Ω) (hI : MeasurableSet I)
    (hA : 1 / 3 ≤ μ.real I)
    (hmargin : 2 * μ.real I * (1 - ell) < 3 * (ν - ell))
    (hold : Y (v 0, v 1) + Y (v 0, v 2) + Y (v 1, v 2) = 1)
    (hroot : ∀ᵐ z ∂μ, G (z, v 0) = false ↔ z ∈ I)
    (h1 : ∀ᵐ z ∂μ, z ∈ I → G (z, v 1) = true)
    (h2 : ∀ᵐ z ∂μ, z ∈ I → G (z, v 2) = true)
    (hmean : ∀ i : Fin 3, (∫ z, Y (z, v i) +
      ell * (if G (z, v i) then 1 else 0) ∂μ) = ν)
    (hmissing1 : μ.real {z | G (z, v 1) = false} ≤ 1 - 2 * μ.real I)
    (hmissing2 : μ.real {z | G (z, v 2) = false} ≤ 1 - 2 * μ.real I)
    (hinsertion : ∀ᵐ z ∂μ,
      Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
        ell * ((if G (z, v 0) then 0 else 1) + (if G (z, v 1) then 0 else 1) +
          (if G (z, v 2) then 0 else 1)) ≤
        TriangleInsertion.majorant ell (Y (v 0, v 1) + Y (v 0, v 2))
          (Y (v 0, v 1) + Y (v 1, v 2)) (Y (v 0, v 2) + Y (v 1, v 2))
          (G (z, v 0)) (G (z, v 1)) (G (z, v 2))) :
    1 - ell < Y (v 0, v 1) := by
  classical
  by_contra hpos
  let u := Y (v 0, v 1)
  let w := Y (v 0, v 2)
  have hu : u ≤ 1 - ell := le_of_not_gt hpos
  have hell0 : 0 ≤ ell := by linarith [hell.1]
  let F1 := {z | G (z, v 1) = false}
  let F2 := {z | G (z, v 2) = false}
  have hF1 : MeasurableSet F1 := (hG.comp (measurable_id.prodMk measurable_const))
    (measurableSet_singleton false)
  have hF2 : MeasurableSet F2 := (hG.comp (measurable_id.prodMk measurable_const))
    (measurableSet_singleton false)
  let L := fun z => Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
    ell * ((if G (z, v 0) then 0 else 1) + (if G (z, v 1) then 0 else 1) +
      (if G (z, v 2) then 0 else 1))
  let R := fun z => I.indicator (fun _ => u + w - ell) z +
    F1.indicator (fun _ => max (1 - ell - w) 0) z +
      F2.indicator (fun _ => 1 - ell - u) z
  have hle : L ≤ᵐ[μ] R := by
    filter_upwards [hinsertion, hroot, h1, h2] with z hi hr h1 h2
    have hs1 : Y (v 0, v 1) + Y (v 1, v 2) = 1 - w := by dsimp [w]; linarith
    have hs2 : Y (v 0, v 2) + Y (v 1, v 2) = 1 - u := by dsimp [u]; linarith
    rw [hs1, hs2] at hi
    have hm := universal_majorant_cover ell u w
      (G (z, v 0)) (G (z, v 1)) (G (z, v 2)) (z ∈ I) hr h1 h2 hell.1
    rw [max_eq_left (show 0 ≤ 1 - ell - u by linarith)] at hm
    have hh := hi.trans hm
    simpa only [L, R, u, w, F1, F2, Set.indicator, mem_ofPred_eq] using hh
  let f := fun i : Fin 3 => fun z => Y (z, v i) + ell * (if G (z, v i) then 1 else 0)
  have hf (i : Fin 3) : Integrable (f i) μ := by
    have hy : Integrable (fun z => Y (z, v i)) μ := Integrable.of_bound
      (hY.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
      (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound (z, v i)))
    have hg : Integrable (fun z => if G (z, v i) then (1 : ℝ) else 0) μ :=
      Integrable.of_bound
        (Measurable.ite ((hG.comp (measurable_id.prodMk measurable_const))
          (measurableSet_singleton true)) measurable_const measurable_const).aestronglyMeasurable
        1 (Eventually.of_forall (fun z => by cases G (z, v i) <;> norm_num))
    exact hy.add (hg.const_mul ell)
  have hL : L = fun z => f 0 z + f 1 z + f 2 z - 3 * ell := by
    funext z
    cases h0 : G (z, v 0) <;> cases h1 : G (z, v 1) <;> cases h2 : G (z, v 2) <;>
      simp [L, f, h0, h1, h2] <;> ring
  have hiL : Integrable L μ := by
    rw [hL]
    exact (((hf 0).add (hf 1)).add (hf 2)).sub (integrable_const (3 * ell))
  have hmeanL : (∫ z, L z ∂μ) = 3 * (ν - ell) := by
    rw [hL, integral_sub, integral_add, integral_add]
    change (∫ z, f 0 z ∂μ) + (∫ z, f 1 z ∂μ) + (∫ z, f 2 z ∂μ) - _ = _
    rw [show (∫ z, f 0 z ∂μ) = ν from hmean 0,
      show (∫ z, f 1 z ∂μ) = ν from hmean 1,
      show (∫ z, f 2 z ∂μ) = ν from hmean 2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
    all_goals first
      | exact integrable_const _
      | exact hf 0
      | exact hf 1
      | exact hf 2
      | exact (hf 0).add (hf 1)
      | exact ((hf 0).add (hf 1)).add (hf 2)
  have hi0 : Integrable (I.indicator (fun _ : Ω => u + w - ell)) μ :=
    (integrable_const _).indicator hI
  have hi1 : Integrable (F1.indicator (fun _ : Ω => max (1 - ell - w) 0)) μ :=
    (integrable_const _).indicator hF1
  have hi2 : Integrable (F2.indicator (fun _ : Ω => 1 - ell - u)) μ :=
    (integrable_const _).indicator hF2
  have hiR : Integrable R μ := (hi0.add hi1).add hi2
  have hmeanR : (∫ z, R z ∂μ) = μ.real I * (u + w - ell) +
      μ.real F1 * max (1 - ell - w) 0 + μ.real F2 * (1 - ell - u) := by
    rw [show R = fun z => I.indicator (fun _ => u + w - ell) z +
      F1.indicator (fun _ => max (1 - ell - w) 0) z +
      F2.indicator (fun _ => 1 - ell - u) z from rfl,
      integral_add, integral_add,
      integral_indicator hI, integral_indicator hF1, integral_indicator hF2]
    simp only [setIntegral_const, smul_eq_mul]
    all_goals first
      | exact hi0
      | exact hi1
      | exact hi2
      | exact hi0.add hi1
  have hh := integral_mono_ae hiL hiR hle
  rw [hmeanL, hmeanR] at hh
  have hm1 := mul_le_mul_of_nonneg_right hmissing1 (le_max_right (1 - ell - w) 0)
  have hm2 := mul_le_mul_of_nonneg_right hmissing2 (show 0 ≤ 1 - ell - u by linarith [hell.2])
  have hscalar := universal_star_capacity_at_delta hA hell0 hu (hcap (v 0, v 2))
  change 3 * (ν - ell) ≤ μ.real I * (u + w - ell) +
    μ.real {z | G (z, v 1) = false} * max (1 - ell - w) 0 +
    μ.real {z | G (z, v 2) = false} * (1 - ell - u) at hh
  change μ.real I * (u + w - ell) + (1 - 2 * μ.real I) *
    (max (1 - ell - w) 0 + (1 - ell - u)) ≤ 2 * μ.real I * (1 - ell) at hscalar
  nlinarith


omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem first_star_integral_bound_above_delta
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (B : ℝ) (hbound : ∀ p, |Y p| ≤ B)
    (hcap : ∀ p, Y p ≤ 1) (ell ν : ℝ) (hell : ell ∈ Icc (1 / 2 : ℝ) 1)
    (v : Fin 3 → Ω) (I : Set Ω) (hI : MeasurableSet I)
    (hA : 1 / 3 ≤ μ.real I) (hAhalf : μ.real I ≤ 1 / 2)
    (hold : Y (v 0, v 1) + Y (v 0, v 2) + Y (v 1, v 2) = 1)
    (hroot : ∀ᵐ z ∂μ, G (z, v 0) = false ↔ z ∈ I)
    (h1 : ∀ᵐ z ∂μ, z ∈ I → G (z, v 1) = true)
    (h2 : ∀ᵐ z ∂μ, z ∈ I → G (z, v 2) = true)
    (hmean : ∀ i : Fin 3, (∫ z, Y (z, v i) +
      ell * (if G (z, v i) then 1 else 0) ∂μ) = ν)
    (hmissing1 : μ.real {z | G (z, v 1) = false} ≤ 1 - 2 * μ.real I)
    (hmissing2 : μ.real {z | G (z, v 2) = false} ≤ 1 - 2 * μ.real I)
    (hinsertion : ∀ᵐ z ∂μ,
      Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
        ell * ((if G (z, v 0) then 0 else 1) + (if G (z, v 1) then 0 else 1) +
          (if G (z, v 2) then 0 else 1)) ≤
        TriangleInsertion.majorant ell (Y (v 0, v 1) + Y (v 0, v 2))
          (Y (v 0, v 1) + Y (v 1, v 2)) (Y (v 0, v 2) + Y (v 1, v 2))
          (G (z, v 0)) (G (z, v 1)) (G (z, v 2)))
    (hu : 1 - ell ≤ Y (v 0, v 1)) :
    3 * (ν - ell) ≤ μ.real I * (Y (v 0, v 1) + 1 - ell) := by
  classical
  let u := Y (v 0, v 1)
  let w := Y (v 0, v 2)
  let F1 := {z | G (z, v 1) = false}
  let F2 := {z | G (z, v 2) = false}
  have hF1 : MeasurableSet F1 := (hG.comp (measurable_id.prodMk measurable_const))
    (measurableSet_singleton false)
  have hF2 : MeasurableSet F2 := (hG.comp (measurable_id.prodMk measurable_const))
    (measurableSet_singleton false)
  let L := fun z => Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
    ell * ((if G (z, v 0) then 0 else 1) + (if G (z, v 1) then 0 else 1) +
      (if G (z, v 2) then 0 else 1))
  let R := fun z => I.indicator (fun _ => u + w - ell) z +
    F1.indicator (fun _ => max (1 - ell - w) 0) z +
      F2.indicator (fun _ => max (1 - ell - u) 0) z
  have hle : L ≤ᵐ[μ] R := by
    filter_upwards [hinsertion, hroot, h1, h2] with z hi hr h1 h2
    have hs1 : Y (v 0, v 1) + Y (v 1, v 2) = 1 - w := by dsimp [w]; linarith
    have hs2 : Y (v 0, v 2) + Y (v 1, v 2) = 1 - u := by dsimp [u]; linarith
    rw [hs1, hs2] at hi
    have hm := universal_majorant_cover ell u w
      (G (z, v 0)) (G (z, v 1)) (G (z, v 2)) (z ∈ I) hr h1 h2 hell.1
    have hh := hi.trans hm
    simpa only [L, R, u, w, F1, F2, Set.indicator, mem_ofPred_eq] using hh
  let f := fun i : Fin 3 => fun z => Y (z, v i) + ell * (if G (z, v i) then 1 else 0)
  have hf (i : Fin 3) : Integrable (f i) μ := by
    have hy : Integrable (fun z => Y (z, v i)) μ := Integrable.of_bound
      (hY.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
      (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound (z, v i)))
    have hg : Integrable (fun z => if G (z, v i) then (1 : ℝ) else 0) μ :=
      Integrable.of_bound
        (Measurable.ite ((hG.comp (measurable_id.prodMk measurable_const))
          (measurableSet_singleton true)) measurable_const measurable_const).aestronglyMeasurable
        1 (Eventually.of_forall (fun z => by cases G (z, v i) <;> norm_num))
    exact hy.add (hg.const_mul ell)
  have hL : L = fun z => f 0 z + f 1 z + f 2 z - 3 * ell := by
    funext z
    cases h0 : G (z, v 0) <;> cases h1 : G (z, v 1) <;> cases h2 : G (z, v 2) <;>
      simp [L, f, h0, h1, h2] <;> ring
  have hiL : Integrable L μ := by
    rw [hL]
    exact (((hf 0).add (hf 1)).add (hf 2)).sub (integrable_const (3 * ell))
  have hmeanL : (∫ z, L z ∂μ) = 3 * (ν - ell) := by
    rw [hL, integral_sub, integral_add, integral_add]
    change (∫ z, f 0 z ∂μ) + (∫ z, f 1 z ∂μ) + (∫ z, f 2 z ∂μ) - _ = _
    rw [show (∫ z, f 0 z ∂μ) = ν from hmean 0,
      show (∫ z, f 1 z ∂μ) = ν from hmean 1,
      show (∫ z, f 2 z ∂μ) = ν from hmean 2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
    all_goals first
      | exact integrable_const _
      | exact hf 0
      | exact hf 1
      | exact hf 2
      | exact (hf 0).add (hf 1)
      | exact ((hf 0).add (hf 1)).add (hf 2)
  have hi0 : Integrable (I.indicator (fun _ : Ω => u + w - ell)) μ :=
    (integrable_const _).indicator hI
  have hi1 : Integrable (F1.indicator (fun _ : Ω => max (1 - ell - w) 0)) μ :=
    (integrable_const _).indicator hF1
  have hi2 : Integrable (F2.indicator (fun _ : Ω => max (1 - ell - u) 0)) μ :=
    (integrable_const _).indicator hF2
  have hiR : Integrable R μ := (hi0.add hi1).add hi2
  have hmeanR : (∫ z, R z ∂μ) = μ.real I * (u + w - ell) +
      μ.real F1 * max (1 - ell - w) 0 + μ.real F2 * max (1 - ell - u) 0 := by
    rw [show R = fun z => I.indicator (fun _ => u + w - ell) z +
      F1.indicator (fun _ => max (1 - ell - w) 0) z +
      F2.indicator (fun _ => max (1 - ell - u) 0) z from rfl,
      integral_add, integral_add,
      integral_indicator hI, integral_indicator hF1, integral_indicator hF2]
    simp only [setIntegral_const, smul_eq_mul]
    all_goals first
      | exact hi0
      | exact hi1
      | exact hi2
      | exact hi0.add hi1
  have hh := integral_mono_ae hiL hiR hle
  rw [hmeanL, hmeanR] at hh
  have hm1 := mul_le_mul_of_nonneg_right hmissing1 (le_max_right (1 - ell - w) 0)
  have hm2 := mul_le_mul_of_nonneg_right hmissing2 (le_max_right (1 - ell - u) 0)
  have hscalar := universal_star_capacity_above_delta hA hAhalf (by linarith [hell.1])
    hu (hcap (v 0, v 2))
  change 3 * (ν - ell) ≤ μ.real I * (u + w - ell) +
    μ.real {z | G (z, v 1) = false} * max (1 - ell - w) 0 +
    μ.real {z | G (z, v 2) = false} * max (1 - ell - u) 0 at hh
  change μ.real I * (u + w - ell) + (1 - 2 * μ.real I) *
    (max (1 - ell - w) 0 + max (1 - ell - u) 0) ≤
      μ.real I * (u + 1 - ell) at hscalar
  nlinarith


/-- Closed physical missing sections at almost every vertex outside both
heads have the actual capacity 1−2A supplied by the localized root edit. -/
private theorem ae_partner_exterior_missing_capacity
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val → S.ρ x ≠ p.val →
      μ.real {z | PhysicalRepresentative.adjacency W m x z = false} ≤
        1 - 2 * μ.real {z | S.ρ z = r.val} := by
  filter_upwards [(ae_restrict_iff' (((S.hfibers r.val r.property).1.union
      (S.hfibers p.val p.property).1).compl)).mp
      (S.ae_universalPartner_exterior_degree_ge_twice_mass r p hpair hW hd hgap hell hN),
    Measure.ae_ae_of_ae_prod (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)] with x hg hp hx hxp
  let F := {z | PhysicalRepresentative.adjacency W m x z = false}
  have hF : MeasurableSet F :=
    (PhysicalRepresentative.measurable_adjacency W m).comp
      (measurable_const.prodMk measurable_id) (measurableSet_singleton false)
  have heq : F.indicator (fun _ : Ω => (1 : ℝ)) =ᵐ[μ]
      (fun z => 1 - adjacencyKernel W x z) := by
    filter_upwards [hp] with z hz
    change W.moment CappedColor.adjacency (x, z) = _ at hz
    change F.indicator (fun _ => (1 : ℝ)) z = 1 - W.moment CappedColor.adjacency (x, z)
    rw [hz]
    cases he : PhysicalRepresentative.adjacency W m x z <;> simp [F, he]
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
      exact (adjacency_moment_mem W (x, z)).2))
  have he := integral_congr_ae heq
  rw [integral_indicator hF, setIntegral_const, smul_eq_mul, mul_one,
    integral_sub (integrable_const 1) hi, integral_const, probReal_univ,
    smul_eq_mul, one_mul] at he
  change μ.real F ≤ _
  linarith [hg (fun h => h.elim hx hxp)]

private theorem ae_hole_partner_nonedge
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.universalPartnerHoleRegion r p →
      S.ρ q.2 = p.val → PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_adjacency p hW hd hgap)
  filter_upwards [hswap] with q hq hH hp
  have he := hq hp
  have hnot : q.1 ∉ S.rootNeighborhood p := by
    intro hN
    exact hH (Or.inr hN)
  cases hA : PhysicalRepresentative.adjacency W m q.1 q.2 with
  | false => rfl
  | true =>
      rw [PhysicalRepresentative.adjacency_symm W m q.1 q.2] at hA
      exact False.elim (hnot (he.mp hA))

/-- Missing the entire original partner fiber caps the degree of every
vertex in the partner's outside hole, modulo the original law. -/
theorem ae_universalPartnerHole_degree_le_one_sub_partner_mass
    (S : SelectedHighLowStructure W m) (r p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      (∫ z, adjacencyKernel W x z ∂μ) ≤ 1 - S.originalAtomMass p := by
  let P := {x | S.ρ x = p.val}
  let H := S.universalPartnerHoleRegion r p
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hAdjPH : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict H),
      adjacencyKernel W q.1 q.2 = 0 := by
    have hle : (μ.restrict P).prod (μ.restrict H) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [ae_mono hle (S.ae_root_adjacency p hW hd hgap),
      ae_mono hle (PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hH)]
      with q hr he hp hH'
    have hnotN : q.2 ∉ S.rootNeighborhood p := fun h => hH' (Or.inr h)
    have hfalse : PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
      cases hA : PhysicalRepresentative.adjacency W m q.1 q.2 with
      | false => rfl
      | true => exact False.elim (hnotN ((hr hp).mp hA))
    change adjacencyKernel W q.1 q.2 = _ at he
    rw [he, hfalse]
    norm_num
  have hswap := (Measure.measurePreserving_swap
    (μ := μ.restrict H) (ν := μ.restrict P)).quasiMeasurePreserving
  have hAdjHP : ∀ᵐ q ∂(μ.restrict H).prod (μ.restrict P),
      adjacencyKernel W q.1 q.2 = 0 := by
    have hle : (μ.restrict H).prod (μ.restrict P) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [hswap.ae hAdjPH, ae_mono hle (adjacencyKernel_symm W)]
      with q hz hs
    change adjacencyKernel W q.2 q.1 = 0 at hz
    exact hs.trans hz
  have hsec := Measure.ae_ae_of_ae_prod hAdjHP
  filter_upwards [hsec] with x hx
  have hzeroP := (ae_restrict_iff' hP).mp hx
  have hpoint : ∀ᵐ y ∂μ,
      adjacencyKernel W x y ≤ 1 - P.indicator (fun _ => (1 : ℝ)) y := by
    filter_upwards [hzeroP] with y hy
    by_cases hp : y ∈ P
    · rw [hy hp, indicator_of_mem hp]
      norm_num
    · simp only [indicator_of_notMem hp, sub_zero]
      exact (adjacency_moment_mem W (x, y)).2
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun y => by
      change ‖W.moment CappedColor.adjacency (x, y)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, y)).1]
      exact (adjacency_moment_mem W (x, y)).2))
  have hiP : Integrable (P.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hP
  have hle := integral_mono_ae hi ((integrable_const 1).sub hiP) hpoint
  change (∫ y, adjacencyKernel W x y ∂μ) ≤
    ∫ y, (1 : ℝ) - P.indicator (fun _ => (1 : ℝ)) y ∂μ at hle
  rw [integral_sub (integrable_const 1) hiP, integral_const, probReal_univ,
    one_smul] at hle
  have hiPeq : (∫ y, P.indicator (fun _ => (1 : ℝ)) y ∂μ) = μ.real P :=
    integral_indicator_one hP
  rw [hiPeq] at hle
  exact hle

omit [StandardBorelSpace Ω] [MeasurableEq Ω] in
private theorem orderRootLeaves_zero_of_no_incidence
    {n : ℕ} (ρ : Measure (Fin n → Ω)) (I B : Set Ω) (hB : MeasurableSet B)
    (hno : ∀ᵐ v ∂ρ, ∀ i j, i ≠ j → v i ∈ I → v j ∈ B → False) :
    PhysicalPrimal.orderRootLeaves n ρ I B = 0 := by
  rw [PhysicalPrimal.orderRootLeaves, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro ij _
  rw [Measure.map_apply (measurable_pi_apply _) hB,
    Measure.restrict_apply (hB.preimage (measurable_pi_apply _))]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hno] with v hv hm
  exact hv ij.val.1 ij.val.2 ij.property hm.2 hm.1

private theorem ae_all_pairs_of_pair_AC_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} (ρ : Measure (Fin n → Ω))
    (hpairs : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (P : Ω × Ω → Prop) (hP : ∀ᵐ p ∂μ.prod μ, P p) :
    ∀ᵐ v ∂ρ, ∀ i j, i ≠ j → P (v i, v j) := by
  simp only [ae_all_iff]
  intro i j hij
  exact ae_of_ae_map ((measurable_pi_apply i).prodMk
    (measurable_pi_apply j)).aemeasurable ((hpairs i j hij).ae_le hP)

private theorem ae_all_coordinates_of_pair_AC_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    (ρ : Measure (Fin n → Ω))
    (hpairs : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (P : Ω → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ v ∂ρ, ∀ i, P (v i) := by
  simp only [ae_all_iff]
  intro i
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable
    ((PhysicalCliqueRepresentative.coordinate_absolutelyContinuous_of_pairs
      μ hn ρ hpairs i).ae_le hP)


/-- The actual selected model exposes the sharp first root-star threshold in every
singular pair-AC tight triangle law. Flat rows, universal fresh sections,
missing capacities and all insertion tests are derived internally. -/
theorem ae_permuted_rooted_triangle_star_gt_delta (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hAhalf : μ.real {x | S.ρ x = r.val} ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * μ.real {x | S.ρ x = r.val} * (1 + m) <
      3 * (2 * (c - m * d) + m))
    (ρ : Measure (Fin 3 → Ω)) [IsFiniteMeasure ρ]
    (hpairs : ∀ i j : Fin 3, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) v)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge
      (Function.uncurry (PhysicalRepresentative.charge W m)) v = 1) :
    ∀ᵐ v ∂ρ, ∀ e : Equiv.Perm (Fin 3),
      S.ρ (v (e 0)) = r.val →
        S.ρ (v (e 1)) ≠ p.val → S.ρ (v (e 2)) ≠ p.val →
          1 + m < S.rootChargeRow r (v (e 1)) ∧
            3 * (2 * (c - m * d) + m) / μ.real {x | S.ρ x = r.val} - (1 + m) ≤
              S.rootChargeRow r (v (e 1)) := by
  let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hs := hW.strict_gap_structure hd hgap
  have htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
    intro n _
    filter_upwards [PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
      hW.deterministic n] with v hv hc
    change PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v ≤ 1
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    exact hv hc
  have hins := PhysicalTriangleExposure.ae_insertion_le_majorant_permutations G
    (PhysicalRepresentative.measurable_adjacency W m)
    (PhysicalRepresentative.adjacency_symm W m) Y (PhysicalRepresentative.measurable_charge W m)
    (PhysicalRepresentative.charge_symm W m) 3 (by norm_num)
    (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
    (fun p => (PhysicalRepresentative.charge_mem_Icc W m p.1 p.2).2)
    (fun p => PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2)
    htest (-m) ρ hpairs hclique htight
  have hroot := S.neutral_atom_physical_adjacency r hW hd hgap hN
  have hvertex : ∀ᵐ x ∂μ,
      ((∫ z, Y (z, x) + (-m) * (if G (z, x) then 1 else 0) ∂μ) = 2 * (c - m * d)) ∧
      (S.ρ x = r.val → ∀ᵐ z ∂μ, G (z, x) = false ↔ z ∈ I) ∧
      (S.ρ x ≠ r.val → ∀ᵐ z ∂μ, z ∈ I → G (z, x) = true) ∧
      (S.ρ x ≠ r.val → S.ρ x ≠ p.val →
        μ.real {z | G (z, x) = false} ≤ 1 - 2 * μ.real I) := by
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hroot
    filter_upwards [S.ae_physical_shifted_column_stationary hW hd hgap,
      Measure.ae_ae_of_ae_prod hroot, Measure.ae_ae_of_ae_prod hswap,
      S.ae_partner_exterior_missing_capacity r p hpair hW hd hgap hN hell.2]
      with x hf hr hc hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · convert hf using 1
      congr 1
      funext z
      cases hg : PhysicalRepresentative.adjacency W m z x <;> simp [G, Y, hg]
      ring
    · intro hx
      filter_upwards [hr] with z hz
      have he := hz hx
      change (PhysicalRepresentative.adjacency W m x z = true ↔ S.ρ z ≠ r.val) at he
      change PhysicalRepresentative.adjacency W m z x = false ↔ S.ρ z = r.val
      rw [PhysicalRepresentative.adjacency_symm W m z x]
      constructor
      · intro hg
        by_contra hne
        have ht := he.mpr hne
        rw [hg] at ht
        contradiction
      · intro hzroot
        cases hg : PhysicalRepresentative.adjacency W m x z with
        | false => rfl
        | true => exact False.elim ((he.mp hg) hzroot)
    · intro hx
      filter_upwards [hc] with z hz hzI
      exact (hz hzI).mpr hx
    · intro hx hxp
      have he : {z | G (z, x) = false} =
          {z | PhysicalRepresentative.adjacency W m x z = false} := by
        ext z
        change PhysicalRepresentative.adjacency W m z x = false ↔
          PhysicalRepresentative.adjacency W m x z = false
        rw [PhysicalRepresentative.adjacency_symm W m z x]
      rw [he]
      exact hm hx hxp
  have hcoords := ae_all_coordinates_of_pair_AC_upper (by norm_num : 2 ≤ 3) ρ hpairs _ hvertex
  have hrootPairs := ae_all_pairs_of_pair_AC_upper ρ hpairs _ hroot
  have hchargePairs := ae_all_pairs_of_pair_AC_upper ρ hpairs _ (S.ae_root_charge r hW hd hgap)
  filter_upwards [hins, hcoords, hrootPairs, hchargePairs, hclique, htight]
    with v hi hc hr hY hv ht e hv0 hv1p hv2p
  have he01 : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (e.injective h)
  have he02 : e 0 ≠ e 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (e.injective h)
  have hv1 : S.ρ (v (e 1)) ≠ r.val := (hr (e 0) (e 1) he01 hv0).mp (hv _ _ he01)
  have hv2 : S.ρ (v (e 2)) ≠ r.val := (hr (e 0) (e 2) he02 hv0).mp (hv _ _ he02)
  have hold : Y (v (e 0), v (e 1)) + Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)) = 1 := by
    have ht' := (PhysicalTriangleExposure.charge_comp_equiv Y v e).trans ht
    have he : (fun i => v (e i)) = ![v (e 0), v (e 1), v (e 2)] := by
      funext i
      fin_cases i <;> rfl
    rw [he, PhysicalTriangleExposure.charge_three Y (PhysicalRepresentative.charge_symm W m)] at ht'
    exact ht'
  have hp := first_star_gt_delta_of_insertion_and_capacity G
    (PhysicalRepresentative.measurable_adjacency W m) Y
    (PhysicalRepresentative.measurable_charge W m)
    3 (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
    (fun p => (PhysicalRepresentative.charge_mem_Icc W m p.1 p.2).2)
    (-m) (2 * (c - m * d)) ⟨hell.1.le, hell.2.le⟩ (fun i => v (e i)) I hI hA.le
    (by simpa only [sub_neg_eq_add] using hmargin) hold ((hc (e 0)).2.1 hv0)
    ((hc (e 1)).2.2.1 hv1) ((hc (e 2)).2.2.1 hv2) (fun i => (hc (e i)).1)
    ((hc (e 1)).2.2.2 hv1 hv1p) ((hc (e 2)).2.2.2 hv2 hv2p) (hi e)
  have hb := first_star_integral_bound_above_delta G
    (PhysicalRepresentative.measurable_adjacency W m) Y
    (PhysicalRepresentative.measurable_charge W m)
    3 (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
    (fun p => (PhysicalRepresentative.charge_mem_Icc W m p.1 p.2).2)
    (-m) (2 * (c - m * d)) ⟨hell.1.le, hell.2.le⟩ (fun i => v (e i)) I hI hA.le
    hAhalf hold ((hc (e 0)).2.1 hv0)
    ((hc (e 1)).2.2.1 hv1) ((hc (e 2)).2.2.1 hv2) (fun i => (hc (e i)).1)
    ((hc (e 1)).2.2.2 hv1 hv1p) ((hc (e 2)).2.2.2 hv2 hv2p) (hi e) hp.le
  have hApos : 0 < μ.real I := by linarith [hA]
  have hθ : 3 * (2 * (c - m * d) + m) / μ.real I - (1 + m) ≤
      Y (v (e 0), v (e 1)) := by
    have hh := (div_le_iff₀ hApos).mpr (show 3 * (2 * (c - m * d) + m) ≤
      (Y (v (e 0), v (e 1)) + (1 + m)) * μ.real I by
        convert hb using 1 <;> ring)
    linarith
  rw [show Y (v (e 0), v (e 1)) = S.rootChargeRow r (v (e 1)) from hY _ _ he01 hv0]
    at hp hθ
  exact ⟨by simpa only [sub_neg_eq_add] using hp, by simpa only [I] using hθ⟩



/-- The same actual physical primal transfers the signed insertion
threshold to almost every original vertex in the partner's hole. -/
theorem UniversalPhysicalPrimal.ae_universal_upperE2_hole_star_threshold
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalPartnerHoleRegion r p),
      3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m) ≤
        S.rootChargeRow r x := by
  let I := {x | S.ρ x = r.val}
  let H := S.universalPartnerHoleRegion r p
  let θ := 3 * (2 * (c - m * d) + m) / S.originalAtomMass r - (1 + m)
  let B := H ∩ {x | S.rootChargeRow r x < θ}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hB : MeasurableSet B := hH.inter
    (measurableSet_lt (S.measurable_rootChargeRow r) measurable_const)
  have hBV : B ⊆ (I ∪ {x | S.ρ x = p.val})ᶜ :=
    fun _ hx h => hx.1 (Or.inl h)
  have : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  have hdemand : PhysicalPrimal.graphDemand μ
      {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true} ≪ μ.prod μ :=
    Measure.absolutelyContinuous_restrict
  have hpairs : ∀ i j : Fin 3, i ≠ j →
      (P.laws 3).map (fun v => (v i, v j)) ≪ μ.prod μ := by
    intro i j hij
    exact (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
      P.feasible.2.2.2 3 ⟨(i, j), hij⟩).trans hdemand
  have hthreshold := S.ae_permuted_rooted_triangle_star_gt_delta r p hpair hW hd hgap hN
    hA hAhalf hell hmargin (P.laws 3) hpairs (P.feasible.2.2.1 3)
      (P.tight_physical 3)
  have hzero := P.ae_original_pairs _
    (S.ae_hole_partner_nonedge r p hW hd hgap) 3
  have hperm : ∀ i j : Fin 3, i ≠ j →
      ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by decide
  have hno : ∀ᵐ v ∂P.laws 3, ∀ i j, i ≠ j → v i ∈ I → v j ∈ B → False := by
    filter_upwards [hthreshold, hzero, P.feasible.2.2.1 3] with v ht hz hc i j hij hi hj
    obtain ⟨e, he0, he1⟩ := hperm i j hij
    have he12 : e 1 ≠ e 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (e.injective h)
    have hj' : v (e 1) ∈ B := by rw [he1]; exact hj
    have hv1p : S.ρ (v (e 1)) ≠ p.val := by
      intro hp
      exact hj'.1 (Or.inl (Or.inr hp))
    have hv2p : S.ρ (v (e 2)) ≠ p.val := by
      intro hp
      have hfalse := hz (e 1) (e 2) he12 hj'.1 hp
      have htrue := hc (e 1) (e 2) he12
      exact Bool.false_ne_true (hfalse.symm.trans htrue)
    have hbound := (ht e (he0 ▸ hi) hv1p hv2p).2
    change θ ≤ S.rootChargeRow r (v (e 1)) at hbound
    exact (not_lt_of_ge hbound) hj'.2
  have hsmall : ∀ n, n < 4 → PhysicalPrimal.orderRootLeaves n (P.laws n) I B = 0 := by
    intro n hn
    interval_cases n
    · simp [P.feasible.1, PhysicalPrimal.orderRootLeaves]
    · simp [P.feasible.2.1, PhysicalPrimal.orderRootLeaves]
    · exact P.orderRootLeaves_two_off_partner_eq_zero p hpair hW hd hgap hell.2 B hB hBV
    · apply orderRootLeaves_zero_of_no_incidence (P.laws 3) I B hB
      exact hno
  have hE : MeasurableSet {p : Ω × Ω |
      PhysicalRepresentative.adjacency W m p.1 p.2 = true} :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hzeroB := PhysicalPrimal.null_event_of_small_root_incidence P.laws μ _ hE
    P.feasible.2.2.2 I hI (S.neutral_atom_physical_blocks r hW hd hgap hN).1
    P.unique_root B hB (fun x hx hi => hBV hx (Or.inl hi)) hsmall hA
  have hnot : ∀ᵐ x ∂μ, x ∉ B := measure_eq_zero_iff_ae_notMem.mp hzeroB
  exact (ae_restrict_iff' hH).mpr (hnot.mono (fun _ hx hH' => by
    by_contra hbad
    exact hx ⟨hH', lt_of_not_ge hbad⟩))

/-- The actual bad set lies in the partner's common region modulo the
original law. The hole-side exclusion is paid by the same tight primal. -/
theorem UniversalPhysicalPrimal.ae_universalUpperE2Bad_subset_common
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ, x ∈ S.universalUpperE2BadRegion r p d c →
      x ∈ S.universalPartnerCommonRegion r p := by
  have hH := (ae_restrict_iff' (S.measurableSet_universalPartnerHoleRegion r p)).mp
    (P.ae_universal_upperE2_hole_star_threshold S r p hpair hW hd hgap hN hA
      hAhalf hell hmargin)
  filter_upwards [hH] with x hx hbad
  have hnotH : x ∉ S.universalPartnerHoleRegion r p := by
    intro hH'
    have hb := hx hH'
    exact (not_lt_of_ge hb) hbad.2
  exact fun h => h.elim hbad.1 hnotH

/-- Every actual tight root triangle with a bad leaf spends its third
vertex in the saturated partner fiber. -/
theorem UniversalPhysicalPrimal.ae_universalUpperE2Bad_partner_stock
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ v ∂P.laws 3, ∀ i j : Fin 3, i ≠ j →
      S.ρ (v i) = r.val → v j ∈ S.universalUpperE2BadRegion r p d c →
        ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ S.ρ (v k) = p.val := by
  have : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  have hdemand : PhysicalPrimal.graphDemand μ
      {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true} ≪ μ.prod μ :=
    Measure.absolutelyContinuous_restrict
  have hpairs : ∀ i j : Fin 3, i ≠ j →
      (P.laws 3).map (fun v => (v i, v j)) ≪ μ.prod μ := by
    intro i j hij
    exact (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
      P.feasible.2.2.2 3 ⟨(i, j), hij⟩).trans hdemand
  have hthreshold := S.ae_permuted_rooted_triangle_star_gt_delta r p hpair hW hd hgap hN
    hA hAhalf hell hmargin (P.laws 3) hpairs (P.feasible.2.2.1 3)
      (P.tight_physical 3)
  have hperm : ∀ i j : Fin 3, i ≠ j →
      ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by decide
  filter_upwards [hthreshold] with v ht i j hij hi hj
  obtain ⟨e, he0, he1⟩ := hperm i j hij
  have he20 : e 2 ≠ i := by
    rw [← he0]
    exact fun h => (by decide : (2 : Fin 3) ≠ 0) (e.injective h)
  have he21 : e 2 ≠ j := by
    rw [← he1]
    exact fun h => (by decide : (2 : Fin 3) ≠ 1) (e.injective h)
  by_cases hp : S.ρ (v (e 2)) = p.val
  · exact ⟨e 2, he20, he21, hp⟩
  · have hj' : v (e 1) ∈ S.universalUpperE2BadRegion r p d c := by
      rw [he1]
      exact hj
    have hv1p : S.ρ (v (e 1)) ≠ p.val := fun h => hj'.1 (Or.inr h)
    have hbound := (ht e (he0 ▸ hi) hv1p hp).2
    exact False.elim ((not_lt_of_ge hbound) hj'.2)

/-- Charging every bad I-root triangle against its P-pair stock gives
the actual original physical-degree lower bound on the bad set. -/
theorem UniversalPhysicalPrimal.ae_universalUpperE2Bad_physicalDegree_ge
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalUpperE2BadRegion r p d c),
      3 * S.originalAtomMass r - S.originalAtomMass p ≤
        (PhysicalPrimal.graphDegree μ
          {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true} x).toReal := by
  have hB := S.measurableSet_universalUpperE2BadRegion r p d c
  have hBV : S.universalUpperE2BadRegion r p d c ⊆
      ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ := fun _ hx => hx.1
  exact P.ae_degree_lower_of_triangle_partner p hpair hW hd hgap hell.2 _ hB hBV
    (P.ae_universalUpperE2Bad_partner_stock S r p hpair hW hd hgap hN hA hAhalf
      hell hmargin)

theorem UniversalPhysicalPrimal.ae_universalUpperE2Bad_originalDegree_ge
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalUpperE2BadRegion r p d c),
      3 * S.originalAtomMass r - S.originalAtomMass p ≤
        ∫ z, adjacencyKernel W x z ∂μ := by
  filter_upwards [P.ae_universalUpperE2Bad_physicalDegree_ge S r p hpair hW hd hgap
    hN hA hAhalf hell hmargin,
    ae_restrict_of_ae (PhysicalRepresentative.ae_graphDegree_eq_original hW hd hgap)]
    with x hb he
  rw [he] at hb
  exact hb

/-- The partner's saturated unit edge leaves opposite physical root
charges at almost every bad original vertex. -/
theorem UniversalPhysicalPrimal.ae_universalUpperE2Bad_partner_charge
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ x ∂μ.restrict (S.universalUpperE2BadRegion r p d c),
      S.rootChargeRow p x = -S.rootChargeRow r x := by
  let B := S.universalUpperE2BadRegion r p d c
  let V := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ
  let F := fun x => x ∈ B → S.rootChargeRow r x + S.rootChargeRow p x = 0
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hV : MeasurableSet V :=
    ((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl
  have hF : MeasurableSet {x | F x} := by
    have he : {x | F x} =
        Bᶜ ∪ {x | S.rootChargeRow r x + S.rootChargeRow p x = 0} := by
      ext x
      simp only [F, mem_ofPred_eq, mem_union, mem_compl_iff]
      tauto
    rw [he]
    exact hB.compl.union (measurableSet_eq_fun
      ((S.measurable_rootChargeRow r).add (S.measurable_rootChargeRow p)) measurable_const)
  have hstock := P.ae_universalUpperE2Bad_partner_stock S r p hpair hW hd hgap hN hA
    hAhalf hell hmargin
  have hscore := P.ae_triangle_partner_score_zero p hpair hW hd hgap
  have hperm : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j ∧ e 2 = k := by decide
  have htriangle : ∀ᵐ v ∂P.laws 3, ∀ i j : Fin 3, i ≠ j →
      S.ρ (v i) = r.val → v j ∈ V → F (v j) := by
    filter_upwards [hstock, hscore] with v hs hc i j hij hi _ hbad
    obtain ⟨k, hki, hkj, hpk⟩ := hs i j hij hi hbad
    obtain ⟨e, he0, he1, he2⟩ := hperm i k j hki.symm hij hkj
    simpa only [he0, he1, he2] using hc e (by rw [he0]; exact hi)
      (by rw [he1]; exact hpk)
  have htransfer := P.ae_off_partner_of_triangle p hpair hW hd hgap hell.2 hA F hF
    htriangle
  apply (ae_restrict_iff' hB).mpr
  filter_upwards [(ae_restrict_iff' hV).mp htransfer] with x hx hbad
  have hv : x ∈ V := hbad.1
  linarith [hx hv hbad]

/-- The original HIGH partner hole joins every bad vertex. A missing
pair would cross in the wrong original degree direction. -/
theorem UniversalPhysicalPrimal.ae_universalUpperE2_hole_bad_join
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p) (P : S.UniversalPhysicalPrimal r c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hA : 1 / 3 < S.originalAtomMass r)
    (hAhalf : S.originalAtomMass r ≤ 1 / 2)
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * S.originalAtomMass r * (1 + m) <
      3 * (2 * (c - m * d) + m)) :
    ∀ᵐ q ∂μ.prod μ, q.1 ∈ S.universalPartnerHoleRegion r p →
      q.2 ∈ S.universalUpperE2BadRegion r p d c →
        adjacencyKernel W q.1 q.2 = 1 := by
  let H := S.universalPartnerHoleRegion r p
  let B := S.universalUpperE2BadRegion r p d c
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hH : MeasurableSet H := S.measurableSet_universalPartnerHoleRegion r p
  have hB : MeasurableSet B := S.measurableSet_universalUpperE2BadRegion r p d c
  have hHdeg := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_degree_le_one_sub_partner_mass r p hW hd hgap)
  have hBdeg := (ae_restrict_iff' hB).mp
    (P.ae_universalUpperE2Bad_originalDegree_ge S r p hpair hW hd hgap hN hA
      hAhalf hell hmargin)
  have hHigh := (ae_restrict_iff' hH).mp
    (S.ae_universalPartnerHole_high r p hpair hW hd hgap hell.2)
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hfactor := ae_degree_eq_wholeRowDegree W m S.ρ S.hrow hs
  have hop := KernelOperator.onL2_coe (adjacencyKernel W)
    (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
    (Lp.const 2 μ (1 : ℝ))
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hHdeg,
    Measure.quasiMeasurePreserving_snd.ae hBdeg,
    Measure.quasiMeasurePreserving_fst.ae hHigh,
    Measure.quasiMeasurePreserving_fst.ae hfactor,
    Measure.quasiMeasurePreserving_snd.ae hfactor,
    Measure.quasiMeasurePreserving_fst.ae hop,
    Measure.quasiMeasurePreserving_snd.ae hop,
    S.ae_zero_iff_sameAtom_or_relation hW hd hgap,
    S.hrelation, hW.moment_mem, hs]
    with q hh hb hhigh hfx hfy hox hoy hzero hrel hnonneg hsupport hx hy
  have hxg : g q.1 = ∫ z, adjacencyKernel W q.1 z ∂μ := by
    change g q.1 = KernelOperator.applyKernel (adjacencyKernel W)
      (Lp.const 2 μ (1 : ℝ)) q.1 at hox
    rw [hox, KernelOperator.applyKernel]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with z hz
    simp only [hz, Function.const_apply, mul_one]
  have hyg : g q.2 = ∫ z, adjacencyKernel W q.2 z ∂μ := by
    change g q.2 = KernelOperator.applyKernel (adjacencyKernel W)
      (Lp.const 2 μ (1 : ℝ)) q.2 at hoy
    rw [hoy, KernelOperator.applyKernel]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with z hz
    simp only [hz, Function.const_apply, mul_one]
  have hgt : g q.1 < g q.2 := by
    rw [hxg, hyg]
    have hthree : 1 < 3 * S.originalAtomMass r := by linarith [hA]
    linarith [hh hx, hb hy]
  have hnotK : shiftedKernel W m q.1 q.2 ≠ 0 := by
    intro hK
    rcases hzero.mp hK with hsame | hZ
    · have heq : S.ρ q.1 = S.ρ q.2 := hsame.1
      exact (ne_of_lt hgt) (hfx.trans (heq ▸ hfy.symm))
    · rcases hrel hZ with h | h
      · linarith [h.2.2]
      · exact (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 (hhigh hx) h.2.1).elim
  have hKpos : 0 < shiftedKernel W m q.1 q.2 :=
    lt_of_le_of_ne hnonneg.1 (Ne.symm hnotK)
  change 0 < shiftedMoment W m q at hKpos
  have heq : adjacencyKernel W q.1 q.2 =
      if 0 < shiftedMoment W m q then 1 else 0 := hsupport
  simpa only [ite_eq_left hKpos] using heq



end Erdos1017.CappedModel.SelectedHighLowStructure
