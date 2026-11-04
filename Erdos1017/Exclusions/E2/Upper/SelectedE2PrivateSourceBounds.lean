module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateSourceCover
public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateCapacityAssembly
public import Erdos1017.Exclusions.E2.Upper.SelectedE2PrivateRadius
public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePeakBound
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedScoreFloor

/-!
# Scalar lower bound from the private sources

The entire compulsory-source deficit splits across the two private sectors and
the shared sector, and the smooth `E₂` contact with one largest private whole
atom and the partial reverse capacity implies the receipt-free scalar lower
bound (`e2_private_source_scalar_lower_bound`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

private def sourceCoverValue (s L : ℝ) : ℝ := max 0 (min (s / 2) (s - L))

private theorem sourceCoverValue_add_le (s L a : ℝ) (ha : 0 ≤ a) :
    sourceCoverValue (s + a) L ≤ sourceCoverValue s L + a := by
  unfold sourceCoverValue
  have hmin : min ((s + a) / 2) (s + a - L) ≤ min (s / 2) (s - L) + a := by
    calc
      min ((s + a) / 2) (s + a - L) ≤
          min (s / 2 + a) (s - L + a) :=
        min_le_min (by linarith) (by linarith)
      _ = min (s / 2) (s - L) + a := by rw [min_add_add_right]
  calc
    max 0 (min ((s + a) / 2) (s + a - L)) ≤
        max a (min (s / 2) (s - L) + a) :=
      max_le_max ha hmin
    _ = max 0 (min (s / 2) (s - L)) + a := by
      nth_rewrite 1 [← zero_add a]
      rw [max_add_add_right]

private theorem receipt_absorption (t a₁ a₂ α₁ α₂ A Rrad κ ν ζ D₁ D₂ : ℝ)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) (hζ : 0 ≤ ζ) (hκ : ζ ≤ κ)
    (hcover₁ : ζ * sourceCoverValue (t - a₁ - α₁) A ≤ D₁)
    (hcover₂ : ζ * sourceCoverValue (t - a₂ - α₂) (Rrad - a₂) ≤ D₂)
    (hcapacity : D₁ + D₂ + κ * (α₁ + α₂) + ζ * (1 - 2 * t) ≤ κ - 2 * ν) :
    ζ * (1 - 2 * t + sourceCoverValue (t - a₁) A +
      sourceCoverValue (t - a₂) (Rrad - a₂)) ≤ κ - 2 * ν := by
  have h₁ := sourceCoverValue_add_le (t - a₁ - α₁) A α₁ hα₁
  have h₂ := sourceCoverValue_add_le (t - a₂ - α₂) (Rrad - a₂) α₂ hα₂
  have h₁' : sourceCoverValue (t - a₁) A ≤
      sourceCoverValue (t - a₁ - α₁) A + α₁ := by
    simpa only [sub_add_cancel] using h₁
  have h₂' : sourceCoverValue (t - a₂) (Rrad - a₂) ≤
      sourceCoverValue (t - a₂ - α₂) (Rrad - a₂) + α₂ := by
    simpa only [sub_add_cancel] using h₂
  have hmul₁ := mul_le_mul_of_nonneg_left h₁' hζ
  have hmul₂ := mul_le_mul_of_nonneg_left h₂' hζ
  have hmulκ := mul_le_mul_of_nonneg_right hκ (add_nonneg hα₁ hα₂)
  nlinarith only [hcover₁, hcover₂, hcapacity, hmul₁, hmul₂, hmulκ]

private theorem sourceCoverValue_sum_lower (t a₁ a₂ A Rrad : ℝ)
    (ht : t ≤ 1 / 2) (hhead : 2 * A + t + a₁ ≤ 1)
    (ha₂ : a₂ ≤ Rrad) (hR : Rrad ≤ t) :
    t / 2 + A - Rrad / 2 ≤
      1 - 2 * t + sourceCoverValue (t - a₁) A +
        sourceCoverValue (t - a₂) (Rrad - a₂) := by
  have h₁ : 2 * t + A - 1 ≤ sourceCoverValue (t - a₁) A := by
    unfold sourceCoverValue
    apply le_max_of_le_right
    apply le_min
    · linarith
    · linarith
  have h₂ : (t - Rrad) / 2 ≤ sourceCoverValue (t - a₂) (Rrad - a₂) := by
    unfold sourceCoverValue
    apply le_max_of_le_right
    apply le_min
    · linarith
    · linarith
  linarith

private theorem source_bounds_scalar (t a₁ a₂ α₁ α₂ A Rrad κ ν ζ D₁ D₂ : ℝ)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) (hζ : 0 ≤ ζ) (hκ : ζ ≤ κ)
    (ht : t ≤ 1 / 2) (hhead : 2 * A + t + a₁ ≤ 1)
    (ha₂ : a₂ ≤ Rrad) (hR : Rrad ≤ t)
    (hcover₁ : ζ * sourceCoverValue (t - a₁ - α₁) A ≤ D₁)
    (hcover₂ : ζ * sourceCoverValue (t - a₂ - α₂) (Rrad - a₂) ≤ D₂)
    (hcapacity : D₁ + D₂ + κ * (α₁ + α₂) + ζ * (1 - 2 * t) ≤ κ - 2 * ν) :
    ζ * (t / 2 + A - Rrad / 2) ≤ κ - 2 * ν := by
  have hsum := sourceCoverValue_sum_lower t a₁ a₂ A Rrad ht hhead ha₂ hR
  have hmul := mul_le_mul_of_nonneg_left hsum hζ
  exact hmul.trans (receipt_absorption t a₁ a₂ α₁ α₂ A Rrad κ ν ζ D₁ D₂
    hα₁ hα₂ hζ hκ hcover₁ hcover₂ hcapacity)

variable {Ω : Type*} [MeasurableSpace Ω] [hBorel : StandardBorelSpace Ω]
  [hEq : MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [hNull : NullSingletonClass μ]
  [hSep : TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem privateDeficit_integrable (r u : S.I) :
    Integrable (S.twoCenterPrivateDeficit r u) μ := by
  have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  exact ((integrable_const _).sub hr).sub hu

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- On the shared source, both original missing head rows vanish almost
everywhere, so the actual original deficit is the head pairing. -/
theorem shared_privateDeficit_eq_headPairing (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hp : R.plateau = {r, u}) :
    ∀ᵐ x ∂μ.restrict (S.twoCenterShared r u),
      S.twoCenterPrivateDeficit r u x = S.headPairing r u := by
  filter_upwards [ae_restrict_of_ae (S.ae_whole_row_nonneg r hW),
    ae_restrict_of_ae (S.ae_whole_row_nonneg u hW),
    ae_restrict_mem (R.measurableSet_twoCenter_patterns r u hp).2.2]
    with x hr hu hx
  have hr0 : r.val x = 0 := le_antisymm hx.1.2.2 hr
  have hu0 : u.val x = 0 := le_antisymm hx.2.2 hu
  simp only [twoCenterPrivateDeficit, hr0, hu0, sub_zero]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The entire original compulsory-source deficit splits across the two
literal private sectors and the actual shared sector. -/
theorem entire_source_deficit_integral_eq (r u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hp : R.plateau = {r, u}) :
    (∫ x in S.reverseCompulsorySource R.plateau,
      S.twoCenterPrivateDeficit r u x ∂μ) =
      (∫ x in S.twoCenterPrivate r u, S.twoCenterPrivateDeficit r u x ∂μ) +
      (∫ x in S.twoCenterPrivate u r, S.twoCenterPrivateDeficit r u x ∂μ) +
      S.headPairing r u * μ.real (S.twoCenterShared r u) := by
  let C₁ := S.twoCenterPrivate r u
  let C₂ := S.twoCenterPrivate u r
  let U := S.twoCenterShared r u
  let f := S.twoCenterPrivateDeficit r u
  have hm := R.measurableSet_twoCenter_patterns r u hp
  have hd := S.twoCenter_patterns_disjoint r u
  have hf : Integrable f μ := privateDeficit_integrable r u
  have hpart : S.reverseCompulsorySource R.plateau = (C₁ ∪ C₂) ∪ U := by
    rw [hp, S.twoCenter_source_partition]
  rw [hpart, setIntegral_union (disjoint_union_left.mpr ⟨hd.2.1, hd.2.2⟩)
    hm.2.2 hf.integrableOn hf.integrableOn,
    setIntegral_union hd.1 hm.2.1 hf.integrableOn hf.integrableOn]
  have hU : (∫ x in U, f x ∂μ) = S.headPairing r u * μ.real U := by
    rw [integral_congr_ae (R.shared_privateDeficit_eq_headPairing r u hW hp),
      setIntegral_const, smul_eq_mul]
    ring
  rw [hU]

/-- The actual original head-price box and the strict intercept make the
private pair-cover threshold positive and no larger than the shared deficit. -/
theorem private_threshold_pos_le_pairing (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m) :
    0 < S.twoCenterPrivateThreshold r u ∧
      S.twoCenterPrivateThreshold r u ≤ S.headPairing r u := by
  let κ := S.headPairing r u
  let ν := 2 * (c - m * d)
  have hs := hW.strict_gap_structure hd hgap
  have hκ := R.headPairing_ge_two_stationary r u hru hW hd hgap hp hintercept
  have hκpos : 0 < κ := by dsimp only [κ]; linarith [hs.stationary_pos]
  dsimp only [κ, ν] at hκpos hκ
  have hr : r ∈ R.plateau := by rw [hp]; simp
  have hu : u ∈ R.plateau := by rw [hp]; simp
  have hprice := R.currentHeadPrice_le_one hW r u hr hu
  rw [R.current_head_price_eq_original hW r u hr hu,
    S.collapsedPartLabel_fiber, S.collapsedPartLabel_fiber,
    S.original_headPrice_eq_headPairing r u hW] at hprice
  simp only [ite_eq_left hκpos] at hprice
  dsimp only [twoCenterPrivateThreshold]
  constructor
  · linarith only [hκ, hintercept]
  · linarith only [hprice, hs.multiplier_neg]

include hBorel hEq hNull hSep in
/-- The actual conditional missing-mass radius bounds every original
whole-fiber cell of both private sectors, with the second head mass paid. -/
theorem e2_private_source_fiber_bounds (i r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.twoCenterPrivate r u)
    (hmax : ∀ k : S.I, S.originalAtomMass k ≤ S.originalAtomMass i)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    let B := missingMassCapRadius d c m (S.originalAtomMass i)
    (∀ k : S.I, μ.real (S.twoCenterPrivate r u ∩ {x | S.ρ x = k.val}) ≤
      S.originalAtomMass i) ∧
    (∀ k : S.I, μ.real (S.twoCenterPrivate u r ∩ {x | S.ρ x = k.val}) ≤
      B - S.originalAtomMass u) ∧
    S.originalAtomMass u ≤ B ∧ B < S.originalAtomMass i := by
  let B := missingMassCapRadius d c m (S.originalAtomMass i)
  obtain ⟨_, _, hBlt, _, hAu, hcap⟩ :=
    R.private_e2_radius_bounds i r u hru hp hprivate hmax hW hq hdq hgap hglobal
  refine ⟨?_, ?_, hAu, hBlt⟩
  · intro k
    have hm := measureReal_mono (show
      S.twoCenterPrivate r u ∩ {x | S.ρ x = k.val} ⊆
        {x | S.ρ x = k.val} from inter_subset_right)
      (measure_ne_top μ {x | S.ρ x = k.val})
    exact hm.trans (hmax k)
  · intro k
    let C := S.twoCenterPrivate u r ∩ {x | S.ρ x = k.val}
    by_cases hCpos : 0 < μ C
    · have hm := measureReal_mono
        (show C ⊆ {x | S.ρ x = k.val} from inter_subset_right)
        (measure_ne_top μ {x | S.ρ x = k.val})
      have hb := hcap k hCpos
      change μ.real C ≤ S.originalAtomMass k at hm
      change μ.real C ≤ B - S.originalAtomMass u
      linarith
    · have hCzero : μ C = 0 := le_antisymm (le_of_not_gt hCpos) zero_le
      have hreal : μ.real C = 0 := by rw [measureReal_def, hCzero, ENNReal.toReal_zero]
      change μ.real C ≤ B - S.originalAtomMass u
      rw [hreal]
      linarith

/-- The actual private whole atom and its unsaturated opposite head give
the original mass budget used to eliminate the first private receipt. -/
theorem private_peak_mass_budget (i r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.twoCenterPrivate r u) :
    2 * S.originalAtomMass i + R.height + S.originalAtomMass r +
      R.sharedReceipt r u ≤ 1 := by
  have hcard : R.plateau.card = 2 := by rw [hp, Finset.card_pair hru]
  have hell := (R.two_center_parameters hW hd hgap hcard hintercept).2.1
  have hnot : ¬S.IsSaturatedAtomPair i u := by
    intro hpair
    have hz := hpair.high_head_null hW hd hgap hell
    have hhigh := (ae_restrict_iff' (S.hfibers i.val i.property).1).mp hprivate
    have heq : μ ({x | S.ρ x = i.val} ∩ S.H) = μ {x | S.ρ x = i.val} := by
      apply measure_congr
      filter_upwards [hhigh] with x hx
      exact propext ⟨fun h => h.1, fun h => ⟨h, (hx h).1.1.1⟩⟩
    rw [heq] at hz
    exact (S.hfibers i.val i.property).2.1.ne' hz
  have hslack := S.ae_rootChargeRow_lt_one_of_not_saturated i u
    (R.private_atom_ne_heads i r u hp hprivate).2 hW hd hgap hnot
  have hbound := R.private_atom_mass_bound_of_unsaturated_head i r u hru
    hW hd hgap hp hprivate hslack
  have hbalance := R.twoCenter_head_balance r u hru hp
  dsimp only [originalAtomMass]
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem privateDeficit_comm (r u : S.I) (x : Ω) :
    S.twoCenterPrivateDeficit u r x = S.twoCenterPrivateDeficit r u x := by
  have hκ : S.headPairing u r = S.headPairing r u :=
    schurForm_symm (S.normalizedHead u) (S.normalizedHead r)
  simp only [twoCenterPrivateDeficit, hκ]
  ring

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem privateThreshold_comm (r u : S.I) :
    S.twoCenterPrivateThreshold u r = S.twoCenterPrivateThreshold r u := by
  have hκ : S.headPairing u r = S.headPairing r u :=
    schurForm_symm (S.normalizedHead u) (S.normalizedHead r)
  simp only [twoCenterPrivateThreshold, hκ]

private theorem e2_second_private_cover (r u : S.I) (hru : r ≠ u)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hζ : 0 ≤ S.twoCenterPrivateThreshold r u) (L : ℝ)
    (hmax : ∀ k : S.I,
      μ.real (S.twoCenterPrivate u r ∩ {x | S.ρ x = k.val}) ≤ L) :
    S.twoCenterPrivateThreshold r u *
      sourceCoverValue (μ.real (S.twoCenterPrivate u r)) L ≤
      ∫ x in S.twoCenterPrivate u r, S.twoCenterPrivateDeficit r u x ∂μ := by
  have hp' : R.plateau = {u, r} := by simpa only [Finset.pair_comm] using hp
  have hζ' : 0 ≤ S.twoCenterPrivateThreshold u r := by
    rw [privateThreshold_comm]
    exact hζ
  have h := R.e2_private_source_deficit_integral_ge u r hru.symm
    hW hq hdq hgap hglobal hp' hintercept hζ' L hmax
  rw [privateThreshold_comm] at h
  have hdef : (fun x => S.twoCenterPrivateDeficit u r x) =
      S.twoCenterPrivateDeficit r u := by
    funext x
    exact privateDeficit_comm r u x
  rw [← hdef]
  exact h

private theorem e2_entire_source_cover (i r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.twoCenterPrivate r u)
    (hmax : ∀ k : S.I, S.originalAtomMass k ≤ S.originalAtomMass i)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    let B := missingMassCapRadius d c m (S.originalAtomMass i)
    S.twoCenterPrivateThreshold r u *
        sourceCoverValue (μ.real (S.twoCenterPrivate r u))
          (S.originalAtomMass i) +
      S.twoCenterPrivateThreshold r u *
        sourceCoverValue (μ.real (S.twoCenterPrivate u r))
          (B - S.originalAtomMass u) +
      S.headPairing r u * μ.real (S.twoCenterShared r u) ≤
        ∫ x in S.reverseCompulsorySource R.plateau,
          S.twoCenterPrivateDeficit r u x ∂μ := by
  let B := missingMassCapRadius d c m (S.originalAtomMass i)
  have hintercept := hW.e2_intercept_guard hq hdq hgap hglobal
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  have hζ := (R.private_threshold_pos_le_pairing r u hru hW hd hgap hp hintercept).1.le
  obtain ⟨hmax₁, hmax₂, _, _⟩ :=
    R.e2_private_source_fiber_bounds i r u hru hp hprivate hmax
      hW hq hdq hgap hglobal
  have hcover₁ := R.e2_private_source_deficit_integral_ge r u hru
    hW hq hdq hgap hglobal hp hintercept hζ
    (S.originalAtomMass i) hmax₁
  have hcover₂ := R.e2_second_private_cover r u hru hW hq hdq hgap hglobal
    hp hintercept hζ (B - S.originalAtomMass u) hmax₂
  have hsplit := R.entire_source_deficit_integral_eq r u hW hp
  change S.twoCenterPrivateThreshold r u *
      sourceCoverValue (μ.real (S.twoCenterPrivate r u)) (S.originalAtomMass i) +
    S.twoCenterPrivateThreshold r u *
      sourceCoverValue (μ.real (S.twoCenterPrivate u r)) (B - S.originalAtomMass u) +
    S.headPairing r u * μ.real (S.twoCenterShared r u) ≤
      ∫ x in S.reverseCompulsorySource R.plateau,
        S.twoCenterPrivateDeficit r u x ∂μ
  rw [hsplit]
  change S.twoCenterPrivateThreshold r u *
      sourceCoverValue (μ.real (S.twoCenterPrivate r u)) (S.originalAtomMass i) ≤
      ∫ x in S.twoCenterPrivate r u, S.twoCenterPrivateDeficit r u x ∂μ at hcover₁
  linarith [hcover₁, hcover₂]

private theorem e2_private_source_bound_of_capacity (i r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.twoCenterPrivate r u)
    (hmax : ∀ k : S.I, S.originalAtomMass k ≤ S.originalAtomMass i)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcapacity :
      (∫ x in S.reverseCompulsorySource R.plateau,
        S.twoCenterPrivateDeficit r u x ∂μ) +
        S.twoCenterPrivateThreshold r u * (1 - 2 * R.height) ≤
          S.headPairing r u - 2 * (2 * (c - m * d))) :
    let B := missingMassCapRadius d c m (S.originalAtomMass i)
    S.twoCenterPrivateThreshold r u *
      (R.height / 2 + S.originalAtomMass i - B / 2) ≤
        S.headPairing r u - 2 * (2 * (c - m * d)) := by
  let B := missingMassCapRadius d c m (S.originalAtomMass i)
  let A := S.originalAtomMass i
  let t := R.height
  let a₁ := S.originalAtomMass r
  let a₂ := S.originalAtomMass u
  let α₁ := R.sharedReceipt r u
  let α₂ := R.sharedReceipt u r
  let κ := S.headPairing r u
  let ν := 2 * (c - m * d)
  let ζ := S.twoCenterPrivateThreshold r u
  let D₁ := ζ * sourceCoverValue (t - a₁ - α₁) A
  let D₂ := ζ * sourceCoverValue (t - a₂ - α₂) (B - a₂)
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  have hintercept := hW.e2_intercept_guard hq hdq hgap hglobal
  have hparams := R.two_center_parameters hW hd hgap (by rw [hp, Finset.card_pair hru])
    hintercept
  have hreceipts := R.twoCenter_receipt_balances r u hru hp
  have hthreshold := R.private_threshold_pos_le_pairing r u hru hW hd hgap hp hintercept
  have hpeak := R.private_peak_mass_budget i r u hru hW hd hgap hp hintercept hprivate
  obtain ⟨_, _, ha₂B, hBA⟩ := R.e2_private_source_fiber_bounds
    i r u hru hp hprivate hmax hW hq hdq hgap hglobal
  have hthird := R.private_atom_mass_lt_third i r u hru hW hd hgap hp
    hintercept hprivate
  have hBt : B ≤ t := by
    change B < A at hBA
    change A < 1 / 3 at hthird
    have htthird : 1 / 3 < t := hparams.2.2.1
    linarith
  have hsrc := R.e2_entire_source_cover i r u hru hp hprivate hmax
    hW hq hdq hgap hglobal
  have hs₁ : μ.real (S.twoCenterPrivate r u) = t - a₁ - α₁ := by
    have hb := hreceipts.2.2.2.1
    change a₁ + μ.real (S.twoCenterPrivate r u) + α₁ = t at hb
    linarith only [hb]
  have hs₂ : μ.real (S.twoCenterPrivate u r) = t - a₂ - α₂ := by
    have hb := hreceipts.2.2.2.2
    change a₂ + μ.real (S.twoCenterPrivate u r) + α₂ = t at hb
    linarith only [hb]
  have hsum : α₁ + α₂ = μ.real (S.twoCenterShared r u) := hreceipts.2.2.1
  have hD₁ : ζ * sourceCoverValue (t - a₁ - α₁) A ≤ D₁ := le_rfl
  have hD₂ : ζ * sourceCoverValue (t - a₂ - α₂) (B - a₂) ≤ D₂ := le_rfl
  have hcap' : D₁ + D₂ + κ * (α₁ + α₂) + ζ * (1 - 2 * t) ≤ κ - 2 * ν := by
    dsimp only [D₁, D₂, κ, ν, ζ, t, A, B, a₁, a₂, α₁, α₂]
    rw [← hs₁, ← hs₂, hsum]
    linarith only [hsrc, hcapacity]
  exact source_bounds_scalar t a₁ a₂ α₁ α₂ A B κ ν ζ D₁ D₂
    hreceipts.1 hreceipts.2.1 hthreshold.1.le hthreshold.2
    hparams.2.2.2 (by linarith [hpeak, hreceipts.1]) ha₂B hBt
    hD₁ hD₂ hcap'

/-- The actual smooth E2 contact, one original largest private whole atom,
the original partial reverse capacity and the physical source covers imply
the receipt-free two-center scalar lower bound. No capacity, radius, or
source-cover inequality is supplied as a premise. -/
theorem e2_private_source_scalar_lower_bound (i r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val},
      x ∈ S.twoCenterPrivate r u)
    (hmax : ∀ k : S.I, S.originalAtomMass k ≤ S.originalAtomMass i)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    let B := missingMassCapRadius d c m (S.originalAtomMass i)
    S.twoCenterPrivateThreshold r u *
      (R.height / 2 + S.originalAtomMass i - B / 2) ≤
        S.headPairing r u - 2 * (2 * (c - m * d)) := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  have hintercept := hW.e2_intercept_guard hq hdq hgap hglobal
  have hdegree0 := R.e2_mean_head_degree_inner_neg r u hru hW hq hdq
    hgap hglobal hp
  have hcapacity := R.entire_source_deficit_capacity r u hru hW hd hgap hp
    hintercept hdegree0
  change (∫ x in S.reverseCompulsorySource R.plateau,
      S.twoCenterPrivateDeficit r u x ∂μ) +
      S.twoCenterPrivateThreshold r u * (1 - 2 * R.height) ≤
        S.headPairing r u - 2 * (2 * (c - m * d)) at hcapacity
  exact R.e2_private_source_bound_of_capacity i r u hru hp hprivate hmax
    hW hq hdq hgap hglobal hcapacity

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
