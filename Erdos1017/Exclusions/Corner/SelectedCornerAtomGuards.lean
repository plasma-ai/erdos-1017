module

public import Erdos1017.Exclusions.Corner.FullSharpCornerPeak
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards

/-!
# Contact guards of corner atoms

Any own corner optimum gives every measurable independent block the strict
contact bonus, with the one-sided benchmark slopes and the `Phi` bound derived,
and each selected atom inherits these guards from its independent fiber.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel

private theorem independent_bonus_of_right_phi {h B c L ell b : ℝ}
    (hh : 0 ≤ h) (hsquare : b ^ 2 ≤ h)
    (hB : h / 2 < B) (hc : B < c) (hL : L < 1) (hle : L ≤ ell) (hell : ell < 1)
    (hphi : Real.sqrt h * (1 - L) / (2 * B - L * h) < 2) :
    b * (1 - ell) < 2 * (2 * c - ell * h) := by
  have hdenL : 0 < 2 * B - L * h := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - L by linarith) hh]
  have hden : 0 < 2 * B - ell * h := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ell by linarith) hh]
  have hmono : (1 - ell) * (2 * B - L * h) ≤ (1 - L) * (2 * B - ell * h) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ 2 * B - h by linarith)]
  have hquotient : Real.sqrt h * (1 - ell) / (2 * B - ell * h) ≤
      Real.sqrt h * (1 - L) / (2 * B - L * h) := by
    apply (div_le_div_iff₀ hden hdenL).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg h)]
  have hstrict := (div_lt_iff₀ hden).mp (hquotient.trans_lt hphi)
  have hroot : b ≤ Real.sqrt h := by
    nlinarith [Real.sq_sqrt hh, Real.sqrt_nonneg h]
  have hbound := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 1 - ell by linarith)
  nlinarith only [hstrict, hbound, hc]

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m : ℝ}

/-- Any actual own corner optimum gives every measurable independent block
the strict contact bonus. The actual one-sided benchmark slopes and Phi
bound are derived; no smooth derivative or transferred multiplier is used. -/
theorem FullStationaryClass.corner_independent_set_contact_guards
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (I : Set Ω) (hI : MeasurableSet I)
    (hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), adjacencyKernel W p.1 p.2 = 0) :
    -m ∈ Ioo (1 / 2 : ℝ) 1 ∧ 0 < 2 * (c - m * d) + m ∧
      (μ.real I) ^ 2 ≤ 1 - 2 * d ∧
      μ.real I * (1 + m) < 2 * (2 * (c - m * d) + m) ∧
      μ.real I * (1 + m) / (2 * (c - m * d) + m) < 2 := by
  obtain ⟨hinterval, _, _, _⟩ := hW.corner_contact_parameters hd hgap he heq hglobal
  have hell : -m ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [hinterval.1, hinterval.2]
  have hbox := (Benchmark.crossing_contact_location he heq).1
  have hmid : d ∈ Ioo (3 / 8 : ℝ) (21 / 50) := by
    constructor <;> linarith [hbox.1, hbox.2]
  obtain ⟨L, hright, _, hL, hB, hphi⟩ := Benchmark.benchmark_head_count_guards hmid
  have hleft := (Benchmark.benchmark_corner_one_sided_derivatives hd he heq).1
  have hbracket := hW.multiplier_mem_one_sided_slopes_of_strict_gap hd hgap hglobal hleft hright
  have hle : L ≤ -m := by linarith [hbracket.2]
  have hsquare := independent_set_mass_sq_le_missing_density W I hI hind
  rw [hW.density_eq] at hsquare
  have hphi' : Real.sqrt (1 - 2 * d) * (1 - L) /
      (2 * benchmark d - L * (1 - 2 * d)) < 2 := by
    convert hphi using 1
    ring
  have hbonus : μ.real I * (1 + m) < 2 * (2 * (c - m * d) + m) := by
    have h := independent_bonus_of_right_phi (show 0 ≤ 1 - 2 * d by linarith [hd.2])
      hsquare (by linarith only [hB]) hgap hL hle hell.2 hphi'
    convert h using 1 <;> ring
  have hgamma : 0 < 2 * (c - m * d) + m :=
    (hW.strict_gap_structure hd hgap).gamma_pos
  exact ⟨hell, hgamma, hsquare, hbonus, (div_lt_iff₀ hgamma).mpr (by linarith only [hbonus])⟩

/-- Each original selected atom inherits the corner guards from its actual
independent fiber. No peak, saturation partner or region positivity is assumed. -/
theorem SelectedHighLowStructure.corner_atom_contact_guards
    (S : SelectedHighLowStructure W m) (r : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Icc Benchmark.epsilonC Benchmark.epsilonD)
    (heq : Benchmark.twoHeadCurve (1 / 2 - d) = Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    -m ∈ Ioo (1 / 2 : ℝ) 1 ∧ 0 < 2 * (c - m * d) + m ∧
      (S.originalAtomMass r) ^ 2 ≤ 1 - 2 * d ∧
      S.originalAtomMass r * (1 + m) < 2 * (2 * (c - m * d) + m) ∧
      S.originalAtomMass r * (1 + m) / (2 * (c - m * d) + m) < 2 :=
  hW.corner_independent_set_contact_guards hd hgap he heq hglobal
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 (S.hfibers r.val r.property).2.2.1

end Erdos1017.CappedModel
