module

public import Erdos1017.Exclusions.Cusp.FullSplitCuspContact
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards

/-!
# Contact guards for atoms at a reciprocal cusp

One-sided reciprocal contact gives the model's own strict slope bracket and
positive intercept with no smooth derivative at the cusp, every measurable
independent block of the cusp optimum has the strict signed bonus, and every
selected atom receives the same one-sided bracket and strict signed ratio.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Genuine one-sided reciprocal contact gives the displayed model's
own strict slope bracket and positive intercept. No smooth derivative is
assigned at the cusp, including its first case k=3. -/
theorem FullStationaryClass.cusp_contact_parameters
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (k : ℕ) (hk : 3 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    d ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧
      -m ∈ Ioo (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) (2 - 2 / (k : ℝ)) ∧
      -m ∈ Ioo (5 / 6 : ℝ) 2 ∧ 0 < 2 * (c - m * d) + m ∧
      (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 < 2 * (c - m * d) + m := by
  obtain ⟨hslope, hupper⟩ := hW.split_cusp_strict_slope k hk hdk hgap hglobal
  obtain ⟨hmargin, hfloor⟩ := hW.split_cusp_gamma_margin k hk hdk hgap hglobal
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdk]
    have hband := Benchmark.split_cusp_mem_band k hk
    exact ⟨by linarith [hband.1, Benchmark.epsilonStar_lt_tenth], hband.2⟩
  have hlower : 5 / 6 < -m := by
    by_cases hk3 : k = 3
    · subst k
      norm_num at hslope
      exact hslope.1
    · have hlow := Benchmark.split_cusp_lower_slope_ge_eleven_tenths k (by omega)
      linarith [hslope.1]
  exact ⟨hd, hslope, ⟨hlower, hslope.2.trans hupper⟩, hmargin.trans hfloor, hfloor⟩

/-- Any measurable independent block of this actual cusp optimum has
the strict signed bonus. The k=3 comparison uses its exact intercept;
for k≥4 the actual own penalty exceeds one and the numerator is nonpositive. -/
theorem FullStationaryClass.cusp_independent_set_contact_guards
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (k : ℕ) (hk : 3 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (I : Set Ω) (hI : MeasurableSet I)
    (hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I), adjacencyKernel W p.1 p.2 = 0) :
    -m ∈ Ioo (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) (2 - 2 / (k : ℝ)) ∧
      -m ∈ Ioo (5 / 6 : ℝ) 2 ∧ 0 < 2 * (c - m * d) + m ∧
      (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 < 2 * (c - m * d) + m ∧
      (μ.real I) ^ 2 ≤ 1 / (k : ℝ) ^ 2 ∧ μ.real I ≤ 1 / (k : ℝ) ∧
      μ.real I * (1 + m) < 2 * (2 * (c - m * d) + m) ∧
      μ.real I * (1 + m) / (2 * (c - m * d) + m) < 2 := by
  obtain ⟨_, hslope, hell, hgamma, hfloor⟩ := hW.cusp_contact_parameters k hk hdk hgap hglobal
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hsq := independent_set_mass_sq_le_missing_density W I hI hind
  rw [hW.density_eq, hdk] at hsq
  have hsquare : (μ.real I) ^ 2 ≤ 1 / (k : ℝ) ^ 2 := by linarith only [hsq]
  have hrecip : 0 ≤ 1 / (k : ℝ) := by positivity
  have hmass : μ.real I ≤ 1 / (k : ℝ) := by
    apply (sq_le_sq₀ measureReal_nonneg hrecip).mp
    simpa only [one_div_pow] using hsquare
  have hbonus : μ.real I * (1 + m) < 2 * (2 * (c - m * d) + m) := by
    by_cases hdelta : 0 ≤ 1 + m
    · by_cases hk3 : k = 3
      · subst k
        norm_num at hmass hfloor
        have hprod := mul_nonneg (sub_nonneg.mpr hmass) hdelta
        nlinarith only [hprod, hfloor, hell.1]
      · have hlow := Benchmark.split_cusp_lower_slope_ge_eleven_tenths k (by omega)
        have hpenalty : 1 < -m := by linarith [hslope.1]
        linarith
    · have hnonpos := mul_nonpos_of_nonneg_of_nonpos (measureReal_nonneg (μ := μ) (s := I))
        (le_of_not_ge hdelta)
      linarith
  exact ⟨hslope, hell, hgamma, hfloor, hsquare, hmass, hbonus,
    (div_lt_iff₀ hgamma).mpr (by linarith only [hbonus])⟩

end Erdos1017.CappedModel

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- Every original selected atom receives the same true one-sided cusp
bracket and strict signed ratio from its actual independent square. -/
theorem cusp_atom_contact_guards (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (k : ℕ) (hk : 3 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    -m ∈ Ioo (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) (2 - 2 / (k : ℝ)) ∧
      -m ∈ Ioo (5 / 6 : ℝ) 2 ∧ 0 < 2 * (c - m * d) + m ∧
      (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 < 2 * (c - m * d) + m ∧
      (S.originalAtomMass r) ^ 2 ≤ 1 / (k : ℝ) ^ 2 ∧ S.originalAtomMass r ≤ 1 / (k : ℝ) ∧
      S.originalAtomMass r * (1 + m) < 2 * (2 * (c - m * d) + m) ∧
      S.originalAtomMass r * (1 + m) / (2 * (c - m * d) + m) < 2 :=
  hW.cusp_independent_set_contact_guards k hk hdk hgap hglobal
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 (S.hfibers r.val r.property).2.2.1

end Erdos1017.CappedModel.SelectedHighLowStructure
