module

public import Erdos1017.Exclusions.Cusp.SelectedCuspWholeSourceInventory
public import Erdos1017.Exclusions.Common.BoundedKernelSupportBound
public import Erdos1017.Benchmark.BenchmarkDenseHeadCountGuards
public import Erdos1017.Exclusions.Cusp.BenchmarkSplitCubicEnvelopes

/-!
# Range of the full cusp endpoint

The support bound and the same original reverse budget put the full cusp
endpoint in the dense split band, with a positive normalized split gap and
inside the common coarse range needed by both reciprocal-cusp peak branches.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- The actual support bound and same original reverse budget put the
full cusp endpoint in the genuine dense split band. -/
theorem cusp_endpoint_dense_split (R : S.ReverseRecovery) (k : ℕ) (hk : 6 ≤ k)
    (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    density R.isFullReverseFlow.endpoint ∈ Ioc (21 / 50 : ℝ) (1 / 2) ∧
      objective R.isFullReverseFlow.endpoint ≤
        Benchmark.splitValue (Real.sqrt (1 - 2 * density R.isFullReverseFlow.endpoint)) := by
  obtain ⟨hd, hslope, _, hgamma, _⟩ := hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  let := R.isFullReverseFlow.endpoint_probability
  have hmem := density_mem R.isFullReverseFlow.endpoint
  have hcost := fullFeasible_objective_le_densityLimit R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full)
  have hsupport := FractionalGraph.densityLimit_add_density_le hmem
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hL := Benchmark.split_cusp_lower_slope_ge_eleven_tenths k (by omega)
  have hlo : 19 / 15 < -m := by
    have hk6 : (6 : ℝ) ≤ k := by exact_mod_cast hk
    have h₁ : 2 / (k : ℝ) ≤ 1 / 3 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    have h₂ : 2 / ((k : ℝ) + 1) ≤ 2 / 7 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith [hslope.1]
  have hprod := mul_nonneg (show 0 ≤ -m - 19 / 15 by linarith)
    (show 0 ≤ 1 - 2 * density R.isFullReverseFlow.endpoint by linarith [hmem.2])
  have hdense : 21 / 50 < density R.isFullReverseFlow.endpoint := by nlinarith
  have hpart := R.isFullReverseFlow.endpoint_partition_support hW hd hgap
  have hMP := objective_le_benchmark_of_partition_support R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.atomicDustPartLabel hpart
  rw [Benchmark.benchmark_eq_split_of_dense ⟨hdense.le, hmem.2⟩] at hMP
  exact ⟨⟨hdense, hmem.2⟩, hMP⟩

private theorem cubic_range {k ell x : ℝ} (hk : 6 ≤ k)
    (hell : 2 - 2 / k - 2 / (k + 1) < ell) (_hx : 0 ≤ x)
    (hr : x / k ∈ Icc (0 : ℝ) 1)
    (hgap : 0 < k ^ 2 * Benchmark.splitValue (x / k) - (1 - 1 / k) - ell * (x ^ 2 - 1) / 2) :
    x < 2 := by
  have hk0 : 0 < k := by linarith
  let D := k * (1 - ell / 2)
  have hD : D < 2 := by
    have hp := mul_lt_mul_of_pos_left hell hk0
    have he : k * (2 - 2 / k - 2 / (k + 1)) = 2 * k - 2 - 2 * k / (k + 1) := by
      field_simp
    rw [he] at hp
    have hr : k / (k + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    dsimp [D]
    simp only [div_eq_mul_inv] at hp hr ⊢
    linarith
  have hcurve := Benchmark.splitValue_le_seven_eighths hr
  have hs := mul_le_mul_of_nonneg_left hcurve (sq_nonneg k)
  have hp : 0 < k ^ 2 * ((x / k) ^ 2 * (1 - 7 / 8 * (x / k))) -
      (1 - 1 / k) - ell * (x ^ 2 - 1) / 2 := lt_of_lt_of_le hgap (by linarith)
  have he : k * (k ^ 2 * ((x / k) ^ 2 * (1 - 7 / 8 * (x / k))) -
      (1 - 1 / k) - ell * (x ^ 2 - 1) / 2) = D * (x ^ 2 - 1) + 1 - 7 / 8 * x ^ 3 := by
    dsimp [D]
    field_simp
    ring
  have hpos := mul_pos hk0 hp
  rw [he] at hpos
  by_contra hn
  have hx2 : 2 ≤ x := le_of_not_gt hn
  have hq : 0 ≤ 7 * x ^ 2 - 2 * x - 4 := by nlinarith [sq_nonneg (x - 2)]
  have hmul := mul_nonneg (sub_nonneg.mpr hx2) hq
  have hDmul := mul_pos (sub_pos.mpr hD) (show 0 < x ^ 2 - 1 by nlinarith)
  nlinarith

/-- The actual endpoint has a positive normalized split gap and lies in
the common coarse range needed by both reciprocal-cusp peak branches. -/
theorem cusp_endpoint_normalized_range (R : S.ReverseRecovery) (k : ℕ) (hk : 6 ≤ k)
    (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    let H := 1 - 2 * density R.isFullReverseFlow.endpoint
    let x := (k : ℝ) * Real.sqrt H
    0 ≤ x ∧ x < 2 ∧ H < 4 / (k : ℝ) ^ 2 ∧ R.height < 2 / (k : ℝ) ∧
      0 < (k : ℝ) ^ 2 * Benchmark.splitValue (x / k) - (1 - 1 / (k : ℝ)) -
        (-m) * (x ^ 2 - 1) / 2 := by
  obtain ⟨hd, hslope, _, _, _⟩ := hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  have hdense := R.cusp_endpoint_dense_split k hk hdk hW hgap hglobal
  let := R.isFullReverseFlow.endpoint_probability
  let H := 1 - 2 * density R.isFullReverseFlow.endpoint
  let x := (k : ℝ) * Real.sqrt H
  have hk0 : (0 : ℝ) < k := by positivity
  have hH : 0 ≤ H := by dsimp [H]; linarith [hdense.1.2]
  have hx0 : 0 ≤ x := by positivity
  have hxdiv : x / k = Real.sqrt H := by dsimp [x]; field_simp
  have hxsq : x ^ 2 = (k : ℝ) ^ 2 * H := by dsimp [x]; rw [mul_pow, Real.sq_sqrt hH]
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have hE := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hvalue : benchmark d = ((k : ℝ) - 1) / (k : ℝ) ^ 3 := by
    have hband := Benchmark.split_cusp_mem_band k (by omega : 3 ≤ k)
    have hs : Real.sqrt (1 - 2 * d) = 1 / (k : ℝ) := by
      rw [hdk]
      have he : 1 - 2 * ((1 - 1 / (k : ℝ) ^ 2) / 2) = (1 / (k : ℝ)) ^ 2 := by ring
      rw [he, Real.sqrt_sq (by positivity)]
    rw [(Benchmark.benchmark_split_eventually (hdk ▸ hband)).eq_of_nhds, hs]
    exact Benchmark.splitValue_reciprocal k (by omega)
  have hscaled := mul_lt_mul_of_pos_left (show ((k : ℝ) - 1) / (k : ℝ) ^ 3 < c by
    rwa [← hvalue]) (sq_pos_of_pos hk0)
  have hbase : (k : ℝ) ^ 2 * (((k : ℝ) - 1) / (k : ℝ) ^ 3) = 1 - 1 / (k : ℝ) := by
    field_simp
  rw [hbase] at hscaled
  rw [hdk] at hbudget
  have hgap' : 0 < (k : ℝ) ^ 2 * Benchmark.splitValue (x / k) - (1 - 1 / (k : ℝ)) -
      (-m) * (x ^ 2 - 1) / 2 := by
    rw [hxdiv, hxsq]
    have hp := mul_nonneg (sq_nonneg (k : ℝ))
      (show 0 ≤ Benchmark.splitValue (Real.sqrt H) - c - (-m) * (H - 1 / (k : ℝ) ^ 2) / 2 by
        dsimp [H] at *
        nlinarith [hdense.2])
    field_simp at hp
    nlinarith
  have hr : x / k ∈ Icc (0 : ℝ) 1 := by
    rw [hxdiv]
    refine ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one).mpr ?_⟩
    dsimp [H]
    linarith [(density_mem R.isFullReverseFlow.endpoint).1]
  have hx2 := cubic_range (by exact_mod_cast hk) hslope.1 hx0 hr hgap'
  have hHlt : H < 4 / (k : ℝ) ^ 2 := (lt_div_iff₀ (sq_pos_of_pos hk0)).mpr (by nlinarith)
  have hheight : R.height < 2 / (k : ℝ) := by
    have hb := R.isFullReverseFlow.plateau_mass_bounds hW hd hgap R.plateau R.height
      (fun r hr => (R.classMass_eq_iff hW r).mpr hr)
    obtain ⟨r, hr⟩ := R.cusp_plateau_singleton k (by omega) hdk hW hgap hglobal
    simp only [hr, Finset.card_singleton, Nat.cast_one, one_mul] at hb
    have hsq : R.height ^ 2 < (2 / (k : ℝ)) ^ 2 := by
      rw [div_pow]
      norm_num
      exact hb.2.trans_lt hHlt
    exact (sq_lt_sq₀ R.height_pos.le (by positivity)).mp hsq
  exact ⟨hx0, hx2, hHlt, hheight, hgap'⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
