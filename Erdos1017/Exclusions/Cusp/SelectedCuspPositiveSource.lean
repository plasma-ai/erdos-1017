module

public import Erdos1017.Exclusions.Cusp.MultipartiteCuspCap
public import Erdos1017.Exclusions.Cusp.SelectedCuspAtomGuards
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedOneCenterSourceCredit

/-!
# One center and a positive source for the cusp recovery

Every recovery at an original reciprocal cusp has one center and a positive
entire source with positive adjacency integral: the cusp slope and plateau
budget force a single center, and a zero source edge integral contradicts the
capped endpoint cost. The selected cusp constructs this recovery with no
supplied plateau or source certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

namespace ReverseRecovery

/-- The actual cusp slope and physical plateau budget force this same
recovery to have one original center. -/
theorem cusp_plateau_singleton (R : S.ReverseRecovery) (k : ℕ) (hk : 4 ≤ k)
    (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    ∃ r : S.I, R.plateau = {r} := by
  obtain ⟨hd, hslope, _, _, _⟩ := hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  have hL := Benchmark.split_cusp_lower_slope_ge_eleven_tenths k hk
  have hm : 1 < -m := by linarith [hslope.1]
  have hcard := R.card_lt_two_div_neg_multiplier hW hd hgap
  have hmul := (lt_div_iff₀ (by linarith : 0 < -m)).mp hcard
  have hnatpos := R.plateau_nonempty.card_pos
  have hreal : (R.plateau.card : ℝ) < 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) R.plateau.card]
  have hnat : R.plateau.card < 2 := by exact_mod_cast hreal
  exact Finset.card_eq_one.mp (by omega)

private theorem height_le_reciprocal_of_zero_source (R : S.ReverseRecovery)
    (r : S.I) (hr : R.plateau = {r}) (k : ℕ) (hk : 4 ≤ k)
    (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : (∫ p in (S.reverseCompulsorySource R.plateau) ×ˢ
      (S.reverseCompulsorySource R.plateau), adjacencyKernel W p.1 p.2 ∂μ.prod μ) = 0) :
    R.height ≤ 1 / (k : ℝ) := by
  let P := {x | S.ρ x = r.val}
  let C := S.reverseCompulsorySource R.plateau
  have hP : MeasurableSet P := (S.hfibers r.val r.property).1
  have hC : MeasurableSet C := R.measurableSet_source
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  have hSource : C = S.reverseCompulsorySource {r} := by dsimp [C]; rw [hr]
  rw [← hSource] at hg
  have hi : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using KernelOperator.integrable_kernel_bilinear
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hCC : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ C → adjacencyKernel W p.1 p.2 = 0 := by
    have he := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun p : Ω × Ω => (adjacency_moment_mem W p).1))
      hi.integrableOn).mp hzero
    exact ((ae_restrict_iff' (hC.prod hC)).mp he).mono (fun _ hp hx hy => hp ⟨hx, hy⟩)
  have hind : ∀ᵐ p ∂(μ.restrict (P ∪ C)).prod (μ.restrict (P ∪ C)),
      adjacencyKernel W p.1 p.2 = 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' ((hP.union hC).prod (hP.union hC))).mpr
    filter_upwards [hg.zero_II, hg.zero_IC, hCC,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.zero_IC,
      adjacencyKernel_symm W] with p hPP hPC hCC hCP hs hp
    rcases hp.1 with hx | hx <;> rcases hp.2 with hy | hy
    · exact hPP hx hy
    · exact hPC hx hy
    · exact hs.trans (hCP hy hx)
    · exact hCC hx hy
  have hsquare := independent_set_mass_sq_le_missing_density W (P ∪ C) (hP.union hC) hind
  rw [measureReal_union hg.disjoint_IC hC, hW.density_eq, hdk] at hsquare
  have hheight := R.singleton_height_eq_mass_add_source r hr
  rw [← hSource] at hheight
  change R.height = μ.real P + μ.real C at hheight
  rw [← hheight] at hsquare
  have hrecip : 0 ≤ 1 / (k : ℝ) := by positivity
  have he : 1 - 2 * ((1 - 1 / (k : ℝ) ^ 2) / 2) = (1 / (k : ℝ)) ^ 2 := by
    rw [one_div_pow]
    ring
  rw [he] at hsquare
  have hsq : R.height ^ 2 ≤ (1 / (k : ℝ)) ^ 2 := hsquare
  exact (sq_le_sq₀ R.height_pos.le hrecip).mp hsq

/-- A zero entire-source edge integral contradicts the actual capped
endpoint cost and same recovery budget; no stationarity is assigned to it. -/
theorem cusp_source_edge_integral_pos (R : S.ReverseRecovery) (k : ℕ) (hk : 4 ≤ k)
    (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    0 < ∫ p in (S.reverseCompulsorySource R.plateau) ×ˢ (S.reverseCompulsorySource R.plateau),
      adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
  obtain ⟨hd, hslope, _, _, _⟩ := hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  obtain ⟨r, hr⟩ := R.cusp_plateau_singleton k hk hdk hW hgap hglobal
  have hnonneg : 0 ≤ ∫ p in (S.reverseCompulsorySource R.plateau) ×ˢ
      (S.reverseCompulsorySource R.plateau), adjacencyKernel W p.1 p.2 ∂μ.prod μ :=
    integral_nonneg (fun p => (adjacency_moment_mem W p).1)
  by_contra hpos
  have hzero := le_antisymm (le_of_not_gt hpos) hnonneg
  have hcap := R.height_le_reciprocal_of_zero_source r hr k hk hdk hW hd hgap hzero
  let ν := missingFlowEndpointLaw μ R.flow
  let := R.isFullReverseFlow.endpoint_probability
  let : NullSingletonClass ν := by
    change NullSingletonClass (μ.withDensity _)
    infer_instance
  let : Countable S.I := S.hI.to_subtype
  have hmass : MultipartiteClassMasses.classMass ν S.collapsedPartLabel r = R.height :=
    (R.classMass_eq_iff hW r).mpr (by rw [hr]; exact Finset.mem_singleton_self r)
  have hcost := MultipartiteClassMasses.objective_le_cusp_cap R.isFullReverseFlow.endpoint
    (R.isFullReverseFlow.endpoint_fullFeasible hW.full) S.collapsedPartLabel S.measurable_collapsedPartLabel
    (by
      filter_upwards [R.isFullReverseFlow.endpoint_collapsed_support hW hd hgap] with p hp
      split_ifs at hp ⊢ <;> exact hp)
    r (hmass ▸ R.height_pos) (by
      intro j
      rw [hmass]
      exact R.classMass_le hW j) k hk (hmass ▸ hcap)
  have hbudget := R.isFullReverseFlow.endpoint_budget hW
  have henergy := R.isFullReverseFlow.energy_nonnegative hW hd hgap
  have hdrop := R.isFullReverseFlow.endpoint_density_lt hW hd hgap
  have hvalue : benchmark d = ((k : ℝ) - 1) / (k : ℝ) ^ 3 := by
    have hband : d ∈ Ioo (1 / 2 - Benchmark.epsilonStar) (1 / 2) := by
      rw [hdk]
      exact Benchmark.split_cusp_mem_band k (by omega)
    have hsqrt : Real.sqrt (1 - 2 * d) = 1 / (k : ℝ) := by
      rw [hdk]
      have he : 1 - 2 * ((1 - 1 / (k : ℝ) ^ 2) / 2) = (1 / (k : ℝ)) ^ 2 := by ring
      rw [he, Real.sqrt_sq (by positivity)]
    rw [(Benchmark.benchmark_split_eventually hband).eq_of_nhds, hsqrt]
    exact Benchmark.splitValue_reciprocal k (by omega)
  have hcredit := mul_pos (sub_pos.mpr hslope.1) (sub_pos.mpr hdrop)
  rw [hvalue] at hgap
  rw [hdk] at hbudget hdrop hcredit
  nlinarith

/-- Every actual recovery at an original reciprocal cusp has one center
and a positive entire source with positive internal adjacency integral. -/
theorem cusp_positive_source_reduction (R : S.ReverseRecovery) (k : ℕ) (hk : 4 ≤ k)
    (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    ∃ r : S.I, R.plateau = {r} ∧ 0 < μ.real (S.reverseCompulsorySource R.plateau) ∧
      0 < ∫ p in (S.reverseCompulsorySource R.plateau) ×ˢ (S.reverseCompulsorySource R.plateau),
        adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
  obtain ⟨r, hr⟩ := R.cusp_plateau_singleton k hk hdk hW hgap hglobal
  have he := R.cusp_source_edge_integral_pos k hk hdk hW hgap hglobal
  have hmass : 0 < μ.real (S.reverseCompulsorySource R.plateau) := by
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    intro hz
    have hnull : μ.prod μ ((S.reverseCompulsorySource R.plateau) ×ˢ
        (S.reverseCompulsorySource R.plateau)) = 0 := by
      rw [Measure.prod_prod, hz, zero_mul]
    have hi : (∫ p in (S.reverseCompulsorySource R.plateau) ×ˢ
        (S.reverseCompulsorySource R.plateau), adjacencyKernel W p.1 p.2 ∂μ.prod μ) = 0 := by
      rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure]
    linarith
  exact ⟨r, hr, hmass, he⟩

end ReverseRecovery

/-- The actual selected cusp constructs the recovery and all positive
source data, with no supplied plateau or source certificate. -/
theorem exists_cusp_positive_source_recovery (S : SelectedHighLowStructure W m)
    (k : ℕ) (hk : 4 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W)) :
    ∃ (R : S.ReverseRecovery) (r : S.I), R.plateau = {r} ∧
      0 < μ.real (S.reverseCompulsorySource R.plateau) ∧
      0 < ∫ p in (S.reverseCompulsorySource R.plateau) ×ˢ (S.reverseCompulsorySource R.plateau),
        adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
  have hd := (hW.cusp_contact_parameters k (by omega) hdk hgap hglobal).1
  obtain ⟨R⟩ := S.exists_reverseRecovery hW hd hgap
  obtain ⟨r, hr, hmass, he⟩ := R.cusp_positive_source_reduction k hk hdk hW hgap hglobal
  exact ⟨R, r, hr, hmass, he⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
