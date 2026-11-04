module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeLowSlopePeak
public import Erdos1017.Exclusions.Common.CliqueStarVariation

/-!
# The missing region of the low-slope third-cusp peak

The region `cuspThreeMissingRegion` is the entire outside missing region of the
third-cusp peak; it is measurable and equals the whole-row missing set of the
full-flow redirection, and for a nonuniversal common peak it is positive with
mass below `2/39`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The entire original outside missing region of the third-cusp peak. -/
def cuspThreeMissingRegion (S : SelectedHighLowStructure W m) (i : S.I) : Set Ω :=
  {x | S.ρ x = i.val}ᶜ \ S.rootNeighborhood i

theorem measurableSet_cuspThreeMissingRegion (S : SelectedHighLowStructure W m) (i : S.I) :
    MeasurableSet (S.cuspThreeMissingRegion i) :=
  (S.hfibers i.val i.property).1.compl.diff (S.measurableSet_rootNeighborhood i)

/-- The literal exterior-neighborhood complement is exactly the original
whole-row missing set used by the full-flow redirection construction. -/
theorem cuspThreeMissingRegion_eq_missingSet (S : SelectedHighLowStructure W m) (i : S.I) :
    S.cuspThreeMissingRegion i = wholeFiberMissingSet S.ρ i.val := by
  ext x
  change (S.ρ x ≠ i.val ∧ ¬(S.ρ x ≠ i.val ∧ 0 < i.val x)) ↔
    S.ρ x ≠ i.val ∧ i.val x ≤ 0
  constructor
  · intro hx
    exact ⟨hx.1, le_of_not_gt (fun hp => hx.2 ⟨hx.1, hp⟩)⟩
  · intro hx
    exact ⟨hx.1, fun hp => not_lt_of_ge hx.2 hp.2⟩

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {d c : ℝ}

/-- A nonuniversal original common peak at the low-slope third cusp has a
positive entire LOW missing region of mass below 2/39. One actual full
forward flow sends every such source uniformly into the original peak,
while every other source column avoids it. -/
theorem cusp_three_low_slope_missing_region (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1)) :
    0 < μ.real (S.cuspThreeMissingRegion i) ∧
      (∀ᵐ x ∂μ.restrict (S.cuspThreeMissingRegion i), x ∈ S.L ∧
        adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x < wholeRowDegree i.val) ∧
      S.originalAtomMass i + μ.real (S.cuspThreeMissingRegion i) < 1 / 3 ∧
      μ.real (S.cuspThreeMissingRegion i) < 2 / 39 ∧
      ∃ (q : Ω × Ω → ℝ) (_hq : S.IsFullForwardFlow q),
        (∀ p, p.2 ∈ S.cuspThreeMissingRegion i → q p =
          {x | S.ρ x = i.val}.indicator (fun _ => 1 / S.originalAtomMass i) p.1) ∧
        (∀ᵐ p ∂μ.prod μ, p.2 ∉ S.cuspThreeMissingRegion i →
          q p ≠ 0 → S.ρ p.1 ≠ i.val) ∧
        S.forwardClassMass q i = S.originalAtomMass i + μ.real (S.cuspThreeMissingRegion i) := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  obtain ⟨_, hfloor, _⟩ := S.cusp_three_low_slope_peak_bounds i hdk hW hgap hglobal hell hpeak
  obtain ⟨hDelta, j, hA, hside, hj, _, _, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  have hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H := by
    rcases hside with hH | hN
    · exact hH
    · exact False.elim (hnonuniv (S.neutral_atom_adjacency i hW hd hgap hN))
  let J := S.cuspThreeMissingRegion i
  have hJpos : 0 < μ.real J := by
    by_contra hn
    have hnull : μ J = 0 := (measureReal_eq_zero_iff (measure_ne_top μ _)).mp
      (le_antisymm (le_of_not_gt hn) measureReal_nonneg)
    have hnot : ∀ᵐ x ∂μ, x ∉ J := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hnull
    apply hnonuniv
    filter_upwards [S.ae_original_root_adjacency i hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae hnot] with p hp hj hi
    rw [hp hi]
    by_cases hsame : S.ρ p.2 = i.val
    · have hn : p.2 ∉ S.rootNeighborhood i := fun hn => hn.1 hsame
      simp only [hsame, hn, ite_true, ite_false]
    · have hn : p.2 ∈ S.rootNeighborhood i := by
        by_contra hn
        exact hj ⟨hsame, hn⟩
      simp only [hsame, hn, ite_true, ite_false]
  have hlow : ∀ᵐ x ∂μ.restrict J, x ∈ S.L ∧
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x < wholeRowDegree i.val := by
    dsimp [J]
    rw [S.cuspThreeMissingRegion_eq_missingSet i]
    exact S.ae_missingRegion_low_degree_lt hW i.val i.property hhigh
  obtain ⟨hbase, havoid⟩ := S.highAtomAvoidingFlow_properties hW hd hgap i hhigh
  let q := S.atomRedirect i.val (S.highAtomAvoidingFlow i)
  have hq : S.IsFullForwardFlow q := hbase.atomRedirect_of_stationary hW i.val i.property hhigh
  have hmass : S.forwardClassMass q i = S.originalAtomMass i + μ.real J := by
    rw [S.forwardClassMass_eq_fiber]
    dsimp [q, J]
    rw [S.cuspThreeMissingRegion_eq_missingSet i]
    exact hbase.atomRedirect_endpoint_mass hW i.val i.property hhigh
  have hp := hq.classMass_properties
  have hs : Summable (fun j => (S.forwardClassMass q j) ^ 2) :=
    hp.2.1.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => by
      nlinarith only [(hp.1 j).1, (hp.1 j).2])
  have hsingle := hs.le_tsum i (fun _ _ => sq_nonneg _)
  rw [← hq.missing_density_eq_classMass_sq hW hd hgap, hmass] at hsingle
  have hdensity := hq.endpoint_density_gt hW hd hgap
  have hsum : S.originalAtomMass i + μ.real J < 1 / 3 := by
    rw [hdk] at hdensity
    nlinarith only [hsingle, hdensity, hA, hJpos]
  have hsmall : μ.real J < 2 / 39 := by linarith only [hsum, hfloor]
  refine ⟨hJpos, hlow, hsum, hsmall, q, hq, ?_, ?_, hmass⟩
  · intro p hp
    change MissingFlow.redirect μ (S.highAtomAvoidingFlow i) {x | S.ρ x = i.val}
      (wholeFiberMissingSet S.ρ i.val) p = _
    have hp' : p.2 ∈ wholeFiberMissingSet S.ρ i.val := by
      rwa [← S.cuspThreeMissingRegion_eq_missingSet i]
    simp only [MissingFlow.redirect, hp', ite_true, originalAtomMass]
  · filter_upwards [havoid] with p hp hn hne
    apply hp
    have hn' : p.2 ∉ wholeFiberMissingSet S.ρ i.val := by
      rwa [← S.cuspThreeMissingRegion_eq_missingSet i]
    simpa only [q, atomRedirect, MissingFlow.redirect, hn', ite_false] using hne

end Erdos1017.CappedModel.SelectedHighLowStructure
