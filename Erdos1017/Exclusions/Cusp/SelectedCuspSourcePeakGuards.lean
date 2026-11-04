module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceBudget
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve
public import Erdos1017.SelectedModel.SelectedHeadPeak

/-!
# Guards for the cusp source peak

The original head and the whole source peak form an independent union whose mass
square is paid by the missing density, and the same common peak pays the head
ordering, independent union and strict reserve used by the cusp child payment,
with no endpoint atom.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ} {S : SelectedHighLowStructure W m}

/-- The original head and the whole original source peak form an independent
union. Its original mass square is paid by the original missing density. -/
theorem cusp_source_peak_mass_sq_le_missing (R : S.ReverseRecovery) (r i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource) :
    (S.originalAtomMass r + S.originalAtomMass i) ^ 2 ≤ 1 - 2 * d := by
  let P := {x | S.ρ x = r.val}
  let I := R.cuspSourcePeak i
  have hP : MeasurableSet P := (S.hfibers r.val r.property).1
  have hI : MeasurableSet I := R.measurableSet_cuspSourcePeak i
  have hSource : R.cuspSource = S.reverseCompulsorySource {r} := by rw [cuspSource, hr]
  have hg := R.singleton_retainedSourceGeometry r hW hd hgap hr
  rw [← hSource] at hg
  have hPI : Disjoint P I := hg.disjoint_IC.mono_right inter_subset_left
  have hind : ∀ᵐ p ∂(μ.restrict (P ∪ I)).prod (μ.restrict (P ∪ I)),
      adjacencyKernel W p.1 p.2 = 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' ((hP.union hI).prod (hP.union hI))).mpr
    filter_upwards [hg.zero_II, hg.zero_IC, singleton_zero_II (S := S) i,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hg.zero_IC,
      adjacencyKernel_symm W] with p hPP hPI hII hIP hs hp
    rcases hp.1 with hx | hx <;> rcases hp.2 with hy | hy
    · exact hPP hx hy
    · exact hPI hx hy.1
    · exact hs.trans (hIP hy hx.1)
    · exact hII hx.2 hy.2
  have hsquare := independent_set_mass_sq_le_missing_density W (P ∪ I) (hP.union hI) hind
  rw [measureReal_union hPI hI, hW.density_eq] at hsquare
  change (S.originalAtomMass r + μ.real (R.cuspSourcePeak i)) ^ 2 ≤ _ at hsquare
  rwa [R.cuspSourcePeak_mass_original i hinside] at hsquare

/-- The same original common peak pays the head ordering, independent union
and strict reserve used by the cusp child payment. No endpoint atom is used. -/
theorem cusp_source_peak_guards (R : S.ReverseRecovery) (r i : S.I)
    (k : ℕ) (hk : 4 ≤ k) (hdk : d = (1 - 1 / (k : ℝ) ^ 2) / 2)
    (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hr : R.plateau = {r})
    (hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ R.cuspSource)
    (hpeak : S.IsCommonForwardPeak d c i) :
    S.originalAtomMass r < S.originalAtomMass i ∧
      (S.originalAtomMass r + S.originalAtomMass i) ^ 2 ≤ 1 / (k : ℝ) ^ 2 ∧
      (2 - 2 / (k : ℝ) + m) / (k : ℝ) ^ 2 <
        (2 + m) * (S.originalAtomMass i) ^ 2 := by
  obtain ⟨hd, _, hell, _, hmargin⟩ :=
    hW.cusp_contact_parameters k (by omega) hdk hgap hglobal
  have hri : r ≠ i := by
    intro heq
    subst i
    obtain ⟨x, hx, hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (S.hfibers r.val r.property).2.1.ne' hinside
    have hdis : Disjoint {x | S.ρ x = r.val} R.cuspSource := by
      rw [cuspSource, hr]
      exact S.disjoint_singleton_fiber_source r
    exact Set.disjoint_left.mp hdis hx hs
  obtain ⟨hDelta, j, _, _, hj, hlargest, hreserve, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have hji : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hDelta
  subst j
  have hQi : (S.originalAtomMass i) ^ 2 ≤ ∑' j, (S.originalAtomMass j) ^ 2 := by
    simpa only [Finset.sum_singleton] using Summable.sum_le_tsum (s := {i})
      (fun j _ => sq_nonneg (S.originalAtomMass j)) S.originalAtomMass_sq_summable
  have hweighted := mul_le_mul_of_nonneg_left hQi (show 0 ≤ -m by linarith [hell.1])
  have hmass := R.cusp_source_peak_mass_sq_le_missing r i hW hd hgap hr hinside
  rw [hdk] at hmass
  exact ⟨hlargest r hri, by linarith only [hmass], by nlinarith only [hmargin, hreserve, hweighted]⟩

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
