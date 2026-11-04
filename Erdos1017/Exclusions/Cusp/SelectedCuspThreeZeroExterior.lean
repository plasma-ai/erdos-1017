module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredZeroExteriorCounts
public import Erdos1017.Exclusions.Cusp.SelectedCuspAtomGuards

/-!
# The `R`-null zero-body case with no exterior atom

The third-cusp `R`-null boundary with no exterior atom is impossible; its
constructed integer optimum receives its own cusp slope and independent-root
mass bound (`no_cusp_three_zero_body_zero_exterior`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem no_integer_row_above_two_thirds {j : ℕ} {b e ell : ℝ}
    (hj : 2 ≤ j) (hb : 0 < b) (hell : 2 / 3 < ell)
    (hfirst : ((j : ℝ) - 1) * b ≤ e)
    (hrow : b * (1 - 2 / ((j : ℝ) + 1)) =
      e * (ell - 2 / ((j : ℝ) * ((j : ℝ) + 1)))) : False := by
  have hJ : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hJ0 : (0 : ℝ) < j := by linarith
  have hJ1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hden : (0 : ℝ) < (j : ℝ) * ((j : ℝ) + 1) := mul_pos hJ0 hJ1
  have hrow' : b * (j : ℝ) * (j - 1) =
      e * ((j : ℝ) * (j + 1) * ell - 2) := by
    have h := congrArg (fun x : ℝ => x * ((j : ℝ) * (j + 1))) hrow
    field_simp at h
    nlinarith only [h]
  have hcoef : (j : ℝ) < (j : ℝ) * (j + 1) * ell - 2 := by
    have hstrict := mul_lt_mul_of_pos_left hell hden
    have hpoly := mul_nonneg (sub_nonneg.mpr hJ)
      (show 0 ≤ 2 * (j : ℝ) + 3 by linarith)
    nlinarith only [hstrict, hpoly]
  have hleft : 0 < ((j : ℝ) - 1) * b := mul_pos (by linarith) hb
  have hbound := mul_le_mul_of_nonneg_right hfirst
    (show 0 ≤ (j : ℝ) * (j + 1) * ell - 2 by linarith)
  have hstrict := mul_lt_mul_of_pos_left hcoef hleft
  nlinarith only [hrow', hbound, hstrict]

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The actual third-cusp R-null boundary with no exterior atom is
impossible. Its constructed integer optimum receives its own cusp slope
and independent-root mass bound; no upper bound ell<1 is assumed. -/
theorem no_cusp_three_zero_body_zero_exterior
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) (hdk : d = 4 / 9)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hatoms : ∀ u : S.I, u = r ∨ u = a) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by rw [hdk]; norm_num
  obtain ⟨j, hj, hlo, _, V, m', hV, hmom, _⟩ :=
    S.exists_covered_zero_explicit_optimum r a hW hd hgap hpair hzero hR hE hatoms
  let label := S.coveredZeroBoundaryLabel r a
  let A := μ.real (label ⁻¹' {0})
  let B := μ.real (label ⁻¹' {1})
  let E := μ.real (label ⁻¹' {2})
  let I := label ⁻¹' {1}
  have hlabel := S.measurable_coveredZeroBoundaryLabel r a
  have hpos := S.coveredZeroBoundaryLabel_fibers_positive r a hpair.1 hatoms
    (hE.trans_le (measure_mono sdiff_subset))
  obtain ⟨_, hB, hD⟩ := S.coveredZeroBoundaryLabel_fibers r a hpair.1 hatoms
  have hb : 0 < B := ENNReal.toReal_pos (hpos 1).ne' (measure_ne_top _ _)
  have hfirst : ((j : ℝ) - 1) * B ≤ E := by simpa only [B, E, label, hB, hD] using hlo
  have hglobalV : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (T : Model Ω ν),
      FullFeasible T → objective T - benchmark (density T) ≤
        objective V - benchmark (density V) := by
    intro ν _ T hT
    simpa only [hW.objective_eq, hW.density_eq, hV.objective_eq, hV.density_eq] using
      hglobal ν T hT
  have hI : MeasurableSet I := hlabel (measurableSet_singleton 1)
  have hind : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict I),
      adjacencyKernel V p.1 p.2 = 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' (hI.prod hI)).mpr
    exact Eventually.of_forall (fun p hp => by
      have hi : S.coveredZeroBoundaryLabel r a p.1 = 1 := hp.1
      have hj : S.coveredZeroBoundaryLabel r a p.2 = 1 := hp.2
      change V.moment CappedColor.adjacency p = 0
      simp [(hmom p).1, hi, hj, CoveredZeroExterior.blockAdjacency])
  obtain ⟨_, hell, _, _, _, hmassB, _, _⟩ :=
    hV.cusp_independent_set_contact_guards 3 (by omega) (by norm_num; exact hdk)
      hgap hglobalV I hI hind
  have hbcap : B ≤ 1 / 3 := by simpa only [I, B, Nat.cast_ofNat] using hmassB
  obtain ⟨hAE, hBA⟩ := CoveredZeroExterior.stationary_row_differences hV label hlabel hpos
    (CoveredZeroExterior.explicitDual j) hmom
  by_cases hjone : j = 1
  · subst j
    norm_num [CoveredZeroExterior.explicitDual] at hBA
    have hmass : A + B + E = 1 := CoveredZeroExterior.block_mass label hlabel
    have hrow : (A - B + E) * (1 - m') = 0 := by
      dsimp only [A, B, E]
      nlinarith only [hBA]
    have hfactor : 1 - m' ≠ 0 := by linarith [hell.1]
    have hbalance := (mul_eq_zero.mp hrow).resolve_right hfactor
    linarith
  · apply no_integer_row_above_two_thirds (ell := -m') (by omega) hb
      (by linarith [hell.1]) hfirst
    simpa only [CoveredZeroExterior.explicitDual, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] using hAE

end Erdos1017.CappedModel.SelectedHighLowStructure
