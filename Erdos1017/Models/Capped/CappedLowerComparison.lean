module

public import Erdos1017.Models.FractionalBoundedDual
public import Erdos1017.Models.Capped.CappedAttainment
public import Erdos1017.Models.Capped.CappedDensityRestoration
public import Erdos1017.Models.Decorated.FiniteGraphDecoratedRealization

/-!
# Finite fractional values below the capped optimum

Every penalized finite fractional graph certificate is bounded by the capped
optimum at its density, so the density limit is dominated by the capped maximum
at every order (`densityLimit_le_capValue`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CappedModel

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω]
  [BorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Every penalized finite fractional graph certificate is bounded by the
actual capped optimum at the prescribed density. -/
theorem finite_fractional_value_le_capValue {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : 0 < n) (r : ℕ) (d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
    FractionalGraph.value G / (n : ℝ) ^ 2 -
      3 * |(G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 - d| ≤ capValue Ω μ r d := by
  obtain ⟨M, _, hdM, hoM, hM⟩ := exists_fixedMeasureMaximizer (μ := μ) r d hd
  obtain ⟨y, hy, hyIcc, hopt⟩ := FractionalGraph.exists_bounded_dual G
  obtain ⟨U, hU, hdenU, hobjU⟩ :=
    exists_fullyFeasible_realization (Ω := Ω) (μ := μ) G hn y hy hyIcc
  obtain ⟨R, hR, hdR, hcostR⟩ := exists_density_restoration U (hU r) d hd
  have hRle : objective R ≤ objective M := hM.2 R hR (hdR.trans hdM.symm)
  calc
    FractionalGraph.value G / (n : ℝ) ^ 2 -
        3 * |(G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 - d| =
      objective U - 3 * |density U - d| := by rw [hdenU, hobjU, hopt]
    _ ≤ objective R := hcostR
    _ ≤ objective M := hRle
    _ = capValue Ω μ r d := hoM

/-- The capped maximum dominates the penalized finite-graph supremum at
every order. -/
theorem densityLimit_le_capValue (r : ℕ) (d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
    FractionalGraph.densityLimit d ≤ capValue Ω μ r d := by
  obtain ⟨M, _, hdM, hoM, hM⟩ := exists_fixedMeasureMaximizer (μ := μ) r d hd
  have hnonneg : 0 ≤ capValue Ω μ r d := by
    obtain ⟨Z, hZ, hdZ, hoZ⟩ := exists_zeroCharge_competitor (μ := μ) r d hd
    have hZle := hM.2 Z hZ (hdZ.trans hdM.symm)
    rw [hoZ, hoM] at hZle
    exact hZle
  unfold FractionalGraph.densityLimit
  apply csSup_le (FractionalGraph.densityCandidates_nonempty d)
  rintro c (rfl | ⟨N, G, rfl⟩)
  · exact hnonneg
  · exact finite_fractional_value_le_capValue (μ := μ) G (Nat.succ_pos N) r d hd

end Erdos1017.CappedModel
