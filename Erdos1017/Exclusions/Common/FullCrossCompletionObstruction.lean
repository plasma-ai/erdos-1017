module

public import Erdos1017.Exclusions.Common.RootCancelledCrossCompletion

/-!
# Obstruction from cross completion at a full optimum

Positive cross-missing sets cannot have every `F`-root charge at most the
optimum's own `ell`, using neutral insertion only across `C` and `F`, so a
constant `F`-root block has charge above `ell`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Positive cross-missing sets cannot have every F-root charge at most
the own ell of this full optimum. Neutral insertion is performed only
across C and F; actual all-order feasibility is derived by cancellation. -/
theorem not_ae_cross_root_star_le (W : Model Ω μ) {d c m : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (R C F : Set Ω) (hC : MeasurableSet C) (hF : MeasurableSet F)
    (hCpos : 0 < μ C) (hFpos : 0 < μ F)
    (hRC : Disjoint R C) (hRF : Disjoint R F) (hCF : Disjoint C F)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → adjacencyKernel W p.1 p.2 = 0)
    (hcross : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ F → adjacencyKernel W p.1 p.2 = 0)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → chargeKernel W p.1 p.2 ≤ 0) :
    ¬(∀ᵐ p ∂μ.prod μ, p.1 ∈ F → p.2 ∈ R → chargeKernel W p.1 p.2 ≤ -m) := by
  intro hstar
  have hs := hW.strict_gap_structure hd hgap
  have hphysical : ∀ᵐ p ∂μ.prod μ,
      (p.1 ∈ R → p.2 ∈ R → PhysicalRepresentative.adjacency W m p.1 p.2 = false) ∧
      (p.1 ∈ C → p.2 ∈ F → PhysicalRepresentative.adjacency W m p.1 p.2 = false) ∧
      (p.1 ∉ R → p.2 ∉ R → PhysicalRepresentative.charge W m p.1 p.2 ≤ 0) ∧
      (p.1 ∈ F → p.2 ∈ R → PhysicalRepresentative.charge W m p.1 p.2 ≤ -m) := by
    filter_upwards [hroot, hcross, hbody, hstar,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hr hc hb ht hG hY
    have hzero (hz : adjacencyKernel W p.1 p.2 = 0) :
        PhysicalRepresentative.adjacency W m p.1 p.2 = false := by
      change W.moment CappedColor.adjacency p = 0 at hz
      rw [hz] at hG
      cases hA : PhysicalRepresentative.adjacency W m p.1 p.2
      · rfl
      · simp only [hA, ite_true] at hG
        norm_num at hG
    exact ⟨fun hx hy => hzero (hr hx hy), fun hx hy => hzero (hc hx hy),
      fun hx hy => hY.trans_le (hb hx hy), fun hx hy => hY.trans_le (ht hx hy)⟩
  have hcap (n : ℕ) : FiniteArity.FeasibleOrder μ
      (FiniteArity.maskAdjacency (PhysicalRepresentative.adjacency W m) (FiniteArity.crossMask C F))
      (FiniteArity.maskCharge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) (FiniteArity.crossMask C F) m) n := by
    simpa only [neg_neg] using FiniteArity.feasibleOrder_root_cancelled_cross μ
      (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.charge W m)
      (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.charge_symm W m)
      R C F hRC hRF hCF (-m) (neg_nonneg.mpr hs.multiplier_neg.le)
      (hphysical.mono (fun _ h => h.1)) (hphysical.mono (fun _ h => h.2.1))
      (hphysical.mono (fun _ h => h.2.2.1)) (hphysical.mono (fun _ h => h.2.2.2))
      (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic) n
  have hmask := FiniteArity.measurableSet_crossMask C F hC hF
  have hmissing := MaskedZeroCompletion.missingMass_eq_zero_of_fullStationaryClass W hW hd hgap
    (FiniteArity.crossMask C F) hmask (FiniteArity.crossMask_symm C F) (fun n _ => hcap n)
  have hcomplete := MaskedZeroCompletion.ae_complete_of_missingMass_eq_zero W m
    (FiniteArity.crossMask C F) hmask hs.strict_support hmissing
  have hfalse : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ F → False := by
    filter_upwards [hcomplete, hcross] with p hp hc hx hy
    have hone := hp (Or.inl ⟨hx, hy⟩)
    have hzero := hc hx hy
    change W.moment CappedColor.adjacency p = 0 at hzero
    linarith
  obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hCpos.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hfalse))
  obtain ⟨y, hy, hxy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hFpos.ne'
    (ae_restrict_of_ae hrow)
  exact hxy hx hy

/-- A genuinely constant F-root block must therefore have charge above
this model's own ell. No positivity of a source or new stationarity is used. -/
theorem cross_root_charge_gt_of_constant (W : Model Ω μ) {d c m v : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (R C F : Set Ω) (hC : MeasurableSet C) (hF : MeasurableSet F)
    (hCpos : 0 < μ C) (hFpos : 0 < μ F)
    (hRC : Disjoint R C) (hRF : Disjoint R F) (hCF : Disjoint C F)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → adjacencyKernel W p.1 p.2 = 0)
    (hcross : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ F → adjacencyKernel W p.1 p.2 = 0)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → chargeKernel W p.1 p.2 ≤ 0)
    (hconstant : ∀ᵐ p ∂μ.prod μ, p.1 ∈ F → p.2 ∈ R → chargeKernel W p.1 p.2 = v) :
    -m < v := by
  by_contra hnot
  apply not_ae_cross_root_star_le W hW hd hgap R C F hC hF hCpos hFpos hRC hRF hCF
    hroot hcross hbody
  exact hconstant.mono (fun _ hp hx hy => (hp hx hy).trans_le (le_of_not_gt hnot))

end Erdos1017.CappedModel
