module

public import Erdos1017.Exclusions.Common.DeterministicFullStationarity

/-!
# Agreement of stationary records on one model

Two constant shifted rows on the same model have the same multiplier and
constant whenever the degree is not essentially constant, so a new stationary
record agrees with any recorded constant row, and a full optimum's recorded row
identifies its own stationary multiplier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Two actual constant shifted rows on the same model have the same
multiplier and constant when its original degree is not essentially
constant. Only bounded-kernel Fubini and the two actual rows are used. -/
theorem stationary_multiplier_unique (W : Model Ω μ) (m₁ m₂ ν₁ ν₂ : ℝ)
    (hdegree : ¬∃ a : ℝ, ∀ᵐ x ∂μ, (∫ y, adjacencyKernel W x y ∂μ) = a)
    (hrow₁ : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m₁ x y ∂μ) = ν₁)
    (hrow₂ : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m₂ x y ∂μ) = ν₂) :
    m₁ = m₂ ∧ ν₁ = ν₂ := by
  have hI₁ : Integrable (fun p : Ω × Ω => shiftedKernel W m₁ p.1 p.2) (μ.prod μ) :=
    integrable_shiftedMoment W m₁
  have hI₂ : Integrable (fun p : Ω × Ω => shiftedKernel W m₂ p.1 p.2) (μ.prod μ) :=
    integrable_shiftedMoment W m₂
  have hdiff : ∀ᵐ x ∂μ, (m₂ - m₁) * (∫ y, adjacencyKernel W x y ∂μ) = ν₁ - ν₂ := by
    filter_upwards [hrow₁, hrow₂, hI₁.prod_right_ae, hI₂.prod_right_ae] with x hr₁ hr₂ hi₁ hi₂
    calc
      _ = ∫ y, shiftedKernel W m₁ x y - shiftedKernel W m₂ x y ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun y => by
          change (m₂ - m₁) * W.moment CappedColor.adjacency (x, y) =
            shiftedMoment W m₁ (x, y) - shiftedMoment W m₂ (x, y)
          rw [shiftedMoment_eq, shiftedMoment_eq]
          ring)
      _ = _ := by rw [integral_sub hi₁ hi₂, hr₁, hr₂]
  have hm : m₁ = m₂ := by
    by_contra hnot
    have hnonzero : m₂ - m₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hnot)
    apply hdegree
    refine ⟨(ν₁ - ν₂) / (m₂ - m₁), ?_⟩
    filter_upwards [hdiff] with x hx
    apply (eq_div_iff hnonzero).mpr
    linarith
  obtain ⟨x, hx⟩ := hdiff.exists
  rw [hm, sub_self, zero_mul] at hx
  exact ⟨hm, by linarith⟩

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A newly constructed own stationary record agrees with another
recorded constant row on that same original model. Nonconstant degree
is derived from this record's actual strict benchmark gap. -/
theorem FullStationaryClass.multiplier_eq_of_stationary
    {W : Model Ω μ} {d c m n ν : ℝ} (hW : FullStationaryClass d c W n)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) :
    m = n ∧ ν = 2 * (c - n * d) :=
  stationary_multiplier_unique W m n ν _
    (hW.strict_gap_structure hd hgap).nonconstant_degree hrow hW.stationary

/-- An actual deterministic full optimum's recorded row identifies its
own newly constructed stationary multiplier, preserving the model,
carrier, law, and labels rather than reselecting them. -/
theorem fullStationaryClass_of_recorded_rows (W : Model Ω μ)
    (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (hphysical : ∀ p, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z)
    (hd : density W ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark (density W) < objective W) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) :
    FullStationaryClass (density W) (objective W) W m ∧
      ν = 2 * (objective W - m * density W) := by
  obtain ⟨n, hn⟩ := exists_same_model_fullStationaryClass W hW hopt hphysical hd hgap
  obtain ⟨hm, hν⟩ := hn.multiplier_eq_of_stationary hd hgap hrow
  subst n
  exact ⟨hn, hν⟩

end Erdos1017.CappedModel
