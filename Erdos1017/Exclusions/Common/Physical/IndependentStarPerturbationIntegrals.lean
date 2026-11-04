module

public import Erdos1017.Exclusions.Common.Physical.IndependentStarPerturbation
public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost

/-!
# Integrals of the independent star edit

The row integrals of the star edit direction are computed (each root row gains
the cell mass, an outside row loses its adjacent cell mass), and the exact
objective change of the bounded signed edit is derived, reducing to the
cell-mass slope when the outside-neighbor section mass is constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.IndependentStarPerturbation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The actual outside-neighbor section of the independent cell direction. -/
def outsideNeighbors (A : Ω → Ω → Bool) (I J : Set Ω) (x : Ω) : Set Ω :=
  (I ∪ J)ᶜ ∩ {y | A x y = true}

/-- Original-law mass of that actual section, before any homogeneity assumption. -/
def outsideNeighborMass (μ : Measure Ω) (A : Ω → Ω → Bool) (I J : Set Ω) (x : Ω) : ℝ :=
  μ.real (outsideNeighbors A I J x)

theorem measurableSet_outsideNeighbors (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (I J : Set Ω)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (x : Ω) :
    MeasurableSet (outsideNeighbors A I J x) :=
  (hI.union hJ).compl.inter
    ((hA.comp (measurable_const.prodMk measurable_id)) (measurableSet_singleton true))

theorem integrable_direction (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    Integrable (Function.uncurry (direction A I J)) (μ.prod μ) := by
  apply Integrable.of_bound (measurable_direction A hA I J hI hJ).aestronglyMeasurable 1
  exact Eventually.of_forall (fun p => by simpa [Real.norm_eq_abs, Function.uncurry] using
    (direction_abs_le_one A I J p.1 p.2))

theorem integrable_direction_row (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (I J : Set Ω)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (x : Ω) :
    Integrable (direction A I J x) μ := by
  apply Integrable.of_bound
    ((measurable_direction A hA I J hI hJ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  exact Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs, Function.uncurry] using
    (direction_abs_le_one A I J x y))

omit [IsFiniteMeasure μ] in
/-- Every root row gains the original cell mass. -/
theorem integral_direction_row_root (A : Ω → Ω → Bool) (I J : Set Ω)
    (hJ : MeasurableSet J) (hdisj : Disjoint I J) (x : Ω) (hx : x ∈ I) :
    (∫ y, direction A I J x y ∂μ) = μ.real J := by
  have hxJ : x ∉ J := fun h => Set.disjoint_left.mp hdisj hx h
  have he : direction A I J x = J.indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases hy : y ∈ J <;> simp [direction, hx, hxJ, hy]
  rw [he, integral_indicator hJ]
  simp

/-- The cell row balances its root gain against its actual outside neighbors. -/
theorem integral_direction_row_cell (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (I J : Set Ω)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (hdisj : Disjoint I J)
    (x : Ω) (hx : x ∈ J) :
    (∫ y, direction A I J x y ∂μ) = μ.real I - outsideNeighborMass μ A I J x := by
  have hxI : x ∉ I := fun h => Set.disjoint_left.mp hdisj h hx
  have he : direction A I J x = fun y => I.indicator (fun _ => (1 : ℝ)) y -
      (outsideNeighbors A I J x).indicator (fun _ => (1 : ℝ)) y := by
    funext y
    by_cases hi : y ∈ I <;> by_cases hj : y ∈ J <;>
      by_cases ha : A x y = true <;>
      simp [direction, hx, hxI, hi, hj, ha, outsideNeighbors]
  have hS := measurableSet_outsideNeighbors A hA I J hI hJ x
  rw [he, integral_sub ((integrable_const 1).indicator hI)
    ((integrable_const 1).indicator hS), integral_indicator hI, integral_indicator hS]
  simp [outsideNeighborMass]

omit [IsFiniteMeasure μ] in
/-- An outside row loses exactly its original adjacent cell mass. -/
theorem integral_direction_row_outside (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (I J : Set Ω)
    (hJ : MeasurableSet J) (x : Ω) (hxI : x ∉ I) (hxJ : x ∉ J) :
    (∫ y, direction A I J x y ∂μ) = -μ.real (J ∩ {y | A x y = true}) := by
  have hS : MeasurableSet (J ∩ {y | A x y = true}) := hJ.inter
    ((hA.comp (measurable_const.prodMk measurable_id)) (measurableSet_singleton true))
  have he : direction A I J x = fun y =>
      -(J ∩ {y | A x y = true}).indicator (fun _ => (1 : ℝ)) y := by
    funext y
    by_cases hj : y ∈ J <;> by_cases ha : A x y = true <;>
      simp [direction, hxI, hxJ, hj, ha]
  rw [he, integral_neg, integral_indicator hS]
  simp

/-- Exact charge-row change under the original law; the old row need
only be integrable and no selected or edited stationarity is assumed. -/
theorem integral_charge_row (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (eps : ℝ) (x : Ω) (hY : Integrable (Y x) μ) :
    (∫ y, charge A Y I J eps x y ∂μ) =
      (∫ y, Y x y ∂μ) + eps * ∫ y, direction A I J x y ∂μ := by
  exact (integral_add hY ((integrable_direction_row A hA I J hI hJ x).const_mul eps)).trans
    (by rw [integral_const_mul])

/-- Exact integral of the edit direction before assuming the cell has a
constant outside-neighbor mass. Both orientations use the same old law. -/
theorem integral_direction (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (hsym : ∀ x y, A x y = A y x) (I J : Set Ω)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (hdisj : Disjoint I J) :
    (∫ p : Ω × Ω, direction A I J p.1 p.2 ∂μ.prod μ) =
      2 * (μ.real I * μ.real J - ∫ x in J, outsideNeighborMass μ A I J x ∂μ) := by
  let F : Ω × Ω → ℝ := (I ×ˢ J).indicator (fun _ => 1)
  let D : Set (Ω × Ω) := {p | p.1 ∈ J ∧ p.2 ∈ outsideNeighbors A I J p.1}
  let H : Ω × Ω → ℝ := D.indicator (fun _ => 1)
  have hD : MeasurableSet D := (hJ.preimage measurable_fst).inter
    (((hI.union hJ).compl.preimage measurable_snd).inter
      (hA (measurableSet_singleton true)))
  have hF : Integrable F (μ.prod μ) := (integrable_const 1).indicator (hI.prod hJ)
  have hH : Integrable H (μ.prod μ) := (integrable_const 1).indicator hD
  have heq : (fun p : Ω × Ω => direction A I J p.1 p.2) =
      fun p => F p + F p.swap - H p - H p.swap := by
    funext p
    have hx : ¬(p.1 ∈ I ∧ p.1 ∈ J) := fun h => Set.disjoint_left.mp hdisj h.1 h.2
    have hy : ¬(p.2 ∈ I ∧ p.2 ∈ J) := fun h => Set.disjoint_left.mp hdisj h.1 h.2
    by_cases hi : p.1 ∈ I <;> by_cases hj : p.1 ∈ J <;>
      by_cases hI' : p.2 ∈ I <;> by_cases hJ' : p.2 ∈ J <;>
      by_cases ha : A p.1 p.2 = true <;>
      simp_all [direction, F, H, D, outsideNeighbors, hsym p.2 p.1]
  have hFi : (∫ p, F p ∂μ.prod μ) = μ.real I * μ.real J := by
    rw [show F = (I ×ˢ J).indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator (hI.prod hJ)]
    simp [measureReal_prod_prod]
  have hHi : (∫ p, H p ∂μ.prod μ) =
      ∫ x in J, outsideNeighborMass μ A I J x ∂μ := by
    rw [integral_prod _ hH, ← integral_indicator hJ]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      change (∫ y, H (x, y) ∂μ) = _
      by_cases hx : x ∈ J
      · have he : (fun y => H (x, y)) =
            (outsideNeighbors A I J x).indicator (fun _ => (1 : ℝ)) := by
          funext y
          simp [H, D, hx, Set.indicator_apply]
        rw [he, integral_indicator (measurableSet_outsideNeighbors A hA I J hI hJ x)]
        simp [hx, outsideNeighborMass]
      · simp [H, D, hx])
  have hFs : Integrable (fun p : Ω × Ω => F p.swap) (μ.prod μ) := hF.swap
  have hHs : Integrable (fun p : Ω × Ω => H p.swap) (μ.prod μ) := hH.swap
  have hsum : Integrable (fun p : Ω × Ω => F p + F p.swap) (μ.prod μ) := hF.add hFs
  have hsub : Integrable (fun p : Ω × Ω => F p + F p.swap - H p) (μ.prod μ) :=
    hsum.sub hH
  rw [heq, integral_sub hsub hHs,
    integral_sub hsum hH, integral_add hF hFs,
    integral_prod_swap F, integral_prod_swap H, hFi, hHi]
  ring

/-- Exact original-law objective change for the bounded signed edit. -/
theorem physicalObjective_charge (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (hsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (hY : Integrable (Function.uncurry Y) (μ.prod μ))
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hdisj : Disjoint I J) (eps : ℝ) :
    FiniteCappedSamplingCost.physicalObjective μ (charge A Y I J eps) =
      FiniteCappedSamplingCost.physicalObjective μ Y +
        eps * (μ.real I * μ.real J - ∫ x in J, outsideNeighborMass μ A I J x ∂μ) := by
  unfold FiniteCappedSamplingCost.physicalObjective
  change (∫ p : Ω × Ω, Y p.1 p.2 + eps * direction A I J p.1 p.2 ∂μ.prod μ) / 2 = _
  have hY' : Integrable (fun p : Ω × Ω => Y p.1 p.2) (μ.prod μ) := hY
  have hD : Integrable (fun p : Ω × Ω => eps * direction A I J p.1 p.2) (μ.prod μ) :=
    (integrable_direction A hA I J hI hJ).const_mul eps
  rw [integral_add hY' hD,
    integral_const_mul, integral_direction A hA hsym I J hI hJ hdisj]
  ring

/-- An actual AE constant section mass gives the literal cell-mass slope. -/
theorem physicalObjective_charge_of_constant_outside (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (hsym : ∀ x y, A x y = A y x)
    (Y : Ω → Ω → ℝ) (hY : Integrable (Function.uncurry Y) (μ.prod μ))
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hdisj : Disjoint I J) (eps s : ℝ)
    (hsection : ∀ᵐ x ∂μ, x ∈ J → outsideNeighborMass μ A I J x = s) :
    FiniteCappedSamplingCost.physicalObjective μ (charge A Y I J eps) =
      FiniteCappedSamplingCost.physicalObjective μ Y + eps * μ.real J * (μ.real I - s) := by
  have he : (∫ x in J, outsideNeighborMass μ A I J x ∂μ) = μ.real J * s := by
    calc
      _ = ∫ _x in J, s ∂μ := integral_congr_ae ((ae_restrict_iff' hJ).mpr hsection)
      _ = _ := by simp
  rw [physicalObjective_charge A hA hsym Y hY I J hI hJ hdisj, he]
  ring

end Erdos1017.IndependentStarPerturbation
