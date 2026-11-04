module

public import Erdos1017.SelectedModel.ZeroClass.IndexOneKernelClasses
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassCliqueOrders
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassInfiniteOrder
public import Erdos1017.Models.Capped.CappedRegularKernel

/-!
# Active boundary classes at index one

This module defines the normalized internal adjacency density of a feature fiber
and the active boundary classes, those positive boundary fibers with internal
density strictly below one, and constructs from a stationary shifted operator of
index at most one the feature and active-class replacement inputs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual unhalved internal adjacency density of one feature fiber,
normalized by the square of its actual latent mass. -/
def internalFiberDensity (W : Model Ω μ) (F : Ω → H) (v : H) : ℝ :=
  (∫ p in {x | F x = v} ×ˢ {x | F x = v}, W.moment CappedColor.adjacency p ∂μ.prod μ) /
    (μ.real {x | F x = v}) ^ 2

/-- Active classes are exactly the listed positive boundary fibers whose
actual normalized internal adjacency density is strictly below one. -/
def activeBoundaryClasses (W : Model Ω μ) (F : Ω → H) (A : Set H) : Set H :=
  {v | v ∈ A ∧ internalFiberDensity W F v < 1}

/-- The actual fiber density equals twice the density of the actual
conditioned model; no replacement or normalized-density premise is used. -/
theorem internalFiberDensity_eq_conditionOn (W : Model Ω μ) (F : Ω → H) (v : H)
    (hpos : 0 < μ {x | F x = v}) :
    internalFiberDensity W F v = 2 * density (conditionOn W {x | F x = v} hpos) := by
  rw [density_conditionOn]
  unfold internalFiberDensity
  ring

/-- Every positive actual fiber has normalized internal density in [0,1]. -/
theorem internalFiberDensity_mem (W : Model Ω μ) (F : Ω → H) (v : H)
    (hpos : 0 < μ {x | F x = v}) : internalFiberDensity W F v ∈ Icc (0 : ℝ) 1 := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ {x | F x = v}) :=
    conditioned_probability _ hpos
  rw [internalFiberDensity_eq_conditionOn W F v hpos]
  have h := density_mem (conditionOn W {x | F x = v} hpos)
  constructor <;> linarith [h.1, h.2]

/-- Every active fiber supplies a finite positive old clique order with
enough Turán capacity. The infinite-positive branch uses a finite
Archimedean choice rather than an assumed last positive order. -/
theorem exists_active_fiber_clique_order (W : Model Ω μ) (F : Ω → H) (v : H)
    (hpos : 0 < μ {x | F x = v}) (hq : internalFiberDensity W F v < 1) :
    ∃ k : ℕ, 1 ≤ k ∧ 0 < restrictedCliquePresence W {x | F x = v} k ∧
      internalFiberDensity W F v ≤ 1 - 1 / (k : ℝ) := by
  rcases restrictedCliquePresence_order_dichotomy W {x | F x = v} hpos with hinfinite | hfinite
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hq)
    refine ⟨n + 1, by omega, hinfinite (n + 1) (by omega), ?_⟩
    have hsmall : 1 / ((n + 1 : ℕ) : ℝ) < 1 - internalFiberDensity W F v := by
      simpa only [Nat.cast_add, Nat.cast_one] using hn
    linarith
  · obtain ⟨k, hk, hpositive, hzero⟩ := hfinite
    exact ⟨k, hk, hpositive,
      internal_density_le_turan_of_zero_restricted_clique W _ hpos k (by omega) hzero⟩

/-- A unit-density actual fiber has old conditional adjacency one almost
everywhere on its original class square, obtained from the normalized
class model's unit-density theorem and an absolute-continuity lift. -/
theorem ae_adjacency_one_on_unit_fiber (W : Model Ω μ) (F : Ω → H) (v : H)
    (hs : MeasurableSet {x | F x = v}) (hpos : 0 < μ {x | F x = v})
    (hq : internalFiberDensity W F v = 1) :
    ∀ᵐ p ∂μ.prod μ, F p.1 = v ∧ F p.2 = v → W.moment CappedColor.adjacency p = 1 := by
  let s := {x | F x = v}
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ s) := conditioned_probability s hpos
  have hunit : 2 * density (conditionOn W s hpos) = 1 := by
    rw [← internalFiberDensity_eq_conditionOn W F v hpos]
    exact hq
  have hcond := adjacency_ae_one_of_unhalved_density_one (conditionOn W s hpos) hunit
  have hac : μ.restrict s ≪ ProbabilityTheory.cond μ s := by
    rw [ProbabilityTheory.cond]
    exact Measure.absolutelyContinuous_smul (by simp [measure_ne_top])
  have hprod : (μ.prod μ).restrict (s ×ˢ s) ≪
      (ProbabilityTheory.cond μ s).prod (ProbabilityTheory.cond μ s) := by
    rw [← Measure.prod_restrict]
    exact hac.prod hac
  have hraw := hprod.ae_le hcond
  exact (ae_restrict_iff' (hs.prod hs)).mp hraw

variable [NormedAddCommGroup H]

/-- Actual inputs needed to replace the active positive boundary fibers.
The outside assertion concerns the original conditional adjacency moment. -/
structure ActiveBoundaryData (W : Model Ω μ) (F : Ω → H) (C : Set H) (R m : ℝ) : Prop where
  countable : C.Countable
  fiber : ∀ v ∈ C, MeasurableSet {x | F x = v} ∧ 0 < μ {x | F x = v} ∧ ‖v‖ = R ∧
    internalFiberDensity W F v ∈ Ico (0 : ℝ) 1 ∧
    ∃ k : ℕ, 1 ≤ k ∧ 0 < restrictedCliquePresence W {x | F x = v} k ∧
      internalFiberDensity W F v ≤ 1 - 1 / (k : ℝ)
  disjoint : C.Pairwise (fun v w => Disjoint {x | F x = v} {x | F x = w})
  zero : ∀ᵐ p ∂μ.prod μ,
    (∃ v ∈ C, F p.1 = v ∧ F p.2 = v) → shiftedMoment W m p = 0
  outside : ∀ᵐ p ∂μ.prod μ,
    (¬∃ v ∈ C, F p.1 = v ∧ F p.2 = v) → W.moment CappedColor.adjacency p = 1

/-- The actual active subset of the countable positive boundary classes
supplies finite old clique witnesses and adjacency one outside their
squares. Unit-density inactive fibers are retained, not replaced. -/
theorem activeBoundaryClasses_data (W : Model Ω μ) (F : Ω → H) (A : Set H) (R m : ℝ)
    (hA : A.Countable)
    (hclass : ∀ v ∈ A, MeasurableSet {x | F x = v} ∧ 0 < μ {x | F x = v} ∧ ‖v‖ = R)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      shiftedMoment W m p = 0 ↔ ∃ v ∈ A, F p.1 = v ∧ F p.2 = v)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) :
    ActiveBoundaryData W F (activeBoundaryClasses W F A) R m := by
  let C := activeBoundaryClasses W F A
  let : Countable A := hA.to_subtype
  have hinactive (v : A) : ∀ᵐ p ∂μ.prod μ, v.val ∉ C →
      F p.1 = v.val ∧ F p.2 = v.val → W.moment CappedColor.adjacency p = 1 := by
    by_cases hv : v.val ∈ C
    · filter_upwards with p hout
      exact (hout hv).elim
    · have hq : internalFiberDensity W F v.val = 1 := by
        have hupper := (internalFiberDensity_mem W F v.val (hclass v.val v.property).2.1).2
        have hlower : 1 ≤ internalFiberDensity W F v.val :=
          le_of_not_gt (fun hlt => hv ⟨v.property, hlt⟩)
        exact le_antisymm hupper hlower
      filter_upwards [ae_adjacency_one_on_unit_fiber W F v.val
        (hclass v.val v.property).1 (hclass v.val v.property).2.1 hq] with p hp _
      exact hp
  have hall : ∀ᵐ p ∂μ.prod μ, ∀ v : A, v.val ∉ C →
      F p.1 = v.val ∧ F p.2 = v.val → W.moment CappedColor.adjacency p = 1 :=
    ae_all_iff.mpr hinactive
  refine ⟨hA.mono (fun _ hv => hv.1), ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hvA : v ∈ A := hv.1
    exact ⟨(hclass v hvA).1, (hclass v hvA).2.1, (hclass v hvA).2.2,
      ⟨(internalFiberDensity_mem W F v (hclass v hvA).2.1).1, hv.2⟩,
      exists_active_fiber_clique_order W F v (hclass v hvA).2.1 hv.2⟩
  · intro v _ w _ hne
    exact disjoint_left.mpr (fun x hx hy => hne (hx.symm.trans hy))
  · filter_upwards [hzero] with p hp hactive
    obtain ⟨v, hv, hx, hy⟩ := hactive
    exact hp.mpr ⟨v, hv.1, hx, hy⟩
  · filter_upwards [hzero, hcomp, hall] with p hz hc hi hout
    by_cases hM : shiftedMoment W m p = 0
    · obtain ⟨v, hv, hx, hy⟩ := hz.mp hM
      have hvnot : v ∉ C := fun hactive => hout ⟨v, hactive, hx, hy⟩
      exact hi ⟨v, hv⟩ hvnot ⟨hx, hy⟩
    · have hAone : 1 - W.moment CappedColor.adjacency p = 0 :=
        (mul_eq_zero.mp hc).resolve_right hM
      linarith

end Erdos1017.CappedModel

namespace Erdos1017.CappedModel

universe u

/-- Actual stationary shifted-operator index at most one constructs its
feature and active-class replacement inputs. The countable eigenbasis and
all positive boundary fibers are derived, with L² separability explicit. -/
theorem exists_index_one_active_classes
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (m ν : ℝ) (hν : 0 < ν)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hstationary : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hfinite : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)))
    (hindex : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 1) :
    ∃ (ι : Type u) (_ : Countable ι) (F : Ω → lp (fun _ : ι => ℝ) 2)
      (C : Set (lp (fun _ : ι => ℝ) 2)),
      StronglyMeasurable F ∧
      (∀ᵐ x ∂μ, ‖F x‖ ≤ Real.sqrt ν) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 ↔
        ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2) ∧
      ActiveBoundaryData W F C (Real.sqrt ν) m := by
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  obtain ⟨ι, hcount, F, A, hF, hbound, hrep, hzero, hA, hclass, _, hclasses, _⟩ :=
    KernelOperator.exists_index_one_feature_zero_classes (shiftedKernel W m) (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hnonneg hsym
      ν hν hstationary hfinite hindex
  exact ⟨ι, hcount, F, activeBoundaryClasses W F A, hF, hbound, hrep, hzero,
    activeBoundaryClasses_data W F A (Real.sqrt ν) m hA hclass hclasses hcomp⟩

end Erdos1017.CappedModel
