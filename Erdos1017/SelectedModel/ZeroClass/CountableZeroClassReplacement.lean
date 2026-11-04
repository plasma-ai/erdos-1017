module

public import Erdos1017.SelectedModel.ZeroClass.AtomlessZeroClassPatch
public import Erdos1017.SelectedModel.ZeroClass.CountableZeroClassEncoding
public import Erdos1017.SelectedModel.ZeroClass.CountableZeroClassInduction
public import Erdos1017.SelectedModel.ZeroClass.CountableClassEditMeans
public import Erdos1017.SelectedModel.ZeroClass.CountableClassEditStructure
public import Erdos1017.SelectedModel.ZeroClass.IndexOneActiveClasses

/-!
# Multipartite replacement of the active boundary classes

All active boundary fibers can be replaced on the original atomless carrier,
every finite prefix being feasible and mean-preserving, and the constructed
multipartite model compares the original model with the benchmark
(`objective_le_benchmark_of_active_boundary_data`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [BorelSpace H] [OpensMeasurableSpace H]
    [SecondCountableTopology H]

/-- The actual active boundary fibers can all be replaced on the original
atomless carrier. Every finite prefix is proved feasible and preserves both
means before passing to the simultaneous edit. -/
theorem exists_multipartite_replacement_of_active_boundary_data
    (W : Model Ω μ) (hW : FullFeasible W) (F : Ω → H) (hF : Measurable F)
    (C : Set H) (ν m : ℝ) (hν : 0 ≤ ν) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hdata : ActiveBoundaryData W F C (Real.sqrt ν) m)
    (hrep : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 ↔
      ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∃ (V : Model Ω μ) (π : Ω → (ℕ × ℕ) ⊕ Ω), FullFeasible V ∧
      density V = density W ∧ objective V = objective W ∧
      (∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂V.kernel p,
        CappedColor.adjacency c = 1 ↔ π p.1 ≠ π p.2) := by
  classical
  let ι := C
  let : Countable ι := hdata.countable.to_subtype
  let v : ι → H := fun i => i.val
  let s : ι → Set Ω := fun i => {x | F x = v i}
  have hs (i : ι) : MeasurableSet (s i) := (hdata.fiber i.val i.property).1
  have hpos (i : ι) : 0 < μ (s i) := (hdata.fiber i.val i.property).2.1
  have hv (i : ι) : ‖v i‖ = Real.sqrt ν := (hdata.fiber i.val i.property).2.2.1
  have horders (i : ι) : ∃ k : ℕ, 1 ≤ k ∧ 0 < restrictedCliquePresence W (s i) k ∧
      internalFiberDensity W F (v i) ≤ 1 - 1 / (k : ℝ) :=
    (hdata.fiber i.val i.property).2.2.2.2
  choose k hk hclique hcapacity using horders
  have hlabels (i : ι) : ∃ (L : Ω → Fin (k i)) (hL : Measurable L),
      (μ.real (s i)) ^ 2 - ∑ j, (patchLabelMass (μ := μ) (s i) L j) ^ 2 =
        ∫ p in s i ×ˢ s i, W.moment CappedColor.adjacency p ∂μ.prod μ := by
    obtain ⟨a, ha, hsum, L, hL, _, _, hmatch, _, _, _⟩ :=
      exists_atomless_zeroClass_patch_of_density_bound W hW F hF (v i) ν m hν (hv i)
        hm (k i) (by have := hk i; omega) (hpos i) (hclique i) (hcapacity i)
        hrep hzero hnonneg hcomp hdet
    exact ⟨L, hL, hmatch⟩
  choose L hL hmatch using hlabels
  have hdisj : Pairwise (fun i j : ι => Disjoint (s i) (s j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    exact hij (Subtype.ext (hx.symm.trans hy))
  obtain ⟨e, t, ht, htag, hout⟩ := exists_measurable_countableClassLabels_encoding s hs hdisj k L hL
  have hclasses (p : Ω × Ω) :
      (0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1) ↔
        ∃ w ∈ C, F p.1 = w ∧ F p.2 = w := by
    constructor
    · rintro ⟨hpositive, hequal⟩
      have hex : ∃ i : ι, p.1 ∈ s i := by
        by_contra hnone
        have hnot : ∀ i, p.1 ∉ s i := fun i hi => hnone ⟨i, hi⟩
        rw [hout p.1 hnot] at hpositive
        exact (Nat.lt_irrefl 0 hpositive)
      obtain ⟨i, hi⟩ := hex
      have hsecond : p.2 ∈ s i :=
        (countableClassLabels_encoding_index_eq_iff s L e t htag hout i p.2).mp (by
          rw [← hequal, htag i p.1 hi])
      exact ⟨i.val, i.property, hi, hsecond⟩
    · rintro ⟨w, hw, hx, hy⟩
      let i : ι := ⟨w, hw⟩
      rw [htag i p.1 hx, htag i p.2 hy]
      exact ⟨Nat.zero_lt_succ _, rfl⟩
  have hclassZero : ∀ᵐ p ∂μ.prod μ,
      0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1 → shiftedMoment W m p = 0 :=
    hdata.zero.mono (fun p hp hclass => hp ((hclasses p).mp hclass))
  have houtside : ∀ᵐ p ∂μ.prod μ,
      ¬(0 < (t p.1).1 ∧ (t p.1).1 = (t p.2).1) → W.moment CappedColor.adjacency p = 1 :=
    hdata.outside.mono (fun p hp hnot => hp (fun hclass => hnot ((hclasses p).mpr hclass)))
  have hprefix := prefixClassEdit_fullFeasible_means W hW F hF ν m hν hm v hv hpos k
    hclique L hL hmatch e t ht htag hout hclassZero hrep hzero hnonneg hcomp hdet
  have hfull := fullFeasible_countableClassEdit W t ht m hm (fun N => (hprefix N).1)
  have hmeans := countableClassEdit_means_eq_of_prefix W t ht m hm
    (fun N => (hprefix N).2.1) (fun N => (hprefix N).2.2)
  exact ⟨countableClassEdit W t ht m hm, classPartLabel t, hfull, hmeans.1, hmeans.2,
    countableClassEdit_partition_support_of_atomless W t ht m hm houtside⟩

/-- The constructed multipartite model compares the original model with the
benchmark, with no supplied prefix feasibility or mean-preservation premise. -/
theorem objective_le_benchmark_of_active_boundary_data
    (W : Model Ω μ) (hW : FullFeasible W) (F : Ω → H) (hF : Measurable F)
    (C : Set H) (ν m : ℝ) (hν : 0 ≤ ν) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hdata : ActiveBoundaryData W F C (Real.sqrt ν) m)
    (hrep : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = ν - ⟪F p.1, F p.2⟫)
    (hzero : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p = 0 ↔
      ‖F p.1‖ = Real.sqrt ν ∧ F p.1 = F p.2)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    objective W ≤ benchmark (density W) := by
  obtain ⟨V, π, hV, hdV, hcV, hsupport⟩ :=
    exists_multipartite_replacement_of_active_boundary_data W hW F hF C ν m hν hm
      hdata hrep hzero hnonneg hcomp hdet
  have h := objective_le_benchmark_of_partition_support V hV π hsupport
  simpa only [hdV, hcV] using h

end Erdos1017.CappedModel
