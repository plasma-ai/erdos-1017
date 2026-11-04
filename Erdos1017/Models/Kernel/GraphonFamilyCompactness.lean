/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The finite-fiber extraction and telescoping proofs below adapt the scalar
arguments in vendor/Graphon/Graphon/Compactness.lean by Cameron Freer.
-/
module

public import Graphon.Compactness
public import Erdos1017.Models.Kernel.GraphonFamilyNets

/-!
# Common-frame compactness of graphon families

Every sequence of finite graphon families has a subsequence converging uniformly
across the family after one common relabeling at each time, and every sequence
of countable families has a subsequence converging coordinatewise in one common
frame, built from finite covers with geometrically decreasing errors.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.GraphonFamily

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Two families close to the same center can be compared using one common map. -/
theorem common_alignment_of_center (U V C : ι → Graphon Ω μ)
    (p : ι → Prop) (ε : ℝ) (e f : Ω ≃ᵐ Ω)
    (he : MeasurePreserving e μ μ) (hf : MeasurePreserving f μ μ)
    (hU : ∀ i, p i → Graphon.cutNormDiff (Graphon.pullback (U i) e he) (C i) ≤ ε)
    (hV : ∀ i, p i → Graphon.cutNormDiff (Graphon.pullback (V i) f hf) (C i) ≤ ε) :
    ∃ (g : Ω ≃ᵐ Ω) (hg : MeasurePreserving g μ μ),
      ∀ i, p i → Graphon.cutNormDiff (Graphon.pullback (U i) g hg) (V i) ≤ 2 * ε := by
  let g := f.symm.trans e
  have hg : MeasurePreserving g μ μ := he.comp (hf.symm f)
  refine ⟨g, hg, fun i hi => ?_⟩
  have hcancel : Graphon.pullback (Graphon.pullback (V i) f hf) f.symm (hf.symm f) = V i := by
    rw [Graphon.pullback_pullback]
    simpa only [f.self_comp_symm] using Graphon.pullback_id (V i)
  calc
    Graphon.cutNormDiff (Graphon.pullback (U i) g hg) (V i)
        = Graphon.cutNormDiff
          (Graphon.pullback (Graphon.pullback (U i) e he) f.symm (hf.symm f))
          (Graphon.pullback (Graphon.pullback (V i) f hf) f.symm (hf.symm f)) := by
            rw [hcancel, Graphon.pullback_pullback]
            rfl
    _ = Graphon.cutNormDiff (Graphon.pullback (U i) e he)
          (Graphon.pullback (V i) f hf) :=
        Graphon.cutNormDiff_pullback_measurableEquiv _ _ f.symm (hf.symm f)
    _ ≤ Graphon.cutNormDiff (Graphon.pullback (U i) e he) (C i) +
          Graphon.cutNormDiff (C i) (Graphon.pullback (V i) f hf) :=
        Graphon.cutNormDiff_triangle _ _ _
    _ ≤ 2 * ε := by rw [Graphon.cutNormDiff_symm (C i)]; linarith [hU i hi, hV i hi]

/-- A diagonal subsequence stays in a common fiber at each successive level. -/
theorem exists_subsequence_common_fibers {K : ℕ → Type*} [∀ k, Finite (K k)]
    (c : ∀ k, ℕ → K k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, c k (φ (k + 1)) = c k (φ k) := by
  classical
  have hrefine (A : Set ℕ) (hA : A.Infinite) (k : ℕ) :
      ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ ∀ m ∈ B, ∀ n ∈ B, c k m = c k n := by
    let g : A → K k := fun n => c k n
    have : Infinite A := Set.infinite_coe_iff.mpr hA
    obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber g
    refine ⟨Subtype.val '' (g ⁻¹' {v}), ?_, ?_, ?_⟩
    · rintro _ ⟨n, _, rfl⟩
      exact n.property
    · exact (Set.infinite_coe_iff.mp hv).image Subtype.val_injective.injOn
    · rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
      exact (Set.mem_singleton_iff.mp hm).trans (Set.mem_singleton_iff.mp hn).symm
  choose B hB using hrefine
  let J : ℕ → {A : Set ℕ // A.Infinite} :=
    Nat.rec ⟨Set.univ, Set.infinite_univ⟩ fun k A => ⟨B A.1 A.2 k, (hB A.1 A.2 k).2.1⟩
  have hnest (k : ℕ) : (J (k + 1)).1 ⊆ (J k).1 := (hB (J k).1 (J k).2 k).1
  have hpick (k bound : ℕ) : ∃ n ∈ (J (k + 1)).1, bound < n :=
    (J (k + 1)).2.exists_gt bound
  choose next hnext_mem hnext_gt using hpick
  let φ : ℕ → ℕ := Nat.rec (next 0 0) fun k n => next (k + 1) n
  refine ⟨φ, strictMono_nat_of_lt_succ (fun k => hnext_gt (k + 1) (φ k)), fun k => ?_⟩
  have hmem (k : ℕ) : φ k ∈ (J (k + 1)).1 := by
    cases k with
    | zero => exact hnext_mem 0 0
    | succ k => exact hnext_mem (k + 1) (φ k)
  exact (hB (J k).1 (J k).2 k).2.2 _ (hnest (k + 1) (hmem (k + 1))) _ (hmem k)

/-- Consecutive common maps telescope to one common frame at every time. -/
theorem exists_common_realignment (W : ℕ → ι → Graphon Ω μ)
    (p : ℕ → ι → Prop) (δ : ℕ → ℝ)
    (hW : ∀ k, ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
      ∀ i, p k i → Graphon.cutNormDiff (Graphon.pullback (W (k + 1) i) e he) (W k i) ≤ δ k) :
    ∃ (f : ℕ → Ω ≃ᵐ Ω) (hf : ∀ k, MeasurePreserving (f k) μ μ),
      ∀ k i, p k i → Graphon.cutNormDiff
        (Graphon.pullback (W (k + 1) i) (f (k + 1)) (hf (k + 1)))
        (Graphon.pullback (W k i) (f k) (hf k)) ≤ δ k := by
  choose e he hbound using hW
  let f : ℕ → Ω ≃ᵐ Ω := Nat.rec (MeasurableEquiv.refl Ω) fun k prev => prev.trans (e k)
  have hf : ∀ k, MeasurePreserving (f k) μ μ := by
    intro k
    induction k with
    | zero => exact MeasurePreserving.id μ
    | succ k ih => exact (he k).comp ih
  refine ⟨f, hf, fun k i hi => ?_⟩
  show Graphon.cutNormDiff
    (Graphon.pullback (W (k + 1) i) (↑(e k) ∘ ↑(f k)) ((he k).comp (hf k)))
    (Graphon.pullback (W k i) (f k) (hf k)) ≤ δ k
  rw [← Graphon.pullback_pullback (W (k + 1) i) (e k) (he k) (f k) (hf k)]
  rw [Graphon.cutNormDiff_pullback_measurableEquiv _ _ (f k) (hf k)]
  exact hbound k i hi

/-- Finite covers at each level give a rapidly aligned common subsequence.
The covered coordinates may grow with the level. -/
theorem exists_rapid_subsequence {K : ℕ → Type*} [∀ k, Finite (K k)]
    (W : ℕ → ι → Graphon Ω μ) (C : ∀ k, K k → ι → Graphon Ω μ)
    (p : ℕ → ι → Prop) (ε : ℕ → ℝ)
    (happrox : ∀ k n, ∃ c : K k, ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
      ∀ i, p k i → Graphon.cutNormDiff (Graphon.pullback (W n i) e he) (C k c i) ≤ ε k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
        ∀ i, p k i → Graphon.cutNormDiff
          (Graphon.pullback (W (φ (k + 1)) i) e he) (W (φ k) i) ≤ 2 * ε k := by
  choose c e he hbound using happrox
  obtain ⟨φ, hφ, hc⟩ := exists_subsequence_common_fibers c
  refine ⟨φ, hφ, fun k => ?_⟩
  apply common_alignment_of_center (W (φ (k + 1))) (W (φ k)) (C k (c k (φ k)))
    (p k) (ε k) (e k (φ (k + 1))) (e k (φ k)) (he k (φ (k + 1))) (he k (φ k))
  · intro i hi
    rw [← hc k]
    exact hbound k (φ (k + 1)) i hi
  · exact hbound k (φ k)

/-- Fixed-label completeness preserves the frame already shared by the coordinates.
Each coordinate only needs summable bounds after a finite initial segment. -/
theorem exists_common_limit_of_summable [StandardBorelSpace Ω]
    (W : ℕ → ι → Graphon Ω μ) (p : ℕ → ι → Prop) (δ : ℕ → ℝ)
    (hδ : ∀ k, 0 ≤ δ k) (hsum : Summable δ)
    (hcover : ∀ i, ∃ M, ∀ k ≥ M, p k i)
    (hW : ∀ k, ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
      ∀ i, p k i → Graphon.cutNormDiff (Graphon.pullback (W (k + 1) i) e he) (W k i) ≤ δ k) :
    ∃ (L : ι → Graphon Ω μ) (f : ℕ → Ω ≃ᵐ Ω)
      (hf : ∀ k, MeasurePreserving (f k) μ μ),
      ∀ i ε, 0 < ε → ∃ N, ∀ n ≥ N,
        Graphon.cutNormDiff (Graphon.pullback (W n i) (f n) (hf n)) (L i) < ε := by
  obtain ⟨f, hf, hbound⟩ := exists_common_realignment W p δ hW
  have hlimit (i : ι) : ∃ L : Graphon Ω μ, ∀ ε > 0, ∃ N, ∀ n ≥ N,
      Graphon.cutNormDiff (Graphon.pullback (W n i) (f n) (hf n)) L < ε := by
    obtain ⟨M, hM⟩ := hcover i
    have hshift : Summable (fun k => δ (M + k)) :=
      hsum.comp_injective (fun _ _ h => by omega)
    obtain ⟨L, hL⟩ := Graphon.exists_cutNormDiff_limit_of_summable
      (fun n => Graphon.pullback (W (M + n) i) (f (M + n)) (hf (M + n)))
      (fun n => δ (M + n)) (fun n => hδ (M + n)) hshift
      (fun k => by simpa [Nat.add_assoc] using hbound (M + k) i (hM _ (by omega)))
    refine ⟨L, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hL ε hε
    refine ⟨M + N, fun n hn => ?_⟩
    have h := hN (n - M) (by omega)
    simpa [Nat.add_sub_of_le (show M ≤ n by omega)] using h
  choose L hL using hlimit
  exact ⟨L, f, hf, hL⟩

/-- Growing finite covers with geometrically decreasing errors give common-frame
coordinatewise compactness. Both the subsequence and every map are shared. -/
theorem compact_of_finite_covers [StandardBorelSpace Ω]
    {K : ℕ → Type*} [∀ k, Finite (K k)]
    (W : ℕ → ι → Graphon Ω μ) (C : ∀ k, K k → ι → Graphon Ω μ)
    (p : ℕ → ι → Prop) (hcover : ∀ i, ∃ M, ∀ k ≥ M, p k i)
    (happrox : ∀ k n, ∃ c : K k, ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
      ∀ i, p k i → Graphon.cutNormDiff
        (Graphon.pullback (W n i) e he) (C k c i) ≤ ((1 : ℝ) / 2) ^ k) :
    ∃ (L : ι → Graphon Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ),
        ∀ i ε, 0 < ε → ∃ N, ∀ n ≥ N,
          Graphon.cutNormDiff (Graphon.pullback (W (φ n) i) (e n) (he n)) (L i) < ε := by
  obtain ⟨φ, hφ, hchain⟩ := exists_rapid_subsequence W C p (fun k => ((1 : ℝ) / 2) ^ k) happrox
  have hsum : Summable (fun k : ℕ => 2 * ((1 : ℝ) / 2) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left 2
  obtain ⟨L, e, he, hL⟩ := exists_common_limit_of_summable
    (fun n => W (φ n)) p (fun k => 2 * ((1 : ℝ) / 2) ^ k)
    (fun k => by positivity) hsum hcover hchain
  exact ⟨L, φ, hφ, e, he, hL⟩

/-- Countable common-frame compactness follows from finite-prefix nets. -/
theorem compact_countable_of_finite_nets [StandardBorelSpace Ω]
    (hnet : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ S : Finset (Fin m → Graphon Ω μ), ∀ V : Fin m → Graphon Ω μ,
        ∃ C ∈ S, ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
          ∀ i, Graphon.cutNormDiff (Graphon.pullback (V i) e he) (C i) ≤ ε)
    (W : ℕ → ℕ → Graphon Ω μ) :
    ∃ (L : ℕ → Graphon Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ),
        ∀ i ε, 0 < ε → ∃ N, ∀ n ≥ N,
          Graphon.cutNormDiff (Graphon.pullback (W (φ n) i) (e n) (he n)) (L i) < ε := by
  classical
  choose S hS using fun k : ℕ => hnet (k + 1) (((1 : ℝ) / 2) ^ k) (by positivity)
  let K (k : ℕ) := {V // V ∈ S k}
  let C (k : ℕ) (V : K k) (i : ℕ) : Graphon Ω μ :=
    if h : i < k + 1 then V.1 ⟨i, h⟩ else Graphon.zero
  have happrox (k n : ℕ) : ∃ c : K k, ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
      ∀ i, i ≤ k → Graphon.cutNormDiff
        (Graphon.pullback (W n i) e he) (C k c i) ≤ ((1 : ℝ) / 2) ^ k := by
    obtain ⟨V, hV, e, he, hbound⟩ := hS k (fun i => W n i.1)
    refine ⟨⟨V, hV⟩, e, he, fun i hi => ?_⟩
    simpa only [C, dite_eq_left (show i < k + 1 by omega)] using hbound ⟨i, by omega⟩
  exact compact_of_finite_covers W C (fun k i => i ≤ k) (fun i => ⟨i, fun _ h => h⟩) happrox

/-- Finite-family compactness uses a common map and uniform convergence across
all coordinates of the finite family. -/
theorem compact_of_finite_nets [StandardBorelSpace Ω] [Fintype ι]
    (hnet : ∀ ε : ℝ, 0 < ε → ∃ S : Finset (ι → Graphon Ω μ),
      ∀ V : ι → Graphon Ω μ, ∃ C ∈ S,
        ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
          ∀ i, Graphon.cutNormDiff (Graphon.pullback (V i) e he) (C i) ≤ ε)
    (W : ℕ → ι → Graphon Ω μ) :
    ∃ (L : ι → Graphon Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ),
        ∀ ε, 0 < ε → ∃ N, ∀ n ≥ N, ∀ i,
          Graphon.cutNormDiff (Graphon.pullback (W (φ n) i) (e n) (he n)) (L i) < ε := by
  classical
  choose S hS using fun k : ℕ => hnet (((1 : ℝ) / 2) ^ k) (by positivity)
  let K (k : ℕ) := {V // V ∈ S k}
  have happrox (k n : ℕ) : ∃ c : K k, ∃ (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ),
      ∀ i, True → Graphon.cutNormDiff
        (Graphon.pullback (W n i) e he) (c.1 i) ≤ ((1 : ℝ) / 2) ^ k := by
    obtain ⟨V, hV, e, he, hbound⟩ := hS k (W n)
    exact ⟨⟨V, hV⟩, e, he, fun i _ => hbound i⟩
  obtain ⟨L, φ, hφ, e, he, hL⟩ := compact_of_finite_covers (K := K) W (fun k (V : K k) => V.1)
    (fun _ _ => True) (fun _ => ⟨0, fun _ _ => trivial⟩) happrox
  refine ⟨L, φ, hφ, e, he, fun ε hε => ?_⟩
  choose N hN using fun i => hL i ε hε
  refine ⟨Finset.univ.sup N, fun n hn i => ?_⟩
  exact hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)

/-- Every sequence of finite graphon families has a subsequence converging
uniformly across the family after one common relabeling at each time. -/
theorem compact [StandardBorelSpace Ω] [NullSingletonClass μ] [Fintype ι]
    (W : ℕ → ι → Graphon Ω μ) :
    ∃ (L : ι → Graphon Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ),
        ∀ ε, 0 < ε → ∃ N, ∀ n ≥ N, ∀ i,
          Graphon.cutNormDiff (Graphon.pullback (W (φ n) i) (e n) (he n)) (L i) < ε :=
  compact_of_finite_nets (fun ε hε => exists_finite_net ε hε) W

/-- Every sequence of countable graphon families has a subsequence converging
coordinatewise in one common frame. The subsequence and relabelings are chosen
before the coordinate, so the same choices work for every coordinate. -/
theorem compact_countable [StandardBorelSpace Ω] [NullSingletonClass μ]
    (W : ℕ → ℕ → Graphon Ω μ) :
    ∃ (L : ℕ → Graphon Ω μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ),
        ∀ i ε, 0 < ε → ∃ N, ∀ n ≥ N,
          Graphon.cutNormDiff (Graphon.pullback (W (φ n) i) (e n) (he n)) (L i) < ε :=
  compact_countable_of_finite_nets (fun _ ε hε => exists_finite_net ε hε) W

end Erdos1017.GraphonFamily
