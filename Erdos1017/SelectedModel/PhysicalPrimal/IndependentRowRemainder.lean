module

public import Erdos1017.SelectedModel.Structure.WholeRowAtoms

/-!
# Independent whole fibers and their measurable remainder

From a supplied row map, the positive whole row fibers with zero internal
adjacency form a countable independent family, and the measurable remainder has
no equal-row zero pair almost everywhere (`exists_independent_row_remainder`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Retain exactly those supplied positive whole row fibers whose actual
internal adjacency is zero almost everywhere. -/
def independentRowValues (μ : Measure Ω) (G : Ω → Ω → ℝ)
    (R : Ω → Lp ℝ 2 μ) (A : Set (Lp ℝ 2 μ)) : Set (Lp ℝ 2 μ) :=
  {r | r ∈ A ∧ ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = r}),
    G p.1 p.2 = 0}

/-- Remove the retained whole independent fibers, without changing the
supplied row map or assigning independent squares to the remainder. -/
def independentRowRemainder (μ : Measure Ω) (G : Ω → Ω → ℝ)
    (R : Ω → Lp ℝ 2 μ) (A : Set (Lp ℝ 2 μ)) : Set Ω :=
  (⋃ r ∈ independentRowValues μ G R A, {x | R x = r})ᶜ

theorem independentRowValues_subset (G : Ω → Ω → ℝ)
    (R : Ω → Lp ℝ 2 μ) (A : Set (Lp ℝ 2 μ)) :
    independentRowValues μ G R A ⊆ A := fun _ hr => hr.1

theorem independentRowValues_countable (G : Ω → Ω → ℝ)
    (R : Ω → Lp ℝ 2 μ) (A : Set (Lp ℝ 2 μ)) (hA : A.Countable) :
    (independentRowValues μ G R A).Countable :=
  hA.mono (independentRowValues_subset G R A)

theorem measurableSet_independentRowRemainder (G : Ω → Ω → ℝ)
    (R : Ω → Lp ℝ 2 μ) (A : Set (Lp ℝ 2 μ)) (hA : A.Countable)
    (hmeas : ∀ r ∈ A, MeasurableSet {x | R x = r}) :
    MeasurableSet (independentRowRemainder μ G R A) :=
  (MeasurableSet.biUnion (independentRowValues_countable G R A hA)
    (fun r hr => hmeas r hr.1)).compl

variable [IsProbabilityMeasure μ]

/-- On one countable common event, an equal-row zero pair belongs to an
actual independent whole fiber. Internal constants are lifted from each
restricted square, never evaluated on an arbitrary physical diagonal. -/
theorem ae_zero_equal_row_mem_independentRowValues
    (K G Y : Ω → Ω → ℝ) (B m : ℝ) (R : Ω → Lp ℝ 2 μ)
    (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x)
    (A : Set (Lp ℝ 2 μ)) (hA : A.Countable)
    (hmeas : ∀ r ∈ A, MeasurableSet {x | R x = r})
    (hexhaust : ∀ᵐ p ∂μ.prod μ, (K p.1 =ᵐ[μ] K p.2) ↔
      ∃ r ∈ A, R p.1 = r ∧ R p.2 = r)
    (hdata : ∀ r ∈ A, WholeRowFiberData μ K G Y B m R r) :
    ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → R p.1 = R p.2 →
      ∃ r ∈ independentRowValues μ G R A, R p.1 = r ∧ R p.2 = r := by
  have hcommon : ∀ᵐ p ∂μ.prod μ, ∀ r ∈ A,
      R p.1 = r → R p.2 = r → K p.1 p.2 = 0 → r ∈ independentRowValues μ G R A := by
    apply (ae_ball_iff hA).mpr
    intro r hr
    obtain ⟨q, _, _, hconstant, hindependent, _⟩ := (hdata r hr).internal
    have hq : ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = r}),
        K p.1 p.2 = q := hconstant.mono (fun _ hp => hp.1)
    rw [Measure.prod_restrict] at hq
    have hglobal := (ae_restrict_iff' ((hmeas r hr).prod (hmeas r hr))).mp hq
    filter_upwards [hglobal] with p hp hx hy hz
    have hqzero : q = 0 := (hp ⟨hx, hy⟩).symm.trans hz
    exact ⟨hr, hindependent.mpr hqzero⟩
  filter_upwards [hcommon, hexhaust, ae_rowMap_eq_iff K R hrow] with p hp he hm hzero hrows
  obtain ⟨r, hr, hx, hy⟩ := he.mp (hm.mp hrows)
  exact ⟨r, hp r hr hx hy hzero, hx, hy⟩

/-- The measurable remainder has no equal-row zero pair almost everywhere,
with exactly the global implication needed by the measurable-cut theorem. -/
theorem ae_zero_row_ne_on_independentRowRemainder
    (K G Y : Ω → Ω → ℝ) (B m : ℝ) (R : Ω → Lp ℝ 2 μ)
    (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x)
    (A : Set (Lp ℝ 2 μ)) (hA : A.Countable)
    (hmeas : ∀ r ∈ A, MeasurableSet {x | R x = r})
    (hexhaust : ∀ᵐ p ∂μ.prod μ, (K p.1 =ᵐ[μ] K p.2) ↔
      ∃ r ∈ A, R p.1 = r ∧ R p.2 = r)
    (hdata : ∀ r ∈ A, WholeRowFiberData μ K G Y B m R r) :
    ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 →
      p.1 ∈ independentRowRemainder μ G R A → p.2 ∈ independentRowRemainder μ G R A →
        R p.1 ≠ R p.2 := by
  filter_upwards [ae_zero_equal_row_mem_independentRowValues K G Y B m R hrow A hA
    hmeas hexhaust hdata] with p hp hzero hx _hy heq
  obtain ⟨r, hr, hxr, _⟩ := hp hzero heq
  exact hx (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, hxr⟩⟩)

/-- Construct the independent whole-fiber family and its measurable
remainder for the same supplied actual row map. The homogeneity payload
and both global and restricted-square distinct-row conclusions are retained. -/
theorem exists_independent_row_remainder
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K G Y : Ω → Ω → ℝ) (B m : ℝ) (R : Ω → Lp ℝ 2 μ) (hR : StronglyMeasurable R)
    (hrow : ∀ᵐ x ∂μ, (R x : Ω → ℝ) =ᵐ[μ] K x)
    (A : Set (Lp ℝ 2 μ)) (hA : A.Countable)
    (hpos : ∀ r ∈ A, 0 < μ {x | R x = r})
    (hexhaust : ∀ᵐ p ∂μ.prod μ, (K p.1 =ᵐ[μ] K p.2) ↔
      ∃ r ∈ A, R p.1 = r ∧ R p.2 = r)
    (hdata : ∀ r ∈ A, WholeRowFiberData μ K G Y B m R r) :
    ∃ (I : Set (Lp ℝ 2 μ)) (D : Set Ω), I ⊆ A ∧ I.Countable ∧
      (∀ r ∈ I, MeasurableSet {x | R x = r} ∧ 0 < μ {x | R x = r} ∧
        (∀ᵐ p ∂(μ.restrict {x | R x = r}).prod (μ.restrict {x | R x = r}),
          G p.1 p.2 = 0) ∧ WholeRowFiberData μ K G Y B m R r) ∧
      I.Pairwise (fun r t => Disjoint {x | R x = r} {x | R x = t}) ∧
      D = (⋃ r ∈ I, {x | R x = r})ᶜ ∧ MeasurableSet D ∧
      (∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → p.1 ∈ D → p.2 ∈ D → R p.1 ≠ R p.2) ∧
      (∀ᵐ p ∂(μ.restrict D).prod (μ.restrict D), K p.1 p.2 = 0 → R p.1 ≠ R p.2) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  have : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hmeas (r : Lp ℝ 2 μ) (_hr : r ∈ A) : MeasurableSet {x | R x = r} :=
    hR.measurable (measurableSet_singleton r)
  have hD := measurableSet_independentRowRemainder G R A hA hmeas
  have hne := ae_zero_row_ne_on_independentRowRemainder K G Y B m R hrow A hA
    hmeas hexhaust hdata
  refine ⟨independentRowValues μ G R A, independentRowRemainder μ G R A,
    independentRowValues_subset G R A, independentRowValues_countable G R A hA,
    ?_, ?_, rfl, hD, hne, ?_⟩
  · intro r hr
    exact ⟨hmeas r hr.1, hpos r hr.1, hr.2, hdata r hr.1⟩
  · intro r _ t _ hrt
    exact Set.disjoint_left.mpr (fun x hx hy => hrt (hx.symm.trans hy))
  · rw [Measure.prod_restrict]
    apply (ae_restrict_iff' (hD.prod hD)).mpr
    filter_upwards [hne] with p hp hmem hz
    exact hp hz hmem.1 hmem.2

end Erdos1017.KernelOperator
