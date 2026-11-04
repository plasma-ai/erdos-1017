module

public import Erdos1017.Multipartite.Physical.PhysicalGraphTail
public import Erdos1017.Multipartite.MultipartiteActualDust
public import Erdos1017.Multipartite.Dust.DustCommonRealization

/-!
# Vertex measures on the countable carrier

One fixed physical carrier holds the anchor, countably many heads and dust; the
head, prefix and tail measures are finite with explicit masses, and the omitted
tail mass is exactly the omitted atomic mass, tending to zero.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableMeasure

open MeasureTheory
open scoped BigOperators ENNReal

/-- One fixed physical carrier for the anchor, countably many heads and dust. -/
abbrev Label := Option ℕ ⊕ Unit

local instance : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A physical component at one fixed label. -/
def component (ν : Measure Ω) (i : Label) : Measure (Label × Ω) :=
  ν.map (fun x => (i, x))

def headMeasure (ν : Measure Ω) (p : ℕ → ℝ) (i : ℕ) : Measure (Label × Ω) :=
  ENNReal.ofReal (p i) • component ν (.inl (some i))

def vertexMeasure (ν : Measure Ω) (p : ℕ → ℝ) (s : ℝ) : Measure (Label × Ω) :=
  component ν (.inl none) + ENNReal.ofReal s • component ν (.inr ()) + Measure.sum (headMeasure ν p)

def prefixMeasure (ν : Measure Ω) (p : ℕ → ℝ) (s : ℝ) (n : ℕ) : Measure (Label × Ω) :=
  component ν (.inl none) + ENNReal.ofReal s • component ν (.inr ()) +
    ∑ i ∈ Finset.range n, headMeasure ν p i

def tailMeasure (ν : Measure Ω) (p : ℕ → ℝ) (n : ℕ) : Measure (Label × Ω) :=
  Measure.sum (fun i => if n ≤ i then headMeasure ν p i else 0)

theorem component_univ (ν : Measure Ω) [IsProbabilityMeasure ν] (i : Label) :
    component ν i Set.univ = 1 := by
  simp [component]

theorem headMeasure_univ (ν : Measure Ω) [IsProbabilityMeasure ν] (p : ℕ → ℝ) (i : ℕ) :
    headMeasure ν p i Set.univ = ENNReal.ofReal (p i) := by
  simp [headMeasure, component_univ]

/-- The full vertex measure is exactly its finite prefix plus its omitted heads. -/
theorem vertexMeasure_eq_prefix_add_tail (ν : Measure Ω) (p : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    vertexMeasure ν p s = prefixMeasure ν p s n + tailMeasure ν p n := by
  have hsplit : Measure.sum (headMeasure ν p) =
      (∑ i ∈ Finset.range n, headMeasure ν p i) + tailMeasure ν p n := by
    ext E hE
    simp only [Measure.sum_apply _ hE, Measure.add_apply, Measure.finsetSum_apply, tailMeasure]
    have hsmall : (∑' i, if i < n then headMeasure ν p i E else 0) =
        ∑ i ∈ Finset.range n, headMeasure ν p i E := by
      rw [tsum_eq_sum (s := Finset.range n) (fun i hi => by
        simp only [Finset.mem_range] at hi
        simp [hi])]
      exact Finset.sum_congr rfl (fun i hi => by simp [Finset.mem_range.mp hi])
    rw [← hsmall, ← ENNReal.tsum_add]
    apply tsum_congr
    intro i
    by_cases hi : i < n
    · simp [hi, Nat.not_le_of_lt hi]
    · simp [hi, Nat.le_of_not_gt hi]

  unfold vertexMeasure prefixMeasure
  rw [hsplit]
  ac_rfl

/-- Summable head masses give a finite measure on the fixed countable carrier. -/
theorem vertexMeasure_finite (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (hsum : Summable p) (s : ℝ) : IsFiniteMeasure (vertexMeasure ν p s) := by
  constructor
  simp only [vertexMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    component_univ, mul_one, Measure.sum_apply _ MeasurableSet.univ, headMeasure_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.ofReal_lt_top⟩,
    hsum.tsum_ofReal_lt_top⟩

theorem prefixMeasure_finite (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (hsum : Summable p) (s : ℝ) (n : ℕ) :
    IsFiniteMeasure (prefixMeasure ν p s n) := by
  have := vertexMeasure_finite ν p hsum s
  apply isFiniteMeasure_of_le (vertexMeasure ν p s)
  rw [vertexMeasure_eq_prefix_add_tail ν p s n]
  intro E
  exact le_self_add

theorem tailMeasure_finite (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (hsum : Summable p) (n : ℕ) : IsFiniteMeasure (tailMeasure ν p n) := by
  have := vertexMeasure_finite ν p hsum 0
  apply isFiniteMeasure_of_le (vertexMeasure ν p 0)
  rw [vertexMeasure_eq_prefix_add_tail ν p 0 n]
  intro E
  exact le_add_self

theorem vertexMeasure_mass (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) (s : ℝ) (hs : 0 ≤ s) :
    (vertexMeasure ν p s).real Set.univ = 1 + s + ∑' i, p i := by
  simp only [measureReal_def, vertexMeasure, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, component_univ, mul_one, Measure.sum_apply _ MeasurableSet.univ,
    headMeasure_univ, ← ENNReal.ofReal_tsum_of_nonneg hp hsum]
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (by norm_num) ENNReal.ofReal_ne_top]
  simp [hs, tsum_nonneg hp]

theorem prefixMeasure_mass (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    (prefixMeasure ν p s n).real Set.univ = 1 + s + ∑ i ∈ Finset.range n, p i := by
  simp only [measureReal_def, prefixMeasure, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, component_univ, mul_one, Measure.finsetSum_apply, headMeasure_univ]
  rw [ENNReal.toReal_add (by finiteness) (by simp),
    ENNReal.toReal_add (by norm_num) ENNReal.ofReal_ne_top,
    ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
  simp [hs, hp]

/-- The omitted physical mass is exactly the omitted atomic mass. -/
theorem tailMeasure_mass (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) (n : ℕ) :
    (tailMeasure ν p n).real Set.univ = (∑' i, p i) - ∑ i ∈ Finset.range n, p i := by
  have := prefixMeasure_finite ν p hsum 0 n
  have := tailMeasure_finite ν p hsum n
  have h := congrArg (fun μ : Measure (Label × Ω) => μ.real Set.univ)
    (vertexMeasure_eq_prefix_add_tail ν p 0 n)
  rw [measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _),
    vertexMeasure_mass ν p hp hsum 0 le_rfl, prefixMeasure_mass ν p hp 0 le_rfl n] at h
  linarith

theorem tailMeasure_mass_tendsto_zero (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) :
    Filter.Tendsto (fun n => (tailMeasure ν p n).real Set.univ) Filter.atTop (nhds 0) := by
  simp_rw [tailMeasure_mass ν p hp hsum]
  simpa using (tendsto_const_nhds (x := ∑' i, p i)).sub hsum.hasSum.tendsto_sum_nat

end Erdos1017.MultipartiteCountableMeasure
