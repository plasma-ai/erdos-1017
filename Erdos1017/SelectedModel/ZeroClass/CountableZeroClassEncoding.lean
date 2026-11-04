module

public import Erdos1017.SelectedModel.ZeroClass.CountableClassEdits
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteDensityRealization

/-!
# Encoding countably many labeled classes

Countably many disjoint measurable classes, each with a finite measurable label,
have one measurable encoding on the same carrier whose positive index identifies
the class and whose part cells are the original class restricted to the local
label fibers, with their original-carrier masses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

/-- Countably many disjoint measurable classes, each with a finite
measurable label, have one measurable encoding on the same carrier. -/
theorem exists_measurable_countableClassLabels_encoding
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    (k : ι → ℕ) (L : ∀ i, Ω → Fin (k i))
    (hL : ∀ i, Measurable (L i)) :
    ∃ e : ι ↪ ℕ, ∃ t : Ω → ℕ × ℕ, Measurable t ∧
      (∀ i x, x ∈ s i → t x = (e i + 1, (L i x).val)) ∧
      (∀ x, (∀ i, x ∉ s i) → t x = (0, 0)) := by
  classical
  let e : ι ↪ ℕ := (nonempty_embedding_nat ι).some
  let U : Set Ω := ⋃ i, s i
  have hU : MeasurableSet U := MeasurableSet.iUnion hs
  let T : Option ι → Set Ω
    | none => Uᶜ
    | some i => s i
  let g : Option ι → Ω → ℕ × ℕ
    | none => fun _ => (0, 0)
    | some i => fun x => (e i + 1, (L i x).val)
  have hT (i : Option ι) : MeasurableSet (T i) := by
    cases i with
    | none => exact hU.compl
    | some i => exact hs i
  have hg (i : Option ι) : Measurable (g i) := by
    cases i with
    | none => exact measurable_const
    | some i =>
        change Measurable (fun x : Ω => (e i + 1, (L i x).val))
        fun_prop
  have hTd : Pairwise (fun i j => Disjoint (T i) (T j)) := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j =>
            apply disjoint_left.mpr
            intro x hx hj
            exact hx (mem_iUnion.mpr ⟨j, hj⟩)
    | some i =>
        cases j with
        | none =>
            apply disjoint_left.mpr
            intro x hi hx
            exact hx (mem_iUnion.mpr ⟨i, hi⟩)
        | some j =>
            have hij' : i ≠ j := by simpa using hij
            exact hdisj hij'
  have hagree : Pairwise (fun i j => EqOn (g i) (g j) (T i ∩ T j)) := by
    intro i j hij x hx
    exact ((disjoint_left.mp (hTd hij)) hx.1 hx.2).elim
  obtain ⟨t, ht, htag⟩ := exists_measurable_piecewise T hT g hg hagree
  refine ⟨e, t, ht, ?_, ?_⟩
  · intro i x hx
    exact htag (some i) hx
  · intro x hx
    have hnot : x ∈ T none := by
      intro hUmem
      obtain ⟨i, hi⟩ := mem_iUnion.mp hUmem
      exact hx i hi
    exact htag none hnot

/-- An encoded positive class index identifies exactly its selected
measurable class. -/
theorem countableClassLabels_encoding_index_eq_iff
    {ι Ω : Type*} [MeasurableSpace Ω]
    (s : ι → Set Ω) {k : ι → ℕ}
    (L : ∀ i, Ω → Fin (k i)) (e : ι ↪ ℕ) (t : Ω → ℕ × ℕ)
    (htag : ∀ i x, x ∈ s i → t x = (e i + 1, (L i x).val))
    (houtside : ∀ x, (∀ i, x ∉ s i) → t x = (0, 0))
    (i : ι) (x : Ω) :
    (t x).1 = e i + 1 ↔ x ∈ s i := by
  constructor
  · intro heq
    by_contra hni
    by_cases hex : ∃ j, x ∈ s j
    · obtain ⟨j, hj⟩ := hex
      have hjtag := htag j x hj
      rw [hjtag] at heq
      have hji : j = i := e.injective (by omega)
      exact hni (hji ▸ hj)
    · have hnot : ∀ j, x ∉ s j := by
        intro j hj
        exact hex ⟨j, hj⟩
      rw [houtside x hnot] at heq
      omega
  · intro hi
    rw [htag i x hi]

/-- One encoded part cell is exactly the old class restricted to the
corresponding local finite-label fiber. -/
theorem countableClassLabels_encoding_cell_eq
    {ι Ω : Type*} [MeasurableSpace Ω]
    {s : ι → Set Ω} {k : ι → ℕ}
    (L : ∀ i, Ω → Fin (k i)) (e : ι ↪ ℕ) (t : Ω → ℕ × ℕ)
    (htag : ∀ i x, x ∈ s i → t x = (e i + 1, (L i x).val))
    (i : ι) (j : Fin (k i)) :
    {x : Ω | x ∈ s i ∧ t x = (e i + 1, j.val)} =
      s i ∩ (L i) ⁻¹' {j} := by
  ext x
  constructor
  · rintro ⟨hx, htx⟩
    have hval : (L i x).val = j.val := by
      rw [htag i x hx] at htx
      exact congrArg Prod.snd htx
    exact ⟨hx, Fin.ext hval⟩
  · rintro ⟨hx, hj⟩
    exact ⟨hx, by rw [htag i x hx, hj]⟩

/-- The encoded part cell has exactly its actual old-carrier mass;
no independence or atomlessness premise is used. -/
theorem countableClassLabels_encoding_cell_mass
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : ι → Set Ω} {k : ι → ℕ}
    (L : ∀ i, Ω → Fin (k i)) (e : ι ↪ ℕ) (t : Ω → ℕ × ℕ)
    (htag : ∀ i x, x ∈ s i → t x = (e i + 1, (L i x).val))
    (i : ι) (j : Fin (k i)) :
    μ.real {x : Ω | x ∈ s i ∧ t x = (e i + 1, j.val)} =
      μ.real (s i ∩ (L i) ⁻¹' {j}) := by
  rw [countableClassLabels_encoding_cell_eq L e t htag i j]

end Erdos1017.CappedModel
