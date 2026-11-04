module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomContactTwoRows

/-!
# Vertices on two surviving lines

Finite tight covers of the two surviving lines cover all tight rows, and four
rows cannot define a positive vertex, so at a vertex with only the `E₂` row and
the two surviving `R` lines both lines carry adjacent double contacts.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- Finite covers of the two surviving lines give a cover of all
actual tight rows. A total of four rows cannot define a positive vertex. -/
theorem not_vertex_of_two_line_covers (x : Coefficients) (hpos : ∀ i, 0 < x i)
    (s₀ s₁ : Finset ℕ) (hcard : s₀.card + s₁.card + 1 ≤ 4)
    (h₀ : ∀ k, countTest k 0 x = 1 → k ∈ s₀)
    (h₁ : ∀ k, countTest k 1 x = 1 → k ∈ s₁)
    (hsupport : ∀ k l, countTest k l x = 1 → (k = 0 ∧ l = 2) ∨ l = 0 ∨ l = 1) :
    x ∉ feasible.extremePoints ℝ := by
  let s := (s₀.image (fun k => (k, 0))) ∪ (s₁.image (fun k => (k, 1))) ∪ {(0, 2)}
  apply not_vertex_of_tight_cover x hpos s
  · have hA := Finset.card_union_le
      (s₀.image (fun k => (k, 0))) (s₁.image (fun k => (k, 1)))
    have hB := Finset.card_union_le
      ((s₀.image (fun k => (k, 0))) ∪ (s₁.image (fun k => (k, 1)))) {(0, 2)}
    have hC := Finset.card_image_le (s := s₀) (f := fun k => (k, 0))
    have hD := Finset.card_image_le (s := s₁) (f := fun k => (k, 1))
    have hsingle : ({(0, 2)} : Finset (ℕ × ℕ)).card = 1 := by simp
    dsimp only [s]
    omega
  · intro k l ht
    simp only [s, Finset.mem_union, Finset.mem_singleton]
    rcases hsupport k l ht with ⟨hk, hl⟩ | hl | hl
    · exact Or.inr (Prod.ext hk hl)
    · subst l
      exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨k, h₀ k ht, rfl⟩))
    · subst l
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨k, h₁ k ht, rfl⟩))

/-- At a genuine vertex with only E2 and the two surviving R lines,
both lines have actual adjacent double contacts. -/
theorem two_double_lines_of_vertex (x : Coefficients)
    (hvertex : x ∈ feasible.extremePoints ℝ) (hpos : ∀ i, 0 < x i)
    (hsupport : ∀ k l, countTest k l x = 1 → (k = 0 ∧ l = 2) ∨ l = 0 ∨ l = 1) :
    (∃ j, countTest j 0 x = 1 ∧ countTest (j + 1) 0 x = 1) ∧
      ∃ k, countTest k 1 x = 1 ∧ countTest (k + 1) 1 x = 1 := by
  have hx := hvertex.1
  constructor
  · by_contra h
    push Not at h
    have hno : ∀ j, ¬(countTest j 0 x = 1 ∧ countTest (j + 1) 0 x = 1) := by
      intro j hj
      exact h j hj.1 hj.2
    obtain ⟨s₀, hc₀, hs₀⟩ := exists_single_line_tight_cover x hx (hpos 2) 0 hno
    obtain ⟨s₁, hc₁, hs₁⟩ := exists_line_tight_cover x hx (hpos 2) 1
    exact not_vertex_of_two_line_covers x hpos s₀ s₁ (by omega) hs₀ hs₁ hsupport hvertex
  · by_contra h
    push Not at h
    have hno : ∀ k, ¬(countTest k 1 x = 1 ∧ countTest (k + 1) 1 x = 1) := by
      intro k hk
      exact h k hk.1 hk.2
    obtain ⟨s₀, hc₀, hs₀⟩ := exists_line_tight_cover x hx (hpos 2) 0
    obtain ⟨s₁, hc₁, hs₁⟩ := exists_single_line_tight_cover x hx (hpos 2) 1 hno
    exact not_vertex_of_two_line_covers x hpos s₀ s₁ (by omega) hs₀ hs₁ hsupport hvertex

end Erdos1017.TwoAtomCountGate
