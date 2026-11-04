module

public import Erdos1017.Multipartite.PatternExtraction

/-!
# Repeat extension at a strictly positive vertex

Every strictly positive vertex admits the full one-sided repeat extension, with
the tight-count alternatives derived from extremality (`vertex_has_repeat`), and
the same penalty controls rooted and rootless columns.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.VertexRepeat

open VertexClassification Repeat PatternExtraction

/-- Repeating the first type costs at most the original cross penalty. -/
def HasRepeat (x : Coefficients) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ D ≤ x 3 ∧ ∀ (r b n : ℕ), b ≤ 1 →
    oneSidedCharge (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) D r b n ≤ 1

/-- Exchange the two distinguished types and their incident dust penalties. -/
def swap (x : Coefficients) : Coefficients := ![x 1, x 0, x 2, x 3, x 5, x 4, x 6]

theorem test_swap (x : Coefficients) (state : State) (n : ℕ) :
    test (state, n) (swap x) = test (state.swap, n) x := by
  rcases state with ⟨a, b⟩
  cases a <;> cases b <;>
    simp [test, constant, slope, swap, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem swap_feasible (x : Coefficients) (hx : x ∈ feasible) : swap x ∈ feasible := by
  constructor
  · intro i
    fin_cases i <;> simpa [swap] using hx.1 _
  · rintro ⟨state, n⟩
    rw [test_swap]
    exact hx.2 _

theorem swap_positive (x : Coefficients) (hx : ∀ i, 0 < x i) :
    ∀ i, 0 < swap x i := by
  intro i
  fin_cases i <;> simpa [swap] using hx _

/-- The old Boolean constraints are exactly the original count tests. -/
theorem original_boolean_feasibility (x : Coefficients) (hx : x ∈ feasible) :
    ∀ (a b n : ℕ), a ≤ 1 → b ≤ 1 →
      oneSidedCharge (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) 0 a b n ≤ 1 := by
  intro a b n ha hb
  interval_cases a <;> interval_cases b
  · simpa [test, constant, slope, oneSidedCharge, pairs, mul_comm] using hx.2 ((false, false), n)
  · simpa [test, constant, slope, oneSidedCharge, pairs, mul_comm] using hx.2 ((false, true), n)
  · simpa [test, constant, slope, oneSidedCharge, pairs, mul_comm] using hx.2 ((true, false), n)
  · simpa [test, constant, slope, oneSidedCharge, pairs, mul_comm] using hx.2 ((true, true), n)

/-- Both classified patterns permit repetition of the type with larger count index. -/
theorem hasRepeat_of_ordered_patterns (x : Coefficients) (hx : x ∈ feasible)
    (hpos : ∀ i, 0 < x i) (j k l : ℕ) (hlk : l ≤ k)
    (h00 : test ((false, false), j) x = 1 ∧ test ((false, false), j + 1) x = 1)
    (h10 : test ((true, false), k) x = 1 ∧ test ((true, false), k + 1) x = 1)
    (h01 : test ((false, true), l) x = 1 ∧ test ((false, true), l + 1) x = 1)
    (h11 : (∃ m, test ((true, true), m) x = 1 ∧ test ((true, true), m + 1) x = 1) ∨
      (test ((true, true), 0) x = 1 ∧ slope (true, true) x < 0)) : HasRepeat x := by
  obtain ⟨hj, hk, hl, hp, hv, ht₁, ht₂, hc₁, hc₂⟩ :=
    three_double_tight_coefficients x j k l (hpos 6) (hpos 4) (hpos 5) h00 h10 h01
  rcases h11 with ⟨m, hm⟩ | ⟨hzero, hnegative⟩
  · have hm' := four_slope_indices x j k l m (hpos 6) h00 h10 h01 hm
    have hc := double_tight_cross x j k l m hj hk.le hl.le hm' hp ht₁ ht₂ hm
    have ht₁' := ht₁.trans (zeroStar_eq_star j k hj hk.le)
    have ht₂' := ht₂.trans (zeroStar_eq_star j l hj hl.le)
    have hde : j - k ≤ j - l := Nat.sub_le_sub_left hlk j
    simpa only [HasRepeat, ht₁', ht₂', hv, hc, hc₁, hc₂, hp, oneSidedCharge] using
      four_double_tight_repeat j (j - k) (j - l) hj hde
  · have hsum := negative_fourth_index x j k l (hpos 6) h00 h10 h01 hnegative
    have hc := zero_tight_cross x j k l ht₁ ht₂ hzero
    have hold := original_boolean_feasibility x hx
    rw [ht₁, ht₂, hv, hc, hc₁, hc₂, hp] at hold
    simpa only [HasRepeat, ht₁, ht₂, hv, hc, hc₁, hc₂, hp] using
      zero_pattern_repeat j k l hj hk hlk hsum hold

/-- Every strictly positive vertex admits the full one-sided repeat extension.
The tight-count alternatives are derived from extremality inside this proof. -/
theorem vertex_has_repeat (x : Coefficients) (hvertex : x ∈ feasible.extremePoints ℝ)
    (hpos : ∀ i, 0 < x i) : HasRepeat x ∨ HasRepeat (swap x) := by
  obtain ⟨⟨j, h00⟩, ⟨k, h10⟩, ⟨l, h01⟩, h11⟩ := vertex_patterns x hvertex hpos
  have h11' : (∃ m, test ((true, true), m) x = 1 ∧
      test ((true, true), m + 1) x = 1) ∨
      (test ((true, true), 0) x = 1 ∧ slope (true, true) x < 0) := by
    rcases h11 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2.1, h.1⟩
  by_cases hlk : l ≤ k
  · exact Or.inl (hasRepeat_of_ordered_patterns x hvertex.1 hpos j k l hlk h00 h10 h01 h11')
  · right
    apply hasRepeat_of_ordered_patterns (swap x) (swap_feasible x hvertex.1)
      (swap_positive x hpos) j l k (by omega)
    · simpa [test_swap] using h00
    · simpa [test_swap] using h01
    · simpa [test_swap] using h10
    · rcases h11' with h | ⟨hzero, hnegative⟩
      · left
        simpa [test_swap] using h
      · right
        refine ⟨by simpa [test_swap] using hzero, ?_⟩
        simpa [slope, swap, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hnegative

/-- The same penalty controls rooted and rootless columns simultaneously. -/
theorem hasRepeat_with_rootless (x : Coefficients) (hpos : ∀ i, 0 < x i)
    (h : HasRepeat x) :
    ∃ D : ℝ, 0 ≤ D ∧ D ≤ x 3 ∧ ∀ (r b n : ℕ), b ≤ 1 →
      oneSidedCharge (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) D r b n ≤ 1 ∧
      -(r : ℝ) * (b : ℝ) * x 3
        - (n : ℝ) * ((r : ℝ) * x 4 + (b : ℝ) * x 5)
        - x 6 * pairs n - D * pairs r ≤ 0 := by
  obtain ⟨D, hD, hc, hcounts⟩ := h
  refine ⟨D, hD, hc, ?_⟩
  intro r b n hb
  exact ⟨hcounts r b n hb,
    rootlessCharge_nonpos _ _ _ _ _ (hpos 3).le (hpos 4).le (hpos 5).le (hpos 6).le hD r b n⟩

end Erdos1017.VertexRepeat
